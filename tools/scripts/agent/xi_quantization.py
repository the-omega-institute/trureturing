"""Bounded actual-xi quantization: Arb inputs, exact CPU bins, optional MPS candidates."""

import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import importlib.metadata
import json
import os
from pathlib import Path
import platform
import shlex
import subprocess
import sys
import time

from gpu5040 import state_store

M = 1_400_000
CLASSES = ("indefinite", "singular", "pd")
COORDINATES = ("x", "y", "beta")
PINS = ["uv", "run", "--python", "3.12", "--with", "torch==2.8.0",
        "--with", "numpy==2.0.2", "--with", "python-flint==0.8.0", "python"]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def validate_range(first, last, chunk):
    require(1 <= first <= last <= M and 1 <= chunk <= M, "range/chunk outside [1, 1400000]")
    # All float32 indices are exact; even the conservative b intermediate fits int64.
    require(M < 2**24 and 4*(M+1)**2 < 2**63, "unsupported arithmetic range")


def certified_bin(interval, m):
    a, b, d = interval
    require(d > 0 and a <= b and m >= 1, "invalid rational interval/resolution")
    lower, upper = (2*m*a+d)//(2*d), (2*m*b+d)//(2*d)
    return lower if lower == upper else None


def entrywise_class(m, kx, ky):
    b = m*m+m*ky-2*kx*kx
    if abs(kx) > m or abs(ky) > m or b < 0:
        return "indefinite"
    return "pd" if abs(kx) < m and ky < m and b > 0 else "singular"


def schur_class(m, kx, kb):
    require(abs(kx) <= m and abs(kb) <= m, "Schur coordinates outside [-1,1]")
    return "pd" if abs(kx) < m and abs(kb) < m else "singular"


def stream_row(m, kx, ky, kb, direct, schur):
    return f"{m},{kx},{ky},{kb},{direct},{schur}\n".encode("ascii")


def entrywise_witness(m, kx, ky):
    b = m*m+m*ky-2*kx*kx
    det = Fraction((m-ky)*b, m**3)
    outcome = entrywise_class(m, kx, ky)
    record = {"m": m, "kx": kx, "ky": ky, "b": b,
              "class": outcome, "determinant": str(det)}
    if b < 0 or outcome == "singular":
        vector = [m, -2*kx, m] if b <= 0 else [1, 0, -1]
        x, y = Fraction(kx, m), Fraction(ky, m)
        a, c, e = vector
        value = a*a+c*c+e*e+2*x*(a*c+c*e)+2*y*a*e
        require(value < 0 if b < 0 else value == 0, "invalid exact witness")
        normalized = [Fraction(v, m) for v in vector] if b <= 0 else list(map(Fraction, vector))
        record.update(vector=vector, quadratic_value=int(value),
                      normalized_vector=[int(v) if v.denominator == 1 else str(v) for v in normalized],
                      normalized_quadratic_value=str(value/m**2 if b <= 0 else value))
    return record


def schur_witness(m, kx, kb):
    x, beta = Fraction(kx, m), Fraction(kb, m)
    y = x*x+(1-x*x)*beta
    det = (1-x*x)**2*(1-beta*beta)
    require(y == Fraction(m*kx*kx+(m*m-kx*kx)*kb, m**3), "reconstruction grid identity")
    require((1-y)*(1+y-2*x*x) == det, "Schur determinant identity")
    record = {"m": m, "kx": kx, "kb": kb, "y_reconstructed": str(y),
              "determinant": str(det), "class": schur_class(m, kx, kb)}
    if det == 0:
        vector = [1, -x, 0] if abs(x) == 1 else ([1, 0, -1] if beta == 1 else [1, -2*x, 1])
        a, c, e = vector
        require(a*a+c*c+e*e+2*x*(a*c+c*e)+2*y*a*e == 0, "Schur null witness")
        record.update(null_vector=[str(v) for v in vector], quadratic_value="0")
    return record


def append_range(ranges, m):
    if ranges and ranges[-1][1]+1 == m:
        ranges[-1][1] = m
    else:
        ranges.append([m, m])


class Coverage:
    def __init__(self, first, last):
        self.first, self.last, self.next = first, last, first
        self.completed, self.unresolved = [], []
        self.classified = 0

    def record(self, m, certified):
        require(m == self.next and m <= self.last, "duplicate, skipped, or unordered resolution")
        append_range(self.completed if certified else self.unresolved, m)
        self.classified += int(certified)
        self.next += 1

    def summary(self):
        unresolved = [row[:] for row in self.unresolved]
        if self.next <= self.last:
            if unresolved and unresolved[-1][1]+1 == self.next:
                unresolved[-1][1] = self.last
            else:
                unresolved.append([self.next, self.last])
        return {"requested_interval": [self.first, self.last],
                "expected_count": self.last-self.first+1, "classified_count": self.classified,
                "attempted_count": self.next-self.first, "completed_intervals": self.completed,
                "unresolved_ranges": unresolved, "unresolved_count": self.last-self.first+1-self.classified}


def generate_inputs(precision, digits):
    from flint import arb, arb_series, ctx

    def enclose(ball, denominator):
        integer = (ball*denominator).floor().unique_fmpz()
        require(integer is not None, "scaled Arb floor is not uniquely certified")
        lower = int(integer)
        require(arb(lower)/denominator < ball < arb(lower+1)/denominator,
                "Arb does not strictly certify both rational endpoints")
        return (lower, lower+1, denominator)

    attempts = []
    while precision <= 2048:
        ctx.prec, ctx.cap = precision, 4
        t = arb_series([0, 1])
        s = 1+t
        xi = s*(-s*arb.pi().log()/2).exp()*(s/2).gamma()*(1+t*s.zeta(deflate=True))/2
        f = (xi/xi[0]).log()
        require(xi[0].contains(arb(1)/2) and f[1] > 0, "xi normalization/denominator uncertified")
        x = f[2]/f[1]
        y = (2*f[2]+3*f[3])/(2*f[1])
        gap = y-(2*x*x-1)
        beta = (y-x*x)/(1-x*x)
        balls = {"x": x, "y": y, "gap": gap, "beta": beta}
        try:
            intervals = {name: enclose(ball, 10**digits) for name, ball in balls.items()}
            coarse = {name: enclose(balls[name], 10**18) for name in ("x", "y", "gap")}
            require(0 < x < 1 and 0 < y < 1 and gap > 0 and -1 < beta < 1, "input PD uncertified")
            return intervals, {"precision_bits": precision, "series_cap": 4, "decimal_digits": digits,
                               "refinements": attempts, "coarse_intervals": coarse,
                               "method": "unique_fmpz(floor(Arb ball * d)); strict Arb comparisons a/d < ball < (a+1)/d; no decimal display parsed",
                               "deflated_zeta": "zeta(s)-1/(s-1)", "original_matrix_pd": True}
        except ValueError as error:
            attempts.append({"precision_bits": precision, "reason": str(error)})
            precision *= 2
    raise ValueError("input certification exhausted 2048 bits")


def tail_certificate(intervals, coarse):
    lower_gap = Fraction(coarse["gap"][0], coarse["gap"][2])
    error = Fraction(5, 2*M)+Fraction(1, 2*M*M)
    remainder = lower_gap-error
    xlo, xhi, xd = intervals["x"]
    _, yhi, yd = intervals["y"]
    lower_x = Fraction(xlo, xd)-Fraction(1, 2*M)
    upper_x = Fraction(xhi, xd)+Fraction(1, 2*M)
    upper_y = Fraction(yhi, yd)+Fraction(1, 2*M)
    blo, bhi, bd = intervals["beta"]
    lower_beta = Fraction(blo, bd)-Fraction(1, 2*M)
    upper_beta = Fraction(bhi, bd)+Fraction(1, 2*M)
    require(remainder > 0 and -1 < lower_x and upper_x < 1 and upper_y < 1, "tail bounds failed")
    require(-1 < lower_beta and upper_beta < 1, "Schur tail strictness failed")
    require(Fraction(intervals["y"][0], yd)-2*Fraction(xhi, xd)**2+1 > 0,
            "independent endpoint PD check failed")
    return {"status": "paper inequality plus exact rational endpoint arithmetic; not Lean-frozen",
            "from_m": M, "gap_lower_used": str(lower_gap), "error_at_M": str(error),
            "gap_minus_error": str(remainder), "rounded_x_lower": str(lower_x),
            "rounded_x_upper": str(upper_x), "rounded_y_upper": str(upper_y),
            "rounded_beta_lower": str(lower_beta), "rounded_beta_upper": str(upper_beta),
            "schur_consequence": "Schur rounded fixed matrix is PD for every integer m>=1400000",
            "proof": "g'=gap+dy-4*x*dx-2*dx^2 >= gap-5/(2m)-1/(2m^2); error decreases for m>=M; -1<x'<1 and y'<1 separately certified",
            "consequence": "entrywise rounded fixed matrix is PD for every integer m>=1400000"}


def float_inputs(intervals):
    values, deficits = [], []
    for name in COORDINATES:
        a, b, d = intervals[name]
        values.append(float(Fraction(a+b, 2*d)))
        # Subtract at rational precision before either binary64 or float32 conversion.
        deficits.append(float(Fraction(2*d-a-b, 2*d)))
    return values, deficits


class MpsCandidates:
    def __init__(self, intervals):
        require("torch" not in sys.modules, "Torch imported before fallback was disabled")
        os.environ["PYTORCH_ENABLE_MPS_FALLBACK"] = "0"
        import torch
        require(torch.backends.mps.is_built() and torch.backends.mps.is_available(), "MPS required")
        self.torch = torch
        self.device = torch.device("mps")
        values, deficits = float_inputs(intervals)
        self.values = torch.tensor(values, device=self.device, dtype=torch.float32)
        self.deficits = torch.tensor(deficits, device=self.device, dtype=torch.float32)
        self.timings, self.executed = [], []
        torch.mps.synchronize()
        self.metadata = {"executed": True, "device": str(self.values.device),
                         "float_dtype": str(self.values.dtype), "integer_dtype": "torch.int64",
                         "mps_built": True, "mps_available": True, "cpu_fallback": "0",
                         "coordinates": list(COORDINATES), "float32_values": self.values.cpu().tolist(),
                         "float32_deficits": self.deficits.cpu().tolist(),
                         "timing_scope": "synchronize before timer and after MPS work; includes allocation and dispatch, excludes CPU transfer"}

    def chunk(self, first, last):
        torch = self.torch
        torch.mps.synchronize()
        started = time.perf_counter()
        m = torch.arange(first, last+1, dtype=torch.int64, device=self.device)
        mf = m.to(torch.float32).unsqueeze(1)
        outputs = {}
        for name, bins in (("naive", torch.floor(mf*self.values+0.5).to(torch.int64)),
                           ("centered", m.unsqueeze(1)-torch.ceil(mf*self.deficits-0.5).to(torch.int64))):
            kx, ky, kb = bins.unbind(1)
            b = m*m+m*ky-2*kx*kx
            psd = (kx.abs() <= m) & (ky.abs() <= m) & (b >= 0)
            pd = (kx.abs() < m) & (ky < m) & (b > 0) & psd
            direct = psd.to(torch.int64)+pd.to(torch.int64)
            schur_psd = (kx.abs() <= m) & (kb.abs() <= m)
            schur = schur_psd.to(torch.int64)+((kx.abs() < m) & (kb.abs() < m)).to(torch.int64)
            outputs[name] = (bins, direct, schur, torch.sign(b))
        torch.mps.synchronize()
        self.timings.append(time.perf_counter()-started)
        self.executed.append([first, last])
        self.metadata["actual_index_device"] = str(m.device)
        self.metadata["actual_index_dtype"] = str(m.dtype)
        self.metadata["actual_sign_device"] = str(outputs["naive"][3].device)
        self.metadata["actual_sign_dtype"] = str(outputs["naive"][3].dtype)
        return {name: tuple(t.cpu().tolist() for t in tensors) for name, tensors in outputs.items()}

    def summary(self):
        return {**self.metadata, "executed_chunks": self.executed,
                "synchronized_seconds_per_chunk": self.timings,
                "synchronized_seconds_total": sum(self.timings)}


def comparison_summary():
    return {"compared_count": 0, "bin_mismatch_resolutions": 0,
            "bin_mismatches_by_coordinate": {name: 0 for name in COORDINATES},
            "entrywise_bin_mismatch_resolutions": 0, "b_sign_mismatches": 0,
            "entrywise_class_mismatches": 0, "schur_class_mismatches": 0,
            "entrywise_counts": dict.fromkeys(CLASSES, 0), "schur_counts": dict.fromkeys(CLASSES, 0),
            "entrywise_confusion_exact_then_candidate": {name: dict.fromkeys(CLASSES, 0) for name in CLASSES},
            "examples": [], "sign_examples": []}


def compare_candidate(summary, m, bins, direct, schur, candidate):
    gpu_bins, gpu_direct, gpu_schur, gpu_sign = candidate
    differing = [name for name, expected, actual in zip(COORDINATES, bins, gpu_bins) if expected != actual]
    b = m*m+m*bins[1]-2*bins[0]*bins[0]
    sign = (b > 0)-(b < 0)
    summary["compared_count"] += 1
    summary["bin_mismatch_resolutions"] += bool(differing)
    summary["entrywise_bin_mismatch_resolutions"] += any(name in differing for name in ("x", "y"))
    for name in differing:
        summary["bin_mismatches_by_coordinate"][name] += 1
    summary["b_sign_mismatches"] += sign != gpu_sign
    summary["entrywise_class_mismatches"] += direct != CLASSES[gpu_direct]
    summary["schur_class_mismatches"] += schur != CLASSES[gpu_schur]
    summary["entrywise_counts"][CLASSES[gpu_direct]] += 1
    summary["schur_counts"][CLASSES[gpu_schur]] += 1
    summary["entrywise_confusion_exact_then_candidate"][direct][CLASSES[gpu_direct]] += 1
    if differing or sign != gpu_sign or direct != CLASSES[gpu_direct] or schur != CLASSES[gpu_schur]:
        sample = {"m": m, "exact_bins": bins, "candidate_bins": gpu_bins,
                  "exact_entrywise": direct, "candidate_entrywise": CLASSES[gpu_direct],
                  "exact_schur": schur, "candidate_schur": CLASSES[gpu_schur],
                  "exact_b_sign": sign, "candidate_b_sign": gpu_sign}
        if len(summary["examples"]) < 6:
            summary["examples"].append(sample)
        if sign != gpu_sign and len(summary["sign_examples"]) < 3:
            summary["sign_examples"].append(sample)
        summary["last_example"] = sample


def system_evidence():
    def command(args):
        return subprocess.check_output(args, text=True).strip()
    evidence = {"python": platform.python_version(), "python_executable": sys.executable,
                "platform": platform.platform(), "machine": platform.machine(),
                "dependencies": {name: importlib.metadata.version(name) for name in ("torch", "numpy", "python-flint")}}
    if sys.platform == "darwin":
        evidence["hardware"] = {key: command(["sysctl", "-n", key])
                                for key in ("hw.model", "machdep.cpu.brand_string", "hw.memsize", "hw.logicalcpu")}
        displays = json.loads(command(["system_profiler", "SPDisplaysDataType", "-json"]))
        evidence["graphics"] = [{key: row.get(key) for key in ("sppci_model", "sppci_cores", "spdisplays_mtlgpufamilysupport")}
                                for row in displays["SPDisplaysDataType"]]
    root = Path(__file__).resolve().parents[3]
    sources = [Path(__file__).resolve(), Path(state_store.__file__).resolve(), root / "tools/Makefile"]
    evidence["source_manifest"] = {str(path.relative_to(root)): state_store.file_hash(path) for path in sources}
    evidence["source_head"] = command(["git", "-C", str(root), "rev-parse", "HEAD"])
    return evidence


def publish_report(path, report):
    require(report["status"] == "publication_unconfirmed" and report["mathematical_status"] == "complete"
            and report["coverage"]["unresolved_count"] == 0,
            "incomplete runs cannot publish/replace a report")
    path = Path(path).resolve()
    root = Path(__file__).resolve().parents[3]
    if root in path.parents:
        require(root / "docs/reports" in path.parents and report["mps"]["executed"]
                and report["coverage"]["requested_interval"] == [1, M-1],
                "repository reports require a full actual MPS prefix")
    path.parent.mkdir(parents=True, exist_ok=True)
    # One line per top-level field keeps the evidence compact without dropping data.
    body = "{\n"+",\n".join("  "+json.dumps(key)+": "+json.dumps(value, sort_keys=True, allow_nan=False)
                             for key, value in report.items())+"\n}"
    text = ("# Actual Xi Quantization, 2026-09-08\n\n"
            "Generated numerical-library evidence for one fixed three-observation matrix. "
            "The analytic tail is a paper argument with exact endpoint arithmetic; nothing here is Lean-frozen. "
            "GPU outputs are candidates. Counts and the mathematical digest cover only the requested prefix; "
            "the two controls are separately recorded. This is a certified pre-publication snapshot: "
            "publication_unconfirmed does not assert I/O success. Consult the runtime record and process exit "
            "for the subsequent publication/recording outcome. Independent review and PR publication remain caller-owned.\n\n"
            "```json\n"+body+"\n```\n")
    state_store.atomic_write(path, lambda stream: stream.write(text.encode("utf-8")))


def run(args):
    validate_range(args.first, args.last, args.chunk)
    require(128 <= args.precision <= 2048 and 18 <= args.digits <= 100, "unsupported precision/digits")
    state = state_store.external_path(args.state_dir)
    coverage = Coverage(args.first, args.last)
    digest = hashlib.sha256()
    counters = {method: Counter({key: 0 for key in CLASSES}) for method in ("entrywise", "schur")}
    extremes = {method: {} for method in counters}
    comparisons = {method: comparison_summary() for method in ("naive", "centered")}
    report = {"schema_version": 2, "status": "incomplete", "started_at_utc": state_store.utc_now(),
              "publication_contract": "mathematical_status describes certified coverage only. Markdown is a pre-publication snapshot with status=publication_unconfirmed, even on successful writes. Runtime/stdout status=complete records that the report writer returned; exit 0 additionally requires runtime recording to return. Failures before replacement preserve old destination bytes. A failed post-replacement directory sync may leave new visible bytes; persistence is uncertain. No rollback is promised. Runtime records use the same writer and cannot certify their own final sync.",
              "command": shlex.join(PINS+[str(Path(__file__).resolve()), *sys.argv[1:]]),
              "settings": vars(args), "evidence_status": "Arb enclosure + exact Python integers; not Lean-frozen",
              "exact_classification": "CPU Python arbitrary-precision integers; both endpoints of x,y,beta certified at EVERY classified m, including MPS nonnegative candidates",
              "quantizer": "Q_m(t)=floor(m*t+1/2)/m; ties toward positive infinity",
              "stream_serialization": "ASCII, increasing m; no header; m,kx,ky,kbeta,entrywise_class,schur_class followed by LF; classes indefinite/singular/pd; controls excluded",
              "schur_preservation": "For |kx|,|kb|<=m, y'=(m*kx^2+(m^2-kx^2)*kb)/m^3 and det=(1-x'^2)^2*(1-beta'^2)>=0; PD iff both strict. Universal algebra, not an enumerative proof.",
              "mps": {"executed": False, "reason": "no MPS run (CPU-only mode)" if args.mode == "cpu" else "MPS not yet executed"}}
    gpu = None
    # This lock covers certification and GPU use, with the existing shared exclusion order.
    with state_store.StateLocks(state) as locks:
        state.mkdir(parents=True, exist_ok=True)
        runtime_path = state / ("run-"+report["started_at_utc"].replace(":", "-")+f"-{os.getpid()}.json")
        report["runtime_record"] = str(runtime_path)
        report["lock_paths"] = list(map(str, locks.paths))
        try:
            report["environment"] = system_evidence()
            require(report["environment"]["dependencies"] == {"torch": "2.8.0", "numpy": "2.0.2", "python-flint": "0.8.0"}
                    and sys.version_info[:2] == (3, 12), "use the pinned Make command")
            intervals, receipt = generate_inputs(args.precision, args.digits)
            report["rational_intervals_a_b_d"] = intervals
            report["input_certification"] = receipt
            report["tail"] = tail_certificate(intervals, receipt["coarse_intervals"])
            if args.mode == "mps":
                gpu = MpsCandidates(intervals)
            started = time.perf_counter()
            for first in range(args.first, args.last+1, args.chunk):
                last = min(args.last, first+args.chunk-1)
                candidates = gpu.chunk(first, last) if gpu else {}
                for offset, m in enumerate(range(first, last+1)):
                    bins = [certified_bin(intervals[name], m) for name in COORDINATES]
                    if None in bins:
                        coverage.record(m, False)
                        continue
                    kx, ky, kb = bins
                    direct, schur = entrywise_class(m, kx, ky), schur_class(m, kx, kb)
                    y_numerator = m*kx*kx+(m*m-kx*kx)*kb
                    require((m**3-y_numerator)*(m**3+y_numerator-2*m*kx*kx)
                            == (m*m-kx*kx)**2*(m*m-kb*kb), "per-resolution Schur reconstruction")
                    for name, tensors in candidates.items():
                        compare_candidate(comparisons[name], m, bins, direct, schur,
                                          tuple(t[offset] for t in tensors))
                    digest.update(stream_row(m, kx, ky, kb, direct, schur))
                    for method, outcome, pair in (("entrywise", direct, (kx, ky)), ("schur", schur, (kx, kb))):
                        counters[method][outcome] += 1
                        rows = extremes[method].setdefault(outcome, {"first": [m, *pair]})
                        rows["last"] = [m, *pair]
                    coverage.record(m, True)
            report["enumeration_seconds"] = time.perf_counter()-started
            report["controls"] = {}
            for m in (200, M):
                bins = [certified_bin(intervals[name], m) for name in COORDINATES]
                require(None not in bins, "control bins unresolved")
                kx, ky, kb = bins
                control = {"certified_bins": bins, "entrywise": entrywise_witness(m, kx, ky),
                           "schur": schur_witness(m, kx, kb)}
                if gpu:
                    control["mps"] = {name: {"bins": values[0][0], "entrywise": CLASSES[values[1][0]],
                                             "schur": CLASSES[values[2][0]], "b_sign": values[3][0]}
                                      for name, values in gpu.chunk(m, m).items()}
                report["controls"][str(m)] = control
            report["witnesses"] = {method: {outcome: {end: (entrywise_witness(*row) if method == "entrywise"
                                                            else schur_witness(*row)) for end, row in ends.items()}
                                               for outcome, ends in classes.items()} for method, classes in extremes.items()}
            require(all(sum(counts.values()) == coverage.classified for counts in counters.values()), "count conservation")
            if gpu:
                require(all(c["compared_count"] == coverage.classified for c in comparisons.values()), "GPU comparison coverage")
            report["status"] = "complete" if coverage.summary()["unresolved_count"] == 0 else "incomplete"
        except (Exception, KeyboardInterrupt) as error:
            report["error"] = f"{type(error).__name__}: {error}"
        report["coverage"] = coverage.summary()
        report["exact_counts"] = counters
        report["schur_reconstruction_identity_checked_count"] = coverage.classified
        report["classification_sha256"] = digest.hexdigest()
        report["digest_complete_for_requested_interval"] = report["status"] == "complete"
        report["all_positive_integer_resolutions_classified"] = (report["status"] == "complete"
                                                                and [args.first, args.last] == [1, M-1])
        report["gpu_comparisons"] = comparisons if gpu else None
        if gpu:
            report["mps"] = gpu.summary()
        report["finished_at_utc"] = state_store.utc_now()
        report["mathematical_status"] = report["status"]
        if report["mathematical_status"] == "complete":
            report["status"] = "publication_unconfirmed"
        try:
            # Persist certified coverage before attempting the independent report write.
            state_store.atomic_json(runtime_path, report)
            if report["mathematical_status"] == "complete":
                try:
                    publish_report(args.report, report)
                except (Exception, KeyboardInterrupt) as error:
                    report.update(status="publication_failed", error=f"{type(error).__name__}: {error}")
                else:
                    report["status"] = "complete"
                state_store.atomic_json(runtime_path, report)
        except (Exception, KeyboardInterrupt) as error:
            report["runtime_record_error"] = f"{type(error).__name__}: {error}"
            if report["status"] != "publication_failed":
                report["status"] = "recording_failed"
        print(json.dumps({"status": report["status"], "runtime_record": str(runtime_path),
                          "mathematical_status": report["mathematical_status"],
                          "coverage": report["coverage"], "exact_counts": counters,
                          "classification_sha256": digest.hexdigest(), "error": report.get("error"),
                          "runtime_record_error": report.get("runtime_record_error")}, sort_keys=True))
        return 0 if report["status"] == "complete" and "runtime_record_error" not in report else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mode", choices=("mps", "cpu"), default="mps")
    parser.add_argument("--first", type=int, default=1)
    parser.add_argument("--last", type=int, default=M-1)
    parser.add_argument("--chunk", type=int, default=65536, help="bounded rows per allocation, not a throughput promise")
    parser.add_argument("--precision", type=int, default=256)
    parser.add_argument("--digits", type=int, default=40)
    parser.add_argument("--state-dir", default="/tmp/qgh-xi-quantization-state")
    parser.add_argument("--report", default="/tmp/qgh-xi-quantization-state/report.md")
    try:
        return run(parser.parse_args())
    except (ValueError, OSError) as error:
        print(f"XI_QUANTIZATION_FAILED {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())

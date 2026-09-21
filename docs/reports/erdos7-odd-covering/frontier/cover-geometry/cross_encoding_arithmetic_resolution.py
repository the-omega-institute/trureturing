#!/usr/bin/env python3
"""Exact bounded numeration/odd-cover diagnostic; Python standard library only."""
import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import itertools
import json
import sys
from pathlib import Path

CHECKS = 0


def require(condition, label):
    global CHECKS
    CHECKS += 1
    if not condition:
        raise RuntimeError(label)


def weights(k, count):
    if k is None:
        return [2 ** j for j in range(count)]
    out = []
    for j in range(count):
        out.append(2 ** j if j < k else sum(out[-k:]))
    return out


def legal(word, k):
    return k is None or "1" * k not in "".join(map(str, word))


def encode(value, k):
    if value == 0:
        return ()
    ws = weights(k, value.bit_length() * 2 + 3)
    while ws[-1] <= value:
        ws = weights(k, 2 * len(ws))
    count = next(i for i, w in enumerate(ws) if w > value)
    out = [0] * count
    for i in reversed(range(count)):
        if ws[i] <= value:
            out[i] = 1
            value -= ws[i]
    require(value == 0, "greedy exhausted value")
    require(legal(out, k), "greedy legality")
    return tuple(out)


def decode(word, k):
    return sum(d * w for d, w in zip(word, weights(k, len(word))))


def covered(s, family):
    return any(s % m == a for a, m in family)


def autonomous(k, modulus, word):
    phase = tuple(w % modulus for w in weights(k, k)) if k else (1 % modulus,)
    residue = run = 0
    for digit in word:
        require(digit == 0 or k is None or run < k - 1, "autonomous guard")
        residue = (residue + digit * phase[0]) % modulus
        phase = phase[1:] + (sum(phase) % modulus,) if k else (2 * phase[0] % modulus,)
        run = 0 if digit == 0 or k is None else run + 1
    return residue


def layered(k, modulus, depth):
    counts = Counter({(0, 0): 1})
    widths = [1]
    for w in weights(k, depth):
        new = Counter()
        for (run, s), count in counts.items():
            new[(0, s)] += count
            if k is None or run < k - 1:
                new[(0 if k is None else run + 1, (s + w) % modulus)] += count
        counts = new
        widths.append(len(counts))
    residues = Counter()
    for (_, s), count in counts.items():
        residues[s] += count
    return residues, widths


def phase_period(k, modulus, cap=100000):
    initial = tuple(w % modulus for w in weights(k, k))
    state = initial
    for period in range(1, cap + 1):
        nxt = state[1:] + (sum(state) % modulus,)
        previous = ((nxt[-1] - sum(nxt[:-1])) % modulus,) + nxt[:-1]
        require(previous == state, "companion inverse")
        state = nxt
        if state == initial:
            return period
    return None


def compute():
    rows = []
    periods = []
    ks = [2, 3, 4, 5, None]
    moduli = [3, 9, 15, 27, 45, 105, 315]
    for modulus in moduli:
        family = [((m // 3 + 1) % m, m) for m in range(2, modulus + 1)
                  if modulus % m == 0]
        survivors = [s for s in range(modulus) if not covered(s, family)]
        survivor_hash = hashlib.sha256(json.dumps(survivors).encode()).hexdigest()
        for k in ks:
            ws = weights(k, 32)
            depth = next(n for n, w in enumerate(ws) if w >= modulus)
            words = [word for word in itertools.product((0, 1), repeat=depth)
                     if legal(word, k)]
            values = [decode(word, k) for word in words]
            require(sorted(values) == list(range(ws[depth])), "whole interval bijection")
            direct = Counter(v % modulus for v in values)
            dp, widths = layered(k, modulus, depth)
            require(dp == direct, "layered DP equals independent enumeration")
            for s in range(modulus):
                expected = ws[depth] // modulus + (s < ws[depth] % modulus)
                require(dp[s] == expected, "exact residue multiplicity")
            enc = [encode(s, k) for s in range(modulus)]
            require(len(set(enc)) == modulus, "canonical representatives injective")
            decoded_survivors = []
            for s, word in enumerate(enc):
                require(decode(word, k) == s, "canonical decode")
                # The uniform law is on s, not on all padded legal words.
                residue = 0
                run = 0
                for j, digit in enumerate(word):
                    require(digit == 0 or k is None or run < k - 1, "run guard")
                    residue = (residue + digit * ws[j]) % modulus
                    run = 0 if digit == 0 or k is None else run + 1
                require(residue == s, "representative path final residue")
                require(autonomous(k, modulus, word) == s, "full-phase autonomous residue")
                if not covered(residue, family):
                    decoded_survivors.append(s)
            require(decoded_survivors == survivors, "same arithmetic survivor")
            counts_by_length = Counter(map(len, enc))
            rows.append({"k": "binary" if k is None else k, "L": modulus,
                         "family": family, "survivors": len(survivors),
                         "survivor_sha256": survivor_hash,
                         "uniform_survivor_mass": str(Fraction(len(survivors), modulus)),
                         "max_code_length": max(map(len, enc)),
                         "mean_code_length": str(Fraction(sum(map(len, enc)), modulus)),
                         "length_counts": dict(sorted(counts_by_length.items())),
                         "padded_length": depth, "padded_legal_words": len(words),
                         "padded_survivor_words": sum(c for s, c in dp.items()
                                                       if not covered(s, family)),
                         "layered_state_widths": widths})
    for k in ks[:-1]:
        for modulus in [3, 5, 9, 15, 27]:
            period = phase_period(k, modulus)
            periods.append({"k": k, "L": modulus, "period": period,
                            "cap": 100000, "status": "exact" if period else "cap-exhausted",
                            "unminimized_product_bound": None if period is None
                            else k * modulus * period})

    chain = [1, 3, 9, 45, 315]
    transport_checks = 0
    for lower, higher in zip(chain, chain[1:]):
        for s in range(higher):
            for k, ell in itertools.product(ks, repeat=2):
                # Both orders are explicit conjugations of arithmetic reduction.
                first_reduce = encode(decode(encode(s, k), k) % lower, k)
                first_recode = encode(decode(encode(s, k), k), ell)
                left = encode(decode(first_reduce, k), ell)
                right = encode(decode(first_recode, ell) % lower, ell)
                require(left == right, "encoded arithmetic square commutes")
                transport_checks += 1

    controls = []
    for family, modulus in [([(1, 3)], 3), ([(0, 3), (1, 9), (2, 27)], 27),
                            ([(0, 2), (0, 3), (1, 4), (5, 6), (7, 12)], 12)]:
        expected = [s for s in range(modulus) if not covered(s, family)]
        for k in ks:
            actual = [decode(encode(s, k), k) for s in range(modulus)
                      if not covered(decode(encode(s, k), k), family)]
            require(actual == expected, "positive and negative coverage controls")
        controls.append({"family": family, "L": modulus, "survivors": expected})
    require(len(controls[1]["survivors"]) == 14, "known 14/27 control")
    require(controls[2]["survivors"] == [], "even whole-cover control")
    require(covered(1, [(1, 3)]) and not covered(3, [(1, 3)]), "prefix pruning refuted")
    for k in ks:
        prefix, extension = (0,), (0, 1)
        require(extension[:len(prefix)] == prefix and legal(prefix, k) and legal(extension, k),
                "all-k legal LSB prefix continuation")
        require(covered(decode(prefix, k), [(0, 3)])
                and not covered(decode(extension, k), [(0, 3)]),
                "all-k covered prefix extends to survivor")
    require(decode((1, 0, 1), 2) == 4 and decode((1, 1), 2) == 3,
            "deleting forced zero changes value")
    require(not legal((1, 1), 2), "deleting forced zero can also break legality")
    # Empty/all-zero histories have identical (run,residue), differing phase.
    require((0 + weights(2, 2)[0]) % 3 != (0 + weights(2, 2)[1]) % 3,
            "phase-free state is not autonomous")
    prefix_witnesses = []
    for k in ks:
        ws = weights(k, 80)
        for prefix_length in [1, 2, 5, 10, 20, 40]:
            j = next(j for j in range(prefix_length, len(ws)) if ws[j] % 3)
            word = (0,) * j + (1,)
            require(legal(word, k) and not any(word[:prefix_length])
                    and decode(word, k) % 3 != 0, "same low prefix different mod3")
            prefix_witnesses.append({"k": "binary" if k is None else k,
                                     "prefix_length": prefix_length, "one_position": j,
                                     "residue_mod3": ws[j] % 3})
    for value, k, display in [(45, None, "101101"), (45, 2, "10010100"),
                              (45, 3, "1000001")]:
        require("".join(map(str, reversed(encode(value, k)))) == display, "45 example")
    return {"scope": "bounded diagnostic, not an unrestricted noncoverage proof",
            "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "active_checks": CHECKS, "rows": rows, "periods": periods,
            "arithmetic_transport_checks": transport_checks, "controls": controls,
            "prefix_witnesses": prefix_witnesses,
            "adversarial_controls": {"covered_prefix_can_escape": [1, 3],
             "all_k_lsb_prefix_escape": {"prefix": [0], "extension": [0, 1],
                                         "values": [0, 2], "covered_class": [0, 3]},
             "zeckendorf_forced_zero_values": [4, 3],
             "phase_free_next_mod3": [1, 2]}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", type=Path, default=Path(__file__).resolve().parents[2],
                        help="erdos7-odd-covering report directory")
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--write", action="store_true")
    group.add_argument("--check", action="store_true")
    args = parser.parse_args()
    base = args.base.resolve()
    sys.path.insert(0, str(base))
    import certificate_io
    source_relative = Path("frontier/cover-geometry/cross_encoding_arithmetic_resolution.py")
    if (base / source_relative).resolve() != Path(__file__).resolve():
        raise RuntimeError("program must belong to the supplied report base")
    result = json.loads(json.dumps(compute()))
    result["source_path"] = source_relative.as_posix()
    result["certificate_io_sha256"] = hashlib.sha256(
        Path(certificate_io.__file__).read_bytes()).hexdigest()
    target = (base / source_relative).with_suffix(".json")
    if args.write:
        certificate_io.write_certificate_text(
            target, json.dumps(result, indent=2, sort_keys=True) + "\n")
    else:
        require(result == json.loads(certificate_io.read_artifact_bytes(target)),
                "retained result replay")
    print(json.dumps({"status": "PASS", "active_checks": CHECKS,
                      "encoding_cases": len(result["rows"]),
                      "period_cases": len(result["periods"])}))


if __name__ == "__main__":
    main()

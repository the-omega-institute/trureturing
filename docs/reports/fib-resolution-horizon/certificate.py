#!/usr/bin/env python3
"""Fixed 165-task exact finite experiment for theory sections 104–110.

Python 3.9+ standard library only. No input files are used.
Write deterministic JSON to stdout, or use --output PATH. See README.md for
the actual-source reachability proof and the finite scope of the results.
"""

import argparse
import hashlib
import json
import math
from pathlib import Path
import sys


WINDOWS = ((0, 0, 0), (1, 0, 0), (0, 1, 0), (1, 0, 1), (0, 0, 1))
TAGS = ((0, False), (0, True), (1, True))


def require(condition, message):
    """Checks remain active under python -O."""
    if not condition:
        raise RuntimeError(message)


def vector_hash(values):
    """SHA-256 of consecutive unsigned 32-bit little-endian integers."""
    digest = hashlib.sha256()
    for value in values:
        digest.update(value.to_bytes(4, "little"))
    return digest.hexdigest()


def intern(values):
    """Canonical class IDs: first occurrence in the given state order."""
    classes = {}
    return [classes.setdefault(value, len(classes)) for value in values]


def factors(n):
    result = []
    p = 2
    while p * p <= n:
        if n % p == 0:
            h = 0
            while n % p == 0:
                n //= p
                h += 1
            result.append((p, h))
        p += 1
    if n > 1:
        result.append((n, 1))
    return result


def local_axes(H, d):
    require(d > 0 and H % d == 0, "d must divide H")
    axes = []
    for p, h in factors(H):
        e, rest = 0, d
        while rest % p == 0:
            rest //= p
            e += 1
        axes.append((p, h, e, p ** (h - e)))
    return axes


def eta(r, axes):
    labels = []
    for p, h, e, M in axes:
        x = r % (p ** h)
        t, unit = 0, x
        if x == 0:
            t = h
        else:
            while unit % p == 0:
                unit //= p
                t += 1
        if t < e:
            labels.append(("S", t, (x // (p ** t)) % M))
        else:
            labels.append(("D", (x // (p ** e)) % M))
    return tuple(labels)


def encode(H, phase, r, tag):
    return (phase * H + r) * 3 + tag


def bit_step(H, r, tag, row, word):
    """Literal low-to-high bits; None denotes an illegal seam."""
    seam, _ = TAGS[tag]
    u, v = row
    nonzero = False
    for bit in word:
        if seam and bit:
            return None
        r = (r + bit * u) % H
        u, v = v, (u + v) % H
        seam = bit
        nonzero = nonzero or bool(bit)
    next_tag = 0 if not nonzero else (2 if seam else 1)
    return r, next_tag, (u, v)


def build_graph(H, ds):
    initial_row = (2 % H, 3 % H)
    row, orbit, seen = initial_row, [], set()
    while row not in seen:
        seen.add(row)
        orbit.append(row)
        u, v = row
        require(math.gcd(math.gcd(u, v), H) == 1, "Nonprimitive row")
        row = ((u + 2 * v) % H, (2 * u + 3 * v) % H)
    require(row == initial_row, "Orbit did not return to its initial row")
    period = len(orbit)
    sink = 3 * period * H
    edges, illegal = [], 0
    for phase, (u, v) in enumerate(orbit):
        next_phase = (phase + 1) % period
        for r in range(H):
            for tag in range(3):
                require(len(edges) == 5 * encode(H, phase, r, tag),
                        "State enumeration mismatch")
                for word in WINDOWS:
                    b0, b1, b2 = word
                    if TAGS[tag][0] and b0:
                        target = sink
                        illegal += 1
                    else:
                        next_r = (r + (b0 + b2) * u + (b1 + b2) * v) % H
                        next_tag = 0 if word == (0, 0, 0) else (2 if b2 else 1)
                        target = encode(H, next_phase, next_r, next_tag)
                    by_bits = bit_step(H, r, tag, (u, v), word)
                    if by_bits is None:
                        require(target == sink, "Illegal bit/window disagreement")
                    else:
                        br, bt, brow = by_bits
                        require(brow == orbit[next_phase], "Bit/window row disagreement")
                        require(target == encode(H, next_phase, br, bt),
                                "Bit/window transition disagreement")
                    require(0 <= target <= sink, "Successor outside graph")
                    edges.append(target)
    edges.extend([sink] * 5)
    require(len(edges) == 5 * (sink + 1), "Incomplete graph")
    require(edges[5 * sink:] == [sink] * 5, "Sink is not absorbing")
    require(illegal == 2 * period * H, "Wrong illegal seam count")
    starts = [encode(H, 0, 0, 0), encode(H, 0, 1, 2)]
    require(starts == [0, 5] and max(starts) < sink, "Missing initial states")
    metadata = dict(H=H, divisors=ds, period=period, phase_order=orbit,
                    states=sink + 1, edges=len(edges), sink=sink,
                    initial_states_epsilon_0_1=starts,
                    transition_vector_sha256=vector_hash(edges),
                    bit_window_transition_pairs_checked=5 * sink,
                    illegal_seam_edges=illegal)
    return edges, metadata


def check_labels(H, d, labels):
    """Compare eta's partition with all allowed affine arithmetic responses."""
    actual = intern(labels)
    arithmetic = intern(
        tuple(H // math.gcd(a * r + d * b, H)
              for a in range(H) for b in range(H // d))
        for r in range(H))
    require(actual == arithmetic, "Eta/affine arithmetic partition mismatch")
    require([r for r in range(H) if labels[r] == labels[0]] == [0],
            "Eta zero fiber is not a singleton")
    if d == 1:
        require(len(set(labels)) == H, "Full-residue endpoint not injective")
    if d == H:
        require(actual == intern(H // math.gcd(r, H) for r in range(H)),
                "Gcd endpoint partition mismatch")


def moore(H, d, edges, states):
    axes = local_axes(H, d)
    labels = [eta(r, axes) for r in range(H)]
    check_labels(H, d, labels)
    old = intern(("err",) if state == states - 1 or state % 3 == 0
                 else ("eta", labels[(state // 3) % H])
                 for state in range(states))
    require(old[-1] == old[0] == 0, "Sink/false-End output mismatch")
    require(old[1] != 0 and old[2] != 0, "Successful zero residue rejected")
    counts, hashes, changes = [max(old) + 1], [vector_hash(old)], []
    # At most states - |P0| strict refinements, then one equality round.
    for round_index in range(1, states - counts[0] + 2):
        ids, new, parent = {}, [], []
        for state in range(states):
            off = 5 * state
            key = (old[state],) + tuple(old[edges[off + a]] for a in range(5))
            class_id = ids.get(key)
            if class_id is None:
                class_id = len(ids)
                ids[key] = class_id
                parent.append(old[state])
            require(parent[class_id] == old[state], "Refinement merged old classes")
            new.append(class_id)
        same = old == new  # The stopping test is the FULL vector comparison.
        changed = sum(a != b for a, b in zip(old, new))
        require(same == (changed == 0), "Equality/changed-position disagreement")
        require(len(ids) >= counts[-1], "Class count decreased")
        require(same or len(ids) > counts[-1], "Nonstable round did not split")
        counts.append(len(ids))
        changes.append(changed)
        hashes.append(vector_hash(new))  # Documentation only, after comparison.
        if same:
            depth = round_index - 1
            require(depth >= 1, "Live false-End/sink distinction was lost")
            require(all(a < b for a, b in zip(counts[:-2], counts[1:-1])),
                    "A previous refinement was not strict")
            require(all(value > 0 for value in changes[:-1]),
                    "Earlier stability was missed")
            return dict(H=H, d=d, Q=max((p ** e for p, e in factors(d)), default=None),
                        H_over_d=H // d, states=states, axes_p_h_e_M=axes,
                        eta_residue_label_count=len(set(labels)), depth=depth,
                        refinement_rounds=round_index, partition_cardinalities=counts,
                        changed_vector_positions=changes, partition_vector_sha256=hashes)
        old = new
    raise RuntimeError("Finite refinement bound exceeded")


def run():
    scope = [(H, [d for d in range(1, H + 1) if H % d == 0])
             for H in range(2, 41)]
    scope.extend((H, [1, 2, 4, 8]) for H in (64, 128))
    graphs, tasks = [], []
    for H, ds in scope:
        edges, graph = build_graph(H, ds)
        graphs.append(graph)
        tasks.extend(moore(H, d, edges, graph["states"]) for d in ds)
    totals = dict(graphs=len(graphs), tasks=len(tasks),
                  states=sum(g["states"] for g in graphs),
                  edges=sum(g["edges"] for g in graphs))
    require(totals == dict(graphs=41, tasks=165, states=95831, edges=479155),
            "Fixed experiment scope mismatch")
    expected = {(H, d) for H, ds in scope for d in ds}
    require({(t["H"], t["d"]) for t in tasks} == expected, "Missing task")
    require(all(t["depth"] == 1 for t in tasks if t["d"] == 1),
            "One-window full-residue consistency failed")
    return dict(
        schema="fib-resolution-horizon-finite-v1",
        contract=dict(
            windows=["".join(map(str, w)) for w in WINDOWS],
            tags=[dict(name=name, seam=s, E=E) for name, (s, E) in zip("ABC", TAGS)],
            state_index="(phase*H+residue)*3+tag; sink=3*period*H",
            phase_order="Orbit of (2,3) modulo H under (u,v)->(u+2v,2u+3v)",
            output="sink or E=false: err; otherwise eta(residue), including residue zero",
            partition_order="First-seen IDs in increasing state order, starting at 0",
            depth="First L with full canonical vectors P_L=P_(L+1); P0 is output",
            vector_hash_encoding="SHA-256 of uint32 little-endian entries without header"),
        scope=dict(main_H_inclusive=[2, 40], main_divisors="all positive divisors",
                   extra_H=[64, 128], extra_d=[1, 2, 4, 8], totals=totals),
        graphs=graphs, tasks=tasks,
        checks=dict(
            all_bit_window_transitions_equal=True,
            exact_first_return_orbits_and_primitive_rows=True,
            both_initial_states_and_absorbing_sink=True,
            successful_zero_residue_preserved=True,
            all_eta_partitions_equal_all_affine_arithmetic_responses=True,
            all_eta_zero_fibers_singleton=True,
            full_residue_and_gcd_endpoint_partitions=True,
            every_round_retains_old_class=True,
            every_nonterminal_round_strictly_refines=True,
            every_terminal_full_vector_comparison_equal=True,
            every_d1_depth_equals_one=True))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Write JSON here instead of stdout")
    args = parser.parse_args()
    require(sys.version_info >= (3, 9), "Python 3.9 or newer is required")
    text = json.dumps(run(), sort_keys=True, indent=2, ensure_ascii=True) + "\n"
    if args.output is None:
        sys.stdout.write(text)
    else:
        args.output.write_bytes(text.encode("ascii"))


if __name__ == "__main__":
    main()

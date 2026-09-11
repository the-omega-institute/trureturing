"""Frozen graph passes and streamed structural rows; never census assessments."""

import collections
import gzip
import json
import pathlib
import shutil
import sqlite3
import time
import zlib

from emission import parse_name_key
from incremental import atomic_json
from streaming import canonical, digest
from Structure.store import wire_key
from Structure.writing import jsonl_elements, object_prefix


def topology(adj):
    reverse = [[] for _ in adj]
    remaining = [len(edges) for edges in adj]
    for source, edges in enumerate(adj):
        for target in edges:
            reverse[target].append(source)
    queue = collections.deque(i for i, count in enumerate(remaining) if not count)
    depth, order = [0] * len(adj), []
    while queue:
        node = queue.popleft()
        order.append(node)
        for consumer in reverse[node]:
            depth[consumer] = max(depth[consumer], depth[node] + 1)
            remaining[consumer] -= 1
            if remaining[consumer] == 0:
                queue.append(consumer)
    return depth, order, reverse


def reachable(adj, seeds):
    seen, pending = set(seeds), list(seeds)
    while pending:
        for target in adj[pending.pop()]:
            if target not in seen:
                seen.add(target)
                pending.append(target)
    return seen


def cyclic_nodes(adj, reverse):
    # Iterative Kosaraju, so a long frozen chain does not exhaust Python recursion.
    seen, finish = set(), []
    for start in range(len(adj)):
        if start in seen:
            continue
        stack = [(start, False)]
        while stack:
            node, exiting = stack.pop()
            if exiting:
                finish.append(node)
            elif node not in seen:
                seen.add(node)
                stack.append((node, True))
                stack.extend((target, False) for target in adj[node] if target not in seen)
    seen, cycles = set(), set()
    for start in reversed(finish):
        if start in seen:
            continue
        component, pending = set(), [start]
        seen.add(start)
        while pending:
            node = pending.pop()
            component.add(node)
            for target in reverse[node]:
                if target not in seen:
                    seen.add(target)
                    pending.append(target)
        if len(component) > 1 or start in adj[start]:
            cycles.update(component)
    return cycles


def descendants(reverse, order, path):
    """Reverse-topological unions of disk-backed compressed exact bit sets.

    One accumulator and one operand are resident. Total disk/time can be
    superlinear; no all-node table of transitive sets is kept in memory.
    """
    counts = [None] * len(reverse)
    with sqlite3.connect(path) as db:
        db.executescript("PRAGMA cache_size=-8192; PRAGMA temp_store=FILE;"
                         "DROP TABLE IF EXISTS sets; CREATE TABLE sets(node INTEGER PRIMARY KEY,bits BLOB);")
        for node in reversed(order):
            bits = 0
            for consumer in reverse[node]:
                row = db.execute("SELECT bits FROM sets WHERE node=?", (consumer,)).fetchone()
                if row is not None:
                    bits |= int.from_bytes(zlib.decompress(row[0]), "little") | (1 << consumer)
            counts[node] = bin(bits).count("1")
            encoded = bits.to_bytes((bits.bit_length() + 7) // 8, "little")
            db.execute("INSERT INTO sets VALUES (?,?)", (node, zlib.compress(encoded)))
    return counts


def display_name(value):
    if value == ["anonymous"]:
        return ""
    parent = display_name(value[1])
    return (parent + "." if parent else "") + str(value[2])


def analyse(store, keys, output, core, *, cache=None, axioms=None, mark=lambda _: None):
    keys = sorted(tuple(key) for key in keys)
    identities = {key[2]: i for i, key in enumerate(keys)}
    if len(identities) != len(keys) or len({(k[1], k[2]) for k in keys}) != len(keys):
        raise ValueError("frozen_key_ambiguous")
    output = pathlib.Path(output)
    folder = pathlib.Path(cache) if cache else output.parent / "structure-work"
    folder.mkdir(parents=True, exist_ok=True)
    store.set_frozen(keys)
    axioms = axioms or {}
    # This policy identity includes the whole projection implementation. Raw
    # reader caches have their own narrower fingerprint, independent of it.
    policy = digest([sorted(core), "first_frozen_hit_all_repository_declarations_stop_axiom",
                     [(p.name, p.read_text()) for p in [pathlib.Path(__file__),
                       pathlib.Path(__file__).with_name("store.py"),
                       pathlib.Path(__file__).with_name("writing.py")]]])
    snapshot = digest([store.snapshot(), keys, policy, sorted((list(k), v) for k, v in axioms.items())])
    rows_cache = folder / (snapshot[7:] + ".rows.gz")
    summary_cache = folder / (snapshot[7:] + ".summary.json")
    if cache and rows_cache.is_file() and summary_cache.is_file():
        mark("structure_snapshot_restore")
        started = time.monotonic()
        with gzip.open(rows_cache, "rb") as source, output.open("wb") as target:
            shutil.copyfileobj(source, target, 1024 * 1024)
        result = json.loads(summary_cache.read_bytes())
        result["cache"] = {"snapshot_hit": True, "fold_hits": len(keys), "fold_misses": 0}
        result["timings_s"] = {"snapshot_restore": time.monotonic() - started}
        return result
    entries, frontiers, hits = [], [], 0
    mark("structure_fold_and_frontier")
    started = time.monotonic()
    for key in keys:
        entry, frontier, hit = store.read_key(key, set(core), folder / "keys", policy)
        entries.append(entry)
        frontiers.append(frontier)
        hits += hit
    timings = {"fold_and_frontier": time.monotonic() - started}
    started = time.monotonic()
    mark("structure_depth_and_cycles")
    adj = [[identities[target] for target in entry["folded"]] for entry in entries]
    direct_adj = [[identities[target] for target in entry["direct"]] for entry in entries]
    depth, order, reverse = topology(adj)
    direct_depth, _, direct_reverse = topology(direct_adj)
    cycles = cyclic_nodes(adj, reverse)
    failures = {i for i, entry in enumerate(entries) if entry["reason"] is not None}
    missing_depth = reachable(reverse, failures | cycles)
    missing_direct_depth = reachable(direct_reverse, failures | cyclic_nodes(direct_adj, direct_reverse))
    potential = {identities[target] for entry in entries for target in entry["potential"]}
    # Consumers blocked by a cycle have no descendant bitset either. Their
    # other prerequisites must not publish a complete undercount.
    excluded = set(range(len(keys))) - set(order)
    missing_descendants = (set(range(len(keys))) if any(e["unbounded"] for e in entries)
                           else reachable(adj, potential | excluded))
    timings["depth_and_cycles"] = time.monotonic() - started
    started = time.monotonic()
    mark("structure_descendants")
    sizes = descendants(reverse, order, output.parent / "structure-descendants.sqlite")
    timings["descendants"] = time.monotonic() - started
    started = time.monotonic()
    mark("structure_row_emission")
    statuses, reasons, histogram = collections.Counter(), collections.Counter(), collections.Counter()
    positive = empty_positive = frontier_count = 0
    by_id = {key[2]: key for key in keys}
    with output.open("wb") as out:
        for i, (key, entry, frontier) in enumerate(zip(keys, entries, frontiers)):
            row = dict(wire_key(key), owning_module=key[0], generated_candidate=".congr_simp" in
                       display_name(parse_name_key(key[1])), information="undetermined", escape="undetermined")
            reason = "graph_cycle" if i in cycles else entry["reason"]
            if reason:
                row.update(status="unavailable", reason=reason, readings=None)
                statuses["unavailable"] += 1
                reasons[reason] += 1
                out.write(canonical(row))
                continue
            readings = {"direct_frozen_prerequisites": [wire_key(by_id[t]) for t in sorted(entry["direct"], key=lambda t: by_id[t][1:])],
                        "folded_frozen_prerequisites": [wire_key(by_id[t]) for t in sorted(entry["folded"], key=lambda t: by_id[t][1:])],
                        "frozen_dag_depth": None if i in missing_depth else depth[i],
                        "descendant_subgraph_size": None if i in missing_descendants else sizes[i],
                        "axiom_closure": axioms.get((key[1], key[2])),
                        "value_constant_count": entry["value_constant_count"],
                        "core_or_frozen_support": entry["core_or_frozen_support"]}
            missing = sorted(field for field, value in readings.items() if value is None)
            row["status"] = "partial" if missing else "complete"
            if missing:
                row["missing_fields"] = missing
            statuses[row["status"]] += 1
            if readings["frozen_dag_depth"] is not None:
                histogram[str(depth[i])] += 1
            positive += readings["core_or_frozen_support"] is True
            empty_positive += entry["empty_core_support"] is True
            object_prefix(out, row)
            out.write(b',"readings":')
            object_prefix(out, readings)
            out.write(b',"upstream_boundary_constants":[')
            with gzip.open(frontier, "rb") as source:
                frontier_count += jsonl_elements(source, out)
            out.write(b"]}}\n")
    timings["row_emission"] = time.monotonic() - started
    names = collections.Counter(key[1] for key in keys)
    collision_keys = {i for i, key in enumerate(keys) if names[key[1]] > 1}
    result = {"rows": len(keys), "status_counts": {s: statuses[s] for s in ["complete", "partial", "unavailable"]},
              "unavailable_reasons": dict(sorted(reasons.items())), "direct_edges": sum(map(len, direct_adj)),
              "folded_edges": sum(map(len, adj)), "depth_histogram": dict(sorted(histogram.items(), key=lambda p: int(p[0]))),
              "support_positive": positive, "support_undetermined": len(keys) - positive,
              "empty_core_support_positive": empty_positive, "frontier_incidences": frontier_count,
              "direct_depths": {key[2]: None if i in missing_direct_depth else direct_depth[i]
                                for i, key in enumerate(keys)},
              "self_edges": [keys[i][2] for i, targets in enumerate(adj) if i in targets],
              "collisions": {"keys": len(collision_keys), "groups": sum(n > 1 for n in names.values()),
                             "keys_readable": sum(i not in failures for i in collision_keys),
                             "resolved": sum(e["scope_resolved_direct_references"] for e in entries),
                             "ambiguous": sum(e["ambiguous_direct_references"] for e in entries),
                             "ambiguous_rows": [list(keys[i]) for i, e in enumerate(entries) if e["reason"] == "frozen_key_ambiguous"]},
              "cache": {"snapshot_hit": False, "fold_hits": hits, "fold_misses": len(keys) - hits},
              "helper_visits": sum(e["helper_visits"] for e in entries),
              "timings_s": timings, "projection_key": snapshot}
    if cache:
        mark("structure_snapshot_save")
        started = time.monotonic()
        with output.open("rb") as source, gzip.open(rows_cache, "wb", compresslevel=1) as target:
            shutil.copyfileobj(source, target, 1024 * 1024)
        timings["snapshot_save"] = time.monotonic() - started
        atomic_json(summary_cache, result)
    return result

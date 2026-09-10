"""Content addresses and sequential candidate batches. No evidence assessment."""

import os
import pathlib

from streaming import canonical, closure, digest


# Owner ruling #5214, 2026-09-09: policy-override, not capacity-derived.
# Fixed module-count safety bound; remeasure at a toolchain/evidence-domain change.
# The run receipt records both this bound and each actual Environment peak.
BATCH_MODULE_BOUND = 5600
BATCH_KEY_BOUND = 128


def atomic_json(path, value):
    path = pathlib.Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + f".{os.getpid()}.tmp")
    temporary.write_bytes(canonical(value))
    os.replace(temporary, path)


def module_digests(hashes):
    parts = {}
    for module, part, _, hashed in hashes:
        parts.setdefault(module, []).append([part, hashed])
    return {module: values[0][1] if len(values) == 1 else digest(values)
            for module, values in parts.items()}


def extraction_plan(manifest, hashes, cache, source, keys):
    # Ownership is restricted to this run's frozen Name universe. A different
    # universe cannot reuse an absence recorded without inspecting those names.
    namespace = pathlib.Path(cache) / digest([source, keys])[7:]
    addresses = module_digests(hashes)
    paths = {module: namespace / (addresses[module][7:] + ".json") for module, _ in manifest}
    return {"paths": paths, "digests": addresses,
            "misses": [entry for entry in manifest if not paths[entry[0]].is_file()],
            "hits": [module for module, _ in manifest if paths[module].is_file()]}


def save_extraction(plan, module, records):
    atomic_json(plan["paths"][module], records)


def validation_key(key, owner_digest, evidence_digests, toolchain, query_source, scope):
    # scope binds the semantic root (including peer imports), not a batch ID.
    # Batch composition and HEAD cannot alter assess and are not cache inputs.
    return digest([key, owner_digest, evidence_digests, toolchain, query_source, scope])


def candidate_batches(keys, owner_imports, graph, bound=BATCH_MODULE_BOUND):
    grouped = {}
    for key in keys:
        grouped.setdefault(key[0], []).append(key)
    batches = []
    current_keys, imports, modules = [], set(), set()
    current_names = {}
    for owner in sorted(grouped):
        owner_names = {key[1] for key in grouped[owner]}
        required = set(owner_imports[owner])
        scope = set(closure(graph, required))
        if len(scope) > bound:
            raise ValueError(f"IE-C044 candidate batch owner={owner} modules={len(scope)} bound={bound}")
        for start in range(0, len(grouped[owner]), BATCH_KEY_BOUND):
            chunk = grouped[owner][start:start + BATCH_KEY_BOUND]
            # Distinct owners of the same Lean Name must never be reimported
            # together merely because their union fits the module bound.
            name_collision = any(name in current_names and current_names[name] != owner for name in owner_names)
            if current_keys and (name_collision or len(modules | scope) > bound or len(current_keys) + len(chunk) > BATCH_KEY_BOUND):
                batches.append({"keys": current_keys, "imports": sorted(imports), "modules": sorted(modules)})
                current_keys, imports, modules = [], set(), set()
                current_names = {}
            current_names.update((name, owner) for name in owner_names)
            current_keys.extend(chunk)
            imports.update(required)
            modules.update(scope)
    if current_keys:
        batches.append({"keys": current_keys, "imports": sorted(imports), "modules": sorted(modules)})
    return batches

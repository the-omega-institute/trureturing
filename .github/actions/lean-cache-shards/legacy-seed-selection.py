"""Validate the legacy seed and select shards reusable by a different checkout."""

import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path("tools/scripts/worktree").resolve()))
import lean_actions_shards as shards


def select(source, output):
    root = Path.cwd()
    try:
        record = shards.read_index(source, shards.binding(root, "complete"), "complete")
    except shards.IncompatibleShardBinding:
        return False
    if record["owner"]["commit"] != shards.source_commit(root):
        modules = shards.workspace_modules(root)
        hashes = shards.tracked_sources(root, modules)
        graph = shards.project_imports(root, modules)
        # Removed modules, changed sources and their transitive clients miss.
        changed = {name for name, value in hashes.items() if record["sources"].get(name) != value}
        users = {name: [] for name in modules}
        for name, imports in graph.items():
            for dependency in imports:
                users[dependency].append(name)
        todo = list(changed)
        while todo:
            for name in users[todo.pop()]:
                if name not in changed:
                    changed.add(name)
                    todo.append(name)
        valid = modules.keys() - changed
        # A legacy archive can hold several modules. It is installed as a unit.
        # Unowned extras and reports have no per-source provenance across SHAs.
        reusable = {key for key, groups in record["layout"].items()
                    if all(name in valid for group in groups for name in group)}
        for field in ("entries", "fingerprints", "required"):
            record[field] = {key: value for key, value in record[field].items() if key in reusable}
        if not record["required"]:
            return False
    output.write_text(json.dumps(record))
    return True


if __name__ == "__main__":
    operation, path, *args = sys.argv[1:]
    source = Path(path)
    if operation == "validate":
        record = shards.read_index(source, json.loads(source.read_bytes())["binding"], "complete")
        prefix = shards.index_addresses(record["binding"])["snapshot_prefix"]
        print(prefix + record["owner"]["run"] + "-" + record["owner"]["attempt"])
    elif operation == "select":
        sys.exit(0 if select(source, Path(args[0])) else 3)
    else:
        raise ValueError("unknown seed operation")

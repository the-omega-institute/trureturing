"""Assemble the release-only report and its statement material from current Lake facets."""

from pathlib import Path
import stat
import sys
import tempfile
import zipfile


def assemble(root, destination):
    # Import the Inspector from the verified tools release for this source checkout.
    sys.path.insert(0, str(root / "tools/lean-inspector"))
    import materials
    import native
    import publication

    modules = sorted(publication.selection.Selection(root).modules())
    if not modules:
        raise ValueError("the configured report has no modules")
    artifacts = native.state(root) / "modules"
    offsets = {}
    with tempfile.TemporaryFile(dir=destination.parent) as spool:
        with destination.open("xb") as report:
            report.write(b'{"modules": [')
            for index, name in enumerate(modules):
                if index:
                    report.write(b", ")
                native.aggregate_module(name, artifacts / (name + ".zip"), report, spool, offsets)
            report.write(b'], "schema": ' + materials.canonical_json(materials.REPORT_SCHEMA)[:-1] + b'}\n')

        # The writer accepts already-deflated statement bytes and emits the same
        # ZIP metadata as the Inspector. Only the release reader uses this ZIP.
        with zipfile.ZipFile(str(destination) + ".materials.zip", "x") as archive:
            for name, (start, length, crc, size) in sorted(offsets.items()):
                info = zipfile.ZipInfo(name, materials.ARCHIVE_TIMESTAMP)
                info.compress_type = zipfile.ZIP_DEFLATED
                info.create_system = 3
                info.external_attr = (stat.S_IFREG | 0o644) << 16
                info.CRC, info.file_size = crc, size
                spool.seek(start)
                compressed = spool.read(length)
                if len(compressed) != length:
                    raise ValueError("truncated statement material: " + name)
                native.append_compressed(archive, info, compressed)
    print(f"Prepared {len(modules)} modules in {destination.stat().st_size} bytes", flush=True)


if __name__ == "__main__":
    assemble(Path.cwd(), Path(sys.argv[1]))

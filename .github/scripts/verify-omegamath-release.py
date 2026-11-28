"""Install the digest-pinned OmegaMath archive and check the consumer's Lake build."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from urllib.parse import quote
from urllib.request import urlopen


ROOT = Path(__file__).resolve().parents[2]
REPOSITORY = 'the-omega-institute/omegamath'
PUBLIC_TARGETS = ('OmegaInit', 'OmegaMathlib', 'OmegaMath', 'OmegaBuild', 'omegaBackendPlan')


def digest(path):
    with path.open('rb') as archive:
        return 'sha256:' + hashlib.file_digest(archive, 'sha256').hexdigest()


def install_archive(package_root, name, expected):
    lake_dir = package_root / '.lake'
    lake_dir.mkdir(exist_ok=True)
    archive = lake_dir / name
    if not archive.is_file() or digest(archive) != expected:
        # Lake also resolves the release using an exact tag at the pinned commit.
        tag = subprocess.check_output(['git', 'describe', '--tags', '--exact-match', 'HEAD'],
                                      cwd=package_root, text=True).strip()
        url = f'https://github.com/{REPOSITORY}/releases/download/{quote(tag, safe="")}/{quote(name)}'
        with tempfile.TemporaryDirectory(dir=lake_dir) as staging:
            pending = Path(staging) / name
            with urlopen(url, timeout=120) as response, pending.open('wb') as output:
                shutil.copyfileobj(response, output)
            actual = digest(pending)
            if actual != expected:
                raise ValueError(f'OmegaMath asset {name} has digest {actual}, expected {expected}')
            pending.replace(archive)
    # Package.unpack extracts into the package build directory. Reading the published
    # archive directly avoids loading a second copy of the Mathlib workspace.
    build = lake_dir / 'build'
    build.mkdir(exist_ok=True)
    subprocess.run(['tar', '-xzf', archive, '-C', build], check=True)


def verify_release(root):
    manifest = json.loads((root / 'lake-manifest.json').read_text())
    reg_manifest = json.loads((root / 'Reg/lake-manifest.json').read_text())
    receipt = json.loads((root / 'Meta/omegamath-release.json').read_text())
    for lock in (manifest, reg_manifest):
        package, = [item for item in lock['packages'] if item['name'] == 'omegamath']
        if (package['url'].removesuffix('.git') != 'https://github.com/' + REPOSITORY or
                package['rev'] != receipt['source']):
            raise ValueError('OmegaMath release receipt differs from the pinned source in root or Reg')
    if (receipt['toolchain'] != (root / 'lean-toolchain').read_text().strip() or
            receipt['repository'] != REPOSITORY):
        raise ValueError('OmegaMath release receipt differs from the toolchain or repository')

    # Resolve the dependency checkout without running any build targets.
    subprocess.run(['lake', 'env', 'true'], cwd=root, check=True)
    package_root = root / manifest['packagesDir'] / 'omegamath'
    head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=package_root, text=True).strip()
    if head != receipt['source']:
        raise ValueError(f'OmegaMath checkout differs from the lock: {head}')
    name = subprocess.check_output(
        ['lean', '--stdin'], cwd=root, text=True,
        input='import Lake\n#eval IO.println (Lake.defaultBuildArchive `omegamath)\n',
    ).strip()
    if not name or Path(name).name != name:
        raise ValueError(f'Invalid Lake build archive name: {name!r}')
    expected = receipt['assets'][name]
    install_archive(package_root, name, expected)
    print(f'OMEGAMATH_RELEASE {head} {name} {expected}', flush=True)
    subprocess.run(['lake', '--no-cache', '--no-build', 'build',
                    *('@omegamath/' + target for target in PUBLIC_TARGETS)], cwd=root, check=True)


if __name__ == '__main__':
    try:
        verify_release(ROOT)
    except (OSError, KeyError, TypeError, ValueError, subprocess.CalledProcessError) as error:
        sys.exit(f'OMEGAMATH_RELEASE_ERROR {error}')

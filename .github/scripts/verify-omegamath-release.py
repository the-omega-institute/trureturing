"""Install the digest-pinned OmegaMath archive and check the consumer's Lake build."""
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import tomllib
from urllib.parse import quote
from urllib.request import urlopen


ROOT = Path(__file__).resolve().parents[2]
REPOSITORY = 'the-omega-institute/omegamath'
PUBLIC_TARGETS = ('OmegaInit', 'OmegaMathlib', 'OmegaMath', 'OmegaBuild', 'omegaBackendPlan')


def digest(path):
    with path.open('rb') as archive:
        return 'sha256:' + hashlib.file_digest(archive, 'sha256').hexdigest()


def release_url(tag, name):
    return f'https://github.com/{REPOSITORY}/releases/download/{quote(tag, safe="")}/{quote(name)}'


def check_published_receipt(receipt):
    public = dict(receipt)
    tag = public.pop('tag')
    if not re.fullmatch(r'v[0-9]+\.[0-9]+\.[0-9]+(?:-rc\.[1-9][0-9]*)?', tag):
        raise ValueError(f'Invalid OmegaMath release tag: {tag!r}')
    assets = public['assets']
    platforms = (r'omegamath-aarch64-[a-z0-9-]*linux[a-z0-9.-]*\.tar\.gz',
                 r'omegamath-(?:arm64|aarch64)-apple-darwin[a-z0-9.]*\.tar\.gz')
    if (len(assets) != len(platforms) or
            not all(sum(bool(re.fullmatch(platform, name)) for name in assets) == 1 for platform in platforms) or
            not all(re.fullmatch(r'sha256:[a-f0-9]{64}', value) for value in assets.values())):
        raise ValueError('OmegaMath release must pin one SHA-256 for each supported arm64 platform')
    with urlopen(release_url(tag, 'omegamath-release.json'), timeout=120) as response:
        published = json.load(response)
    if public != published:
        raise ValueError(f'OmegaMath receipt differs from the published manifest at {tag}')


def install_archive(package_root, name, expected, tag):
    lake_dir = package_root / '.lake'
    lake_dir.mkdir(exist_ok=True)
    archive = lake_dir / name
    if not archive.is_file() or digest(archive) != expected:
        with tempfile.TemporaryDirectory(dir=lake_dir) as staging:
            pending = Path(staging) / name
            with urlopen(release_url(tag, name), timeout=120) as response, pending.open('wb') as output:
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
    mathlib, = [item for item in manifest['packages'] if item['name'] == 'mathlib']
    reg_mathlib, = [item for item in reg_manifest['packages'] if item['name'] == 'mathlib']
    if mathlib['inherited'] or mathlib['rev'] != reg_mathlib['rev']:
        raise ValueError('trureturing must directly pin the Mathlib revision used by Reg')
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
    product_lock = json.loads((package_root / 'lake-manifest.json').read_text())
    product_config = tomllib.loads((package_root / 'lakefile.toml').read_text())
    if (any(item['name'] == 'mathlib' for item in product_config.get('require', [])) or
            any(item['name'] == 'mathlib' for item in product_lock['packages'])):
        raise ValueError('OmegaMath release includes Mathlib in its product dependencies')
    name = subprocess.check_output(
        ['lean', '--stdin'], cwd=root, text=True,
        input='import Lake\n#eval IO.println (Lake.defaultBuildArchive `omegamath)\n',
    ).strip()
    if not name or Path(name).name != name:
        raise ValueError(f'Invalid Lake build archive name: {name!r}')
    check_published_receipt(receipt)
    expected = receipt['assets'][name]
    install_archive(package_root, name, expected, receipt['tag'])
    print(f'OMEGAMATH_RELEASE {head} {name} {expected}', flush=True)
    subprocess.run(['lake', '--no-cache', '--no-build', 'build',
                    *('@omegamath/' + target for target in PUBLIC_TARGETS)], cwd=root, check=True)


if __name__ == '__main__':
    try:
        verify_release(ROOT)
    except (OSError, KeyError, TypeError, ValueError, subprocess.CalledProcessError) as error:
        sys.exit(f'OMEGAMATH_RELEASE_ERROR {error}')

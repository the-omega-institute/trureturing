"""Native fixture run under lean-cache-run.sh by the declared-template tests.

The caller owns the canonical cache for the entire prerequisite/copy/compile
operation, including the shared pinned packages used by the private fixture.
"""
import hashlib
import json
import os
from pathlib import Path
import shutil
import sys

from test_native_support import NativeTestSupport, ROOT


class InstanceSupportFixture(NativeTestSupport):
    def produce(self, output):
        self.root = output
        self.env = dict(os.environ)
        self._commands = []

        def run(args, cwd=output):
            result = self.guarded_command(args, cwd=cwd, env=self.env)
            if result.returncode:
                raise RuntimeError(f'{args}: exit {result.returncode}\n{result.stdout}{result.stderr}')
            return result.stdout

        lake = run(['elan', 'which', 'lake'], ROOT).strip()
        # The enclosing canonical cache owner remains live through copying and
        # native execution. Do not release/reacquire it between these steps.
        run([lake, '-d', str(ROOT / 'tools/lean-inspector'), 'build', 'reportInspector'], ROOT)
        run([lake, '-d', str(ROOT / 'Reg'), 'build', 'Reg.Support.DependentFamily'], ROOT)
        # Reuse only the compiler-reported local import closure of the checked
        # roots. Every copied input retains its logical source path and native
        # trace; subsequent Lake and producer checks validate the private copy.
        bases = ['.lake/build/lib/lean', '.lake/build/reg/lib/lean',
                 '.lake/build/lean-inspector/producer/lib/lean',
                 '.lake/build/lean-inspector/interface/lib/lean']
        pending = ['Reg.Support.DependentFamily', 'LeanInformationAudit.Registry']
        seen = set()
        while pending:
            module = pending.pop()
            if module in seen:
                continue
            seen.add(module)
            if not module.startswith(('D5.', 'Reg.', 'LeanInformationAudit.', 'LeanInformationAuditInterface.')):
                continue
            relative = module.replace('.', '/')
            matches = [ROOT / base / (relative + '.ilean') for base in bases
                       if (ROOT / base / (relative + '.ilean')).is_file()]
            if len(matches) != 1:
                raise ValueError('missing or ambiguous compiled fixture dependency: ' + module)
            ilean = matches[0]
            pending.extend(row[0] for row in json.loads(ilean.read_text())['directImports'])
            for source in ilean.parent.glob(ilean.stem + '.*'):
                if source.is_file():
                    target = output / source.relative_to(ROOT)
                    target.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copyfile(source, target)
            ir = Path(str(ilean).replace('/lib/lean/', '/ir/')).with_suffix('.c')
            for source in ir.parent.glob(ir.stem + '.*'):
                if source.is_file():
                    target = output / source.relative_to(ROOT)
                    target.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copyfile(source, target)
            prefix = ('tools/lean-inspector-interface/' if module.startswith('LeanInformationAuditInterface.')
                      else 'tools/lean-inspector/' if module.startswith('LeanInformationAudit.') else '')
            source = prefix + relative + '.lean'
            target = output / source
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / source, target)
        for name in ('lean-toolchain', 'lean-report-inputs.json', 'lakefile.toml', 'lake-manifest.json',
                     'Reg/lakefile.toml', 'Reg/lake-manifest.json',
                     'tools/lean-inspector/lakefile.lean', 'tools/lean-inspector/lake-manifest.json',
                     'tools/lean-inspector-interface/lakefile.toml',
                     'tools/lean-inspector-interface/lake-manifest.json', 'tools/lean-inspector/materials.py'):
            target = output / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / name, target)
        (output / '.lake/packages').symlink_to(ROOT / '.lake/packages', target_is_directory=True)
        fixture = (ROOT / 'tools/lean-inspector/LeanInformationAuditRegTests/InstanceSupportNative.lean').read_text()
        modules = [('source', 'D5.InstanceSupportFixture'), ('registration', 'Reg.D5.InstanceSupportFixture')]
        for key, module in modules:
            marker = 'def ' + key + ' : String := r####"'
            if fixture.count(marker) != 1:
                raise ValueError('invalid native fixture source marker')
            source = fixture.split(marker, 1)[1].split('"####', 1)[0]
            target = output / (module.replace('.', '/') + '.lean')
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(source)
        run([lake, '-d', str(output / 'Reg'), 'build', '+D5.InstanceSupportFixture', '+Reg.D5.InstanceSupportFixture'])
        (output / 'utility.json').write_text('[]')
        request = ['--output', str(output / 'spool.json'), '--material-spool', str(output / 'spool'),
                   '--utility-input', str(output / 'utility.json')]
        for _, module in modules:
            source = module.replace('.', '/') + '.lean'
            request.extend([module, source, 'sha256:' + hashlib.sha256((output / source).read_bytes()).hexdigest()])
        (output / 'request.json').write_text(json.dumps(request))
        inspector = ROOT / '.lake/build/lean-inspector/producer/bin/reportInspector'
        run([lake, '-d', str(output / 'Reg'), 'env', str(inspector), '--request-file', str(output / 'request.json')])
        run(['python3', str(ROOT / 'tools/lean-inspector/materials.py'), 'compact',
             str(output / 'spool.json'), str(output / 'spool'), str(output / 'raw-lean-report.json'),
             str(output / 'lean-report-inputs.json')])
        self._testMethodName = 'instance_support'
        sources = output / 'sources'
        for _, module in modules:
            path = module.replace('.', '/') + '.lean'
            target = sources / path
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(output / path, target)

        self.record_result('native', dict(modules=[module for _, module in modules], release=16),
            [output / 'raw-lean-report.json', output / 'raw-lean-report.json.materials.zip',
             output / 'lean-report-inputs.json', *sources.rglob('*.lean')])


if __name__ == '__main__':
    fixture = InstanceSupportFixture()
    try:
        fixture.produce(Path(sys.argv[1]).resolve())
    finally:
        for command in getattr(fixture, '_commands', []):
            fixture.join_command(command)

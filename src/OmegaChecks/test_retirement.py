"""Regression tests for protected selection and same-name statement substitution."""
import json
import os
import subprocess
import tempfile
import unittest
from pathlib import Path

from retirement import ROOT, affected_modules, lean_path, reconcile, transferred_freezes


class RetirementTest(unittest.TestCase):
    def test_transitive_original_consumers_and_dropped_import(self):
        old = {'OmegaMath.Original': set(), 'D5.First': {'OmegaMath.Original'},
               'Reg.Last': {'D5.First'}, 'D5.Unrelated': {'Mathlib'}}
        changed = {**old, 'D5.First': {'Mathlib'}}
        self.assertEqual(affected_modules(old), (['OmegaMath.Original'], ['D5.First', 'Reg.Last']))
        self.assertEqual(affected_modules(changed), (['OmegaMath.Original'], []))

    def test_frozen_key_and_missing_compiled_comparison(self):
        old = dict(module='D5.A', declarations=[dict(nameKey='a', kind='theorem',
                   includeInStatement=True, statementTypeAddress='protected-address')])
        inventory = dict(providers=[], consumers=['D5.A'], frozen={'D5.A': {
            'declarations': [dict(declaration_name_key='a', kind='theorem')]}})
        self.assertIn('obligation', reconcile(inventory, [old], [])[0])
        with self.assertRaisesRegex(ValueError, 'does not cover'):
            reconcile(inventory, [], [])
        old['declarations'].clear()
        with self.assertRaisesRegex(ValueError, 'protected frozen declaration missing'):
            reconcile(inventory, [old], [])

    def test_compiled_owner_move_and_hypothesis_substitution(self):
        with tempfile.TemporaryDirectory() as temp:
            tmp = Path(temp)
            modules = {}
            for name, original in [('Old', True), ('New', False)]:
                d = tmp / name
                d.mkdir()
                module = d / (name + '.lean')
                text = ('private def helper (n : Nat) := n + 1\n'
                        'def stable (n : Nat) := helper n\n'
                        'def localProperty (n : Nat) := n = n\n'
                        'theorem selected (n : Nat) (hp : PROPERTY) : n = n := rfl\n')
                module.write_text(text.replace('PROPERTY', 'n = n' if original else 'localProperty n'))
                subprocess.run(['lean', '-R', str(d), '-o', module.with_suffix('.olean'), module],
                               cwd=ROOT, check=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                modules[name] = str(d)
            request = tmp / 'request.json'
            output = tmp / 'output.json'
            request.write_text(json.dumps(dict(protectedPath=modules['Old'], candidatePath=modules['New'],
                                               protectedModules=['Old'], candidateModules=['New'], standardUses=False)))
            subprocess.run(['lake', 'env', 'lean', '--run', 'src/OmegaChecks/RetiredDeclarations.lean',
                            request, output], cwd=ROOT, check=True)
            rows = {row['name']: row for row in json.loads(output.read_text())}
            self.assertEqual(rows['stable']['comparison'], 'checked compiled declaration')
            self.assertEqual(rows['stable']['candidateModule'], 'New')
            self.assertIn('compiled type changed', rows['selected']['obligation'])

    def test_transferred_keys_must_be_frozen(self):
        rows = [dict(module='OmegaMath.X', nameKey='old', candidateModule='D5.New', candidateKey='new',
                     kind='theorem', comparison='checked compiled declaration')]
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / 'D5').mkdir()
            (root / 'D5/New.lean.json').write_text(json.dumps({'declarations': [
                {'declaration_name_key': 'wrong', 'kind': 'theorem'}]}))
            transferred_freezes(rows, {'OmegaMath.X'}, root)
            self.assertIn('missing from canonical freeze', rows[0]['obligation'])

    def test_substitution_of_accepted_upstream_occurrences(self):
        with tempfile.TemporaryDirectory() as d:
            temp = Path(d)
            package_path = lean_path(ROOT, False)
            req, out = temp / 'request.json', temp / 'result.json'
            for name, substituted in [('old', False), ('new', True)]:
                folder = temp / name
                folder.mkdir()
                source = folder / 'Client.lean'
                text = ('import Mathlib.Data.Nat.Prime.Defs\nimport Mathlib.Data.Nat.Fib.Basic\n'
                        'namespace Client\n'
                        'def localPrime := Nat.Prime\ndef localFib := Nat.fib\n'
                        'theorem primeUse (p : Nat) (hp : PRIME p) : p = p := rfl\n'
                        'theorem fibUse (p : Nat) : FIB p = FIB p := rfl\n'
                        'theorem renameBinder (BINDER : Nat) : Nat.fib BINDER = Nat.fib BINDER := rfl\nend Client\n')
                source.write_text(text.replace('PRIME', 'localPrime' if substituted else 'Nat.Prime')
                                  .replace('FIB', 'localFib' if substituted else 'Nat.fib')
                                  .replace('BINDER', 'm' if substituted else 'n'))
                subprocess.run(['lean', '-R', folder, '-o', source.with_suffix('.olean'), source],
                               env={**os.environ, 'LEAN_PATH': package_path}, cwd=ROOT, check=True)
            req.write_text(json.dumps(dict(protectedPath=str(temp / 'old') + os.pathsep + package_path,
                                           candidatePath=str(temp / 'new') + os.pathsep + package_path,
                                           protectedModules=['Client'], candidateModules=['Client'],
                                           standardUses=True)))
            subprocess.run(['lake', 'env', 'lean', '--run', 'src/OmegaChecks/RetiredDeclarations.lean', req, out],
                           cwd=ROOT, check=True)
            failed = json.loads(out.read_text())
            self.assertEqual({r['name'] for r in failed}, {'Client.fibUse', 'Client.primeUse'})
            self.assertEqual({r['expected'] for r in failed}, {'Nat.Prime', 'Nat.fib'})
            self.assertEqual({r['actualOwner'] for r in failed}, {'Client'})


if __name__ == '__main__':
    unittest.main()

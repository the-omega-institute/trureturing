"""Behavioral contracts for the foreground actual-prime inquiry (no GPU)."""
import copy
from fractions import Fraction as F
import importlib
import itertools
import json
import math
import re
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import sys
import subprocess
import time

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
try:
    from prime_slabs import cpu, cpu_store
except ImportError:
    cpu = cpu_store = None


PRODUCER=cpu.digest({'synthetic':True}) if cpu else ''
NEW_PRODUCER=cpu.digest({'synthetic':True,'version':2}) if cpu else ''

class CpuContracts(unittest.TestCase):
    def setUp(self):
        self.assertIsNotNone(cpu, 'foreground CPU arithmetic module is required')
        self.assertIsNotNone(cpu_store, 'scoped per-key resume store is required')
        self.tmp = tempfile.TemporaryDirectory(prefix='actual prime cpu tests ')
        self.addCleanup(self.tmp.cleanup)

    def store(self):
        s = cpu_store.Store(Path(self.tmp.name) / 'results.sqlite3', cpu.EXPERIMENT)
        s.add_producer(PRODUCER,{'synthetic':True})
        s.add_producer(NEW_PRODUCER,{'synthetic':True,'version':2})
        self.addCleanup(s.close)
        return s

    def node(self):
        # Exact-input fixture only: tests never evaluate a selected arithmetic node.
        return cpu.make_box(((2, 5), (3, 5), (23, 0)))['nodes'][0]

    def fake(self, signs, calls):
        def evaluate(node, precision):
            calls.append(precision)
            sign = signs[len(calls)-1]
            return dict(precision=precision, outcome=sign,domain_enclosed=True,
                        bounds={'G': {'negative':['-2','-1'], 'positive':['1','2'],
                                      'nonpositive':['-1','0'], 'nonnegative':['0','1'],
                                      'unresolved':['-1','1']}[sign]})
        return evaluate

    def test_permutations_preserve_paired_zero_exponents_and_witness_coordinates(self):
        pairs = ((2, 5), (3, 5), (23, 0))
        expected = cpu.make_box(pairs)
        for permutation in itertools.permutations(pairs):
            self.assertEqual(expected, cpu.make_box(permutation))
        key = cpu.canonical_key(pairs, F(6, 4), F(10, 2))
        self.assertEqual(key, cpu.canonical_key(tuple(reversed(pairs)), F(3, 2), F(5)))
        self.assertNotEqual(key, cpu.canonical_key(((2, 5), (3, 0), (23, 5)), F(3, 2), F(5)))
        self.assertEqual([[2,5],[3,5],[23,0]], self.node()['input']['coordinates'])
        for node in expected['nodes']:
            a, b = node['exact']['two_configurations']
            self.assertNotEqual(a, b)
            for exponents in (a, b):
                product = math.prod(p**e for (p,_),e in zip(pairs,exponents))
                self.assertLessEqual(F(node['exact']['exp_T0']), product)
                self.assertLessEqual(product, F(node['exact']['exp_T1']))

    def test_actual_corners_use_unbounded_integers_and_the_M_shift(self):
        pairs = ((2,15),(3,15),(31,15))
        box = cpu.make_box(pairs)
        base = (2*3*31)**15
        self.assertEqual([base*x for x in (1,2,3,6,31,62,93,186)],
                         [c['product'] for c in box['corners']])
        self.assertGreater(box['corners'][-1]['product'], 2**64)
        for node in box['nodes']:
            self.assertEqual(F(node['exact']['exp_T0'])*186, F(node['input']['exp_M0']))
            self.assertEqual(F(node['exact']['exp_T1'])*186, F(node['input']['exp_M1']))
            self.assertEqual([2**16,3**16,31**16], node['exact']['C'])
            self.assertEqual([2**17,3**17,31**17], node['exact']['D'])

    def test_every_guard_is_strict_including_cutoff_and_reflection_boundaries(self):
        self.assertEqual(0, cpu.guard_bits(5040))
        self.assertEqual(1, cpu.guard_bits(5041))
        args = [5041, 10, 11, 122, 121, 123]
        self.assertEqual(31, cpu.guard_bits(*args))
        for index,value,bit in [(0,5040,0),(1,11,1),(3,121,2),
                                (4,122,3),(5,122,4)]:
            changed = args.copy(); changed[index] = value
            self.assertFalse(cpu.guard_bits(*changed) & (1 << bit))
        box = cpu.make_box(((2,0),(3,0),(23,0)))
        self.assertEqual(25, len(box['slots']))
        self.assertEqual([],box['nodes'])
        # Exact labels are checked; negative exponents and composites are invalid.
        for pairs in [((2,-1),(3,0),(23,0)),((2,0),(2,1),(23,0)),
                      ((2,0),(3,0),(25,0)),((True,0),(3,0),(23,0))]:
            with self.assertRaises(ValueError): cpu.make_box(pairs)

    def test_reflection_has_nonintegral_budget_and_exact_tie(self):
        # Enumerating guards is not a G evaluation. This fixed fixture is in the domain.
        box = cpu.make_box(((2,4),(3,5),(23,0)))
        reflected = [n for n in box['nodes'] if n['origin']['kind']=='reflection']
        self.assertTrue(reflected)
        from prime_slabs.certify import distance_ratio
        for node in reflected:
            self.assertGreater(F(node['exact']['exp_T1']).denominator, 1)
            i = node['origin']['i']; exact = node['exact']; inp = node['input']
            self.assertEqual(F(inp['exp_M0'])*F(inp['exp_M1']),
                             F((exact['C'][i]*exact['D'][i])**3))
            self.assertTrue(distance_ratio(F(inp['exp_M0']),F(inp['exp_M1']),
                                           exact['C'][i],exact['D'][i])[1])

    def test_completed_signs_skip_and_positive_routes_without_rediscovery(self):
        for sign in ('negative','positive','nonpositive','nonnegative'):
            with self.subTest(sign=sign):
                path = Path(self.tmp.name) / (sign+'.sqlite3')
                with cpu_store.Store(path,cpu.EXPERIMENT) as store:
                    store.add_producer(PRODUCER,{'synthetic':True})
                    store.add_producer(NEW_PRODUCER,{'synthetic':True,'version':2})
                    calls=[]; node=self.node()
                    store.register_node(node)
                    result=store.evaluate_node(node,'pilot',self.fake([sign],calls),PRODUCER,
                                               lambda: 1000, lambda: 1_000_000)
                    self.assertEqual(sign,result['sign'])
                    result=store.evaluate_node(node,'pilot',self.fake([],calls),NEW_PRODUCER,
                                               lambda: 1000, lambda: 1_000_000)
                    self.assertEqual([128],calls)
                    self.assertEqual(sign=='positive', result['status']=='candidate')

    def test_resume_uses_only_uncompleted_tiers_and_retains_512_residual(self):
        store=self.store(); node=self.node();store.register_node(node)
        calls=[]; ticks=iter([0,10,20,30,40,50])
        remaining=iter([1000,0])
        store.evaluate_node(node,'pilot',self.fake(['unresolved'],calls),PRODUCER,
                            lambda: next(remaining), lambda: next(ticks))
        self.assertEqual([128],calls)
        calls=[]
        result=store.evaluate_node(node,'pilot',self.fake(['unresolved','unresolved'],calls),
                                   PRODUCER,lambda:1000,lambda:next(ticks))
        self.assertEqual([256,512],calls)
        self.assertEqual('residual',result['status'])
        self.assertEqual(30,store.spent_ns('pilot'))
        self.assertEqual([128,256,512],[t['precision'] for t in result['tiers']])
        store.evaluate_node(node,'pilot',self.fake([],calls),PRODUCER,lambda:1000,lambda:0)
        self.assertEqual([256,512],calls)

    def test_interrupted_tier_retains_cost_and_resumes_same_uncompleted_tier(self):
        store=self.store();node=self.node();store.register_node(node)
        ticks=iter([100,150])
        def interrupted(n,p): raise KeyboardInterrupt()
        with self.assertRaises(KeyboardInterrupt):
            store.evaluate_node(node,'pilot',interrupted,PRODUCER,lambda:1000,lambda:next(ticks))
        self.assertEqual(50,store.spent_ns('pilot'))
        prior=store.read_node(node['key'])
        self.assertEqual([],prior['tiers'])
        self.assertEqual(128,prior['interruptions'][0]['precision'])
        store.close()
        with cpu_store.Store(Path(self.tmp.name)/'results.sqlite3',cpu.EXPERIMENT) as reopened:
            calls=[]
            reopened.evaluate_node(node,'pilot',self.fake(['negative'],calls),PRODUCER,
                                   lambda:1000,lambda:0)
            self.assertEqual([128],calls)
            self.assertEqual(50,reopened.spent_ns('pilot'))

    def test_cumulative_cap_is_not_reset_on_reopen(self):
        store=self.store();node=self.node();store.register_node(node)
        ticks=iter([0,600_000_000_000])
        calls=[]
        store.evaluate_node(node,'pilot',self.fake(['unresolved'],calls),PRODUCER,
                            lambda: max(0,600_000_000_000-store.spent_ns('pilot')),
                            lambda:next(ticks))
        store.close()
        with cpu_store.Store(Path(self.tmp.name)/'results.sqlite3',cpu.EXPERIMENT) as reopened:
            reopened.evaluate_node(node,'pilot',self.fake([],calls),PRODUCER,
                                   lambda:max(0,600_000_000_000-reopened.spent_ns('pilot')),lambda:0)
            self.assertEqual([128],calls)
            self.assertEqual(600_000_000_000,reopened.spent_ns('pilot'))

    def test_matching_unbound_invalid_and_conflicting_units_fail_before_evaluation(self):
        store=self.store();node=self.node();store.register_node(node)
        altered=copy.deepcopy(node);altered['exact']['C'][0]+=1
        with self.assertRaisesRegex(cpu_store.InputGap,node['key']): store.register_node(altered)
        record=store.read_node(node['key']);record['status']='invalid'
        store.replace_record(node['key'],record)
        with self.assertRaisesRegex(cpu_store.InputGap,'invalid'):
            store.evaluate_node(node,'pilot',self.fake([],[]),PRODUCER,lambda:1000,lambda:0)
        record['status']='pending';record['definition']='unknown'
        store.replace_record(node['key'],record)
        with self.assertRaisesRegex(cpu_store.InputGap,'definition'):
            store.evaluate_node(node,'pilot',self.fake([],[]),PRODUCER,lambda:1000,lambda:0)

    def test_support_exclusion_precedes_decoding(self):
        known=[{'primes':[5,7,11]},{'primes':[2,3,5]}]
        self.assertEqual([],cpu.matching_supports(((2,0),(3,0),(23,0)),known))
        match={'primes':[23,3,2]}
        self.assertEqual([match],cpu.matching_supports(((2,0),(3,0),(23,0)),known+[match]))

    def test_pilot_and_window_declared_order(self):
        pilot=list(cpu.boxes('pilot'))
        self.assertEqual(64,len(pilot))
        self.assertEqual(((2,0),(3,0),(23,0)),pilot[0])
        self.assertEqual(((2,0),(3,0),(23,5)),pilot[1])
        self.assertEqual(((2,15),(3,15),(23,15)),pilot[-1])
        window=list(cpu.boxes('window'))
        self.assertEqual(12288,len(window))
        self.assertEqual(((2,0),(3,0),(29,0)),window[4096])
        self.assertEqual(((2,15),(3,15),(31,15)),window[-1])

    def test_tampered_guard_and_configuration_fail_before_evaluation(self):
        store=self.store();node=self.node();store.register_node(node)
        for field in ('guard','configuration'):
            record=store.read_node(node['key'])
            original=copy.deepcopy(record)
            if field=='guard': record['exact']['guards']['cutoff']=0
            else: record['exact']['two_configurations'][0][0]=-1
            store.replace_record(node['key'],record)
            with self.assertRaisesRegex(cpu_store.InputGap,'retained witness/guard'):
                store.evaluate_node(node,'pilot',self.fake([],[]),PRODUCER,lambda:1000,lambda:0)
            store.replace_record(node['key'],original)

    def test_three_row_Arb_interface_on_symmetric_synthetic_endpoints(self):
        # Synthetic analytic equality; not an actual-prime box or selected search key.
        from prime_slabs import certify
        from flint import ctx
        with ctx.workprec(128):
            for upper,weight in ((8,0),(64,1)):
                result=certify.evaluate([2,2,2],[4,4,4],8,upper)
                lo,hi=map(F,certify.enclosure(result['G']))
                self.assertLessEqual(lo,0);self.assertGreaterEqual(hi,0)
                self.assertEqual(6,len(result['mixtures']))
                self.assertTrue(all(x==weight for row in result['weights'] for x in row))
                self.assertEqual([0,1,2] if upper==64 else [],result['nearest_ties'])

    def test_command_is_portable_and_requires_explicit_inputs(self):
        command=Path(__file__).resolve().parents[1]/'prime_slab_cpu.py'
        help_result=subprocess.run([sys.executable,'-B',str(command),'--help'],
            cwd=self.tmp.name,capture_output=True,text=True)
        self.assertEqual(0,help_result.returncode,help_result.stderr)
        missing=subprocess.run([sys.executable,'-B',str(command)],cwd=self.tmp.name,
                               capture_output=True,text=True)
        self.assertEqual(2,missing.returncode)
        self.assertIn('--input',missing.stderr)

    def test_driver_bounded_boxes_resumes_and_routes_candidate_without_evaluation(self):
        import prime_slab_cpu as driver
        store=self.store();calls=[]
        class Limits:
            def reason(self): return None
            def remaining_ns(self): return 1000
            def evaluate(self,node,precision):
                calls.append(node['key'])
                return dict(precision=precision,outcome='negative',domain_enclosed=True,bounds={'G':['-2','-1']})
        first=driver.execute(store,'pilot',1,Limits(),PRODUCER)
        self.assertEqual('batch-box-limit',first['reason'])
        self.assertEqual(1,store.summary()['boxes_enumerated'])
        self.assertEqual([],calls)
        second=driver.execute(store,'pilot',1,Limits(),PRODUCER)
        self.assertEqual(1,second['boxes_skipped'])
        self.assertEqual(2,store.summary()['boxes_enumerated'])
        self.assertTrue(calls)
        done=len(calls)
        # Reopening a completed exact key must remain a no-evaluation operation.
        with self.assertRaisesRegex(cpu_store.InputGap,'completed pilot'):
            driver.execute(store,'window',1,Limits(),PRODUCER)
        key=calls[-1];record=store.read_node(key)
        record['tiers'][-1].update(outcome='positive',bounds={'G':['1','2']})
        record.update(status='candidate',sign='positive');store.replace_record(key,record)
        third=driver.execute(store,'pilot',1,Limits(),PRODUCER)
        self.assertEqual('candidate-needs-independent-certification',third['reason'])
        self.assertEqual([key],third['candidates']);self.assertEqual(done,len(calls))

    def test_support_binding_failure_precedes_any_legacy_node_decode(self):
        import prime_slab_cpu as driver
        root=Path(self.tmp.name);bindings=[]
        for path in ('docs/develop/theory/ARITHMETIC_BOUNDARY_QUANTIZATION.md',driver.PROGRAMS[-1]):
            target=root/path;target.parent.mkdir(parents=True,exist_ok=True);target.write_text('fixture')
            bindings.append(dict(path=path,sha256=driver.sha(target)))
        manifest=dict(experiment=cpu.EXPERIMENT,source_bindings=bindings,
                      retained_supports=[dict(primes=[5,7,11],support_complete=True)])
        path=root/'explicit input.json';path.write_text(cpu.dumps(manifest))
        self.assertEqual(manifest,driver.bind_inputs(path,driver.sha(path),root))
        manifest['retained_supports'].append(dict(primes=[23,2,3],record='named-record',support_complete=True))
        path.write_text(cpu.dumps(manifest))
        with self.assertRaisesRegex(cpu_store.InputGap,'named-record'):
            driver.bind_inputs(path,driver.sha(path),root)
        with self.assertRaisesRegex(cpu_store.InputGap,'SHA-256'):
            driver.bind_inputs(path,'0'*64,root)

    def test_dataset_hashing_streams_instead_of_allocating_the_whole_database(self):
        import prime_slab_cpu as driver
        path=Path(self.tmp.name)/'data';path.write_bytes(b'abc')
        with patch.object(Path,'read_bytes',side_effect=AssertionError('unbounded database read')):
            self.assertEqual('ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad',
                             driver.sha(path))

    def test_retained_producer_digest_binds_content_before_skip(self):
        store=self.store();node=self.node();store.register_node(node)
        store.evaluate_node(node,'pilot',self.fake(['negative'],[]),PRODUCER,lambda:1000,lambda:0)
        with store.connection:
            store.connection.execute('UPDATE producers SET document=? WHERE id=?',('{}',PRODUCER))
        with self.assertRaisesRegex(cpu_store.InputGap,'producer content'):
            store.evaluate_node(node,'pilot',self.fake([],[]),PRODUCER,lambda:1000,lambda:0)

    def test_missing_cost_cannot_reset_cumulative_allowance(self):
        store=self.store();node=self.node();store.register_node(node);ticks=iter((0,50))
        store.evaluate_node(node,'pilot',self.fake(['negative'],[]),PRODUCER,lambda:1000,lambda:next(ticks))
        with store.connection: store.connection.execute("DELETE FROM costs WHERE phase='pilot'")
        store.close()
        with self.assertRaisesRegex(cpu_store.InputGap,'expenditure'):
            with cpu_store.Store(Path(self.tmp.name)/'results.sqlite3',cpu.EXPERIMENT): pass

    def test_completed_sign_requires_the_recorded_positive_domain(self):
        store=self.store();node=self.node();store.register_node(node)
        store.evaluate_node(node,'pilot',self.fake(['negative'],[]),PRODUCER,lambda:1000,lambda:0)
        record=store.read_node(node['key']);record['tiers'][0]['domain_enclosed']=False
        store.replace_record(node['key'],record)
        with self.assertRaisesRegex(cpu_store.InputGap,'domain'):
            store.evaluate_node(node,'pilot',self.fake([],[]),PRODUCER,lambda:1000,lambda:0)


if __name__ == '__main__':
    name='test_every_guard_is_strict_including_cutoff_and_reflection_boundaries'
    if '--mutant-guard' in sys.argv:
        sys.argv.remove('--mutant-guard')
        source=Path(cpu.__file__).read_text().replace('R>5040','R>=5040')
        namespace={'__name__':'prime_slabs.cpu_guard_mutant'}
        exec(compile(source,'<cpu strict-cutoff mutation>','exec'),namespace)
        cpu.guard_bits=namespace['guard_bits']
        print('mutation_compile_errors=0',flush=True)
        unittest.main(verbosity=2)
    elif '--mutation-check' in sys.argv:
        expected=[name]
        print(cpu.dumps(dict(mutation='cpu.guard_bits strict5040: > becomes >=',
                             expected_red=expected,expected_count=1)),flush=True)
        command=[sys.executable,'-B',str(Path(__file__).resolve())]
        red=subprocess.run(command+['--mutant-guard','CpuContracts.'+name],
                           capture_output=True,text=True)
        actual=re.findall(r'^FAIL: (\w+)',red.stderr,re.MULTILINE)
        restored=subprocess.run(command+['CpuContracts.'+name],capture_output=True,text=True)
        valid=(red.returncode==1 and actual==expected and
               'mutation_compile_errors=0' in red.stdout and restored.returncode==0)
        print(cpu.dumps(dict(mutation_exit=red.returncode,compile_errors=0 if
            'mutation_compile_errors=0' in red.stdout else None,
            actual_red=actual,restored_exit=restored.returncode,
            restoration='Mutation existed only in the joined child process; source unchanged.')))
        for failed in actual: print('[FAIL] '+failed+' (expected mutation detection)')
        sys.exit(0 if valid else 1)
    else:
        unittest.main(verbosity=2)

"""Bounded scientific contracts; synthesized rows are fixtures, never search input."""

import copy
from fractions import Fraction as F
import hashlib
import itertools
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
from types import SimpleNamespace
from contextlib import redirect_stdout
import io
import os
import subprocess
import sys
import uuid

from flint import arb, ctx
from prime_slabs import exact, certify, storage
import prime_slab_search as runner


def constant_fixture():
    rows = []
    for t, primes in enumerate(itertools.combinations(exact.PRIMES, 3)):
        products = {m: __import__('math').prod(p for i, p in enumerate(primes)
                                             if m >> i & 1) for m in range(8)}
        masks = sorted(products, key=products.get)
        rows.append(dict(triple_index=t, primes=list(primes), sorted_masks=masks,
                         subset_products=[products[m] for m in masks]))
    return rows


def raw_fixture(row_id=76801, bits=1, active=1, error=0, proposal=-1.0):
    # A literal, GPU-shaped test fixture: (2,3,5), b=(12,0,0), adjacent slot 1.
    return {'integers': [row_id, 3072, 1, 0, 12, 0, 0, 2, 3, 5,
                         1, 2, -1, 2, -1, bits, active, error],
            'floats': [float(0).hex()]*6 + [proposal.hex(), float(0).hex()] +
                      [proposal.hex()]*6}


def transport_fixture():
    # One synthetic device transcript, not a production candidate source.
    masks=[0,1,2,4,3,5,6,7]
    rows=[]
    for slot in range(25):
        j,i=(slot+1,-1) if slot<7 else (1+(slot-7)//3,(slot-7)%3)
        bits=(0 if slot==0 else 1) if i<0 else ([12,18,18] if j==1 else [13,19,19])[i]
        row=raw_fixture()
        row['integers']=[76800+slot,3072,slot,0,12,0,0,2,3,5,masks[j-1],masks[j],
                         -1 if i<0 else masks[j+1],j,i,bits,int(i<0 and slot>0),0]
        rows.append(row)
    return rows


def verification_fixture(directory):
    """Fixed synthetic verification state; never relabel a historical checkpoint."""
    directory=Path(directory).resolve()
    source=directory/'input.json'
    storage.state_store.atomic_json(source,dict(
        schema_version=1,kind='constant-prime-corner-order-input',
        primes=list(exact.PRIMES),rows=constant_fixture(),triple_order='lexicographic',
        mask_convention='bit i increments prime i',search_executed=False,
        exponent_boxes_generated=0))
    args=SimpleNamespace(command='verify',first_box=3072,last_box=3072,chunk_boxes=1,
                         max_chunks=0,precisions='128,256',state_dir=str(directory/'run'),
                         input=source,input_sha256=storage.state_store.file_hash(source))
    identity=runner.identities(args.input_sha256,(128,256))
    with storage.state_store.StateLocks(args.state_dir):
        store=storage.WindowStore(Path(args.state_dir)/'window-3072-3072',identity,3072,3072)
        store.initialize()
        rows=transport_fixture()
        raw=store.write_raw(3072,3072,rows,dict(synthetic=True,gpu_dispatches=0,
                                              purpose='summary-publication-regression'))
        records=runner.verify_rows(rows,constant_fixture(),(128,256))
        store.commit_chunk(3072,3072,records,storage.state_store.file_hash(raw))
    return args


class ExactContracts(unittest.TestCase):
    def test_unavailable_mps_cannot_use_cpu_fallback(self):
        fake=SimpleNamespace(__version__='2.8.0',
                             backends=SimpleNamespace(mps=SimpleNamespace(is_built=lambda:True,
                                                                          is_available=lambda:False)))
        with patch.dict(sys.modules,{'torch':fake}), patch.dict(os.environ,{'PYTORCH_ENABLE_MPS_FALLBACK':'1'}):
            with self.assertRaisesRegex(ValueError,'CPU fallback prohibited'):
                runner.MpsRunner(constant_fixture(),lambda *a:self.fail('compiled without MPS'))
            self.assertEqual('0',os.environ['PYTORCH_ENABLE_MPS_FALLBACK'])

    def test_cutoff_and_all_reflected_guards_are_strict(self):
        self.assertEqual(0, exact.guard_bits(5040))
        self.assertEqual(0, exact.guard_bits(5039))
        self.assertEqual(1, exact.guard_bits(5041))
        # R, p^(3(b+1)), X, E, P^2 R Rj, P^2 R Rj+1.
        good = [5041, 10, 11, 130, 129, 131]
        self.assertEqual(31, exact.guard_bits(*good))
        for index, value, bit in [(0, 5040, 0), (1, 11, 1), (3, 121, 2),
                                  (4, 130, 3), (5, 130, 4)]:
            args = good.copy(); args[index] = value
            self.assertFalse(exact.guard_bits(*args) & (1 << bit))

    def test_constant_rows_validate_order_primality_and_every_mask(self):
        rows = constant_fixture()
        exact.validate_constants(rows, list(exact.PRIMES))
        for mutate in ('mask', 'product', 'prime', 'order'):
            bad = copy.deepcopy(rows)
            if mutate == 'mask': bad[0]['sorted_masks'][1] = 0
            if mutate == 'product': bad[0]['subset_products'][3] += 1
            if mutate == 'prime': bad[0]['primes'][2] = 9
            if mutate == 'order': bad[0], bad[1] = bad[1], bad[0]
            with self.assertRaises(ValueError):
                exact.validate_constants(bad, list(exact.PRIMES))

    def test_input_identity_is_checked_before_consumption(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d)/'input.json'; p.write_text('{}\n')
            with self.assertRaisesRegex(ValueError, 'identity'):
                exact.load_input(p, '0'*64)

    def test_full_domain_range_and_last_raw_id(self):
        exact.validate_window(0, 229375, 64)
        self.assertEqual(5734399, 25*229375+24)
        for a,b,c in [(-1,0,1),(0,229376,1),(2,1,1),(0,0,0)]:
            with self.assertRaises(ValueError): exact.validate_window(a,b,c)

    def test_missing_duplicate_reordered_rows_are_never_replaced(self):
        rows = [{'integers':[i]} for i in range(25)]
        exact.check_coverage(rows, 0, 0)
        for bad in (rows[:-1], rows+[rows[-1]], rows[:5]+rows[6:],
                    rows[:5]+[rows[4]]+rows[6:], list(reversed(rows))):
            with self.assertRaises(ValueError): exact.check_coverage(bad,0,0)

    def test_corrupted_guard_proposal_is_retained_as_disagreement(self):
        audited = exact.audit_row(raw_fixture(bits=0, active=0), constant_fixture())
        self.assertTrue(audited['active'])
        self.assertEqual(1, audited['guard_bits'])
        self.assertEqual(['guard_bits', 'activity'], audited['disagreements'])

    def test_bad_parameters_and_internal_overflow_cannot_exclude(self):
        bad = raw_fixture(); bad['integers'][4] = 11
        with self.assertRaisesRegex(ValueError, 'parameters'):
            exact.audit_row(bad, constant_fixture())
        row = exact.audit_row(raw_fixture(error=1), constant_fixture())
        self.assertIn('integer_error', row['disagreements'])
        self.assertTrue(row['active'])

    def test_inactive_slots_are_audited_too(self):
        raw = raw_fixture(); raw['integers'] = [76800,3072,0,0,12,0,0,2,3,5,
                                               0,1,-1,1,-1,0,0,0]
        row = exact.audit_row(raw, constant_fixture())
        self.assertFalse(row['active'])
        self.assertEqual(4096, row['R_lower'])
        raw['integers'][15] = 1
        self.assertIn('guard_bits', exact.audit_row(raw,constant_fixture())['disagreements'])


class CertificationContracts(unittest.TestCase):
    def test_reflected_distance_tie_and_rational_upper_budget(self):
        self.assertEqual((F(8), True), certify.distance_ratio(F(64),F(512),2,16))
        # Exact upper boundary gives zero; overlapping balls are never used here.
        self.assertEqual((F(1), False), certify.distance_ratio(F(64),F(512),8,16))
        row = raw_fixture()
        row['integers'] = [76807,3072,7,0,12,0,0,2,3,5,0,1,2,1,0,0,0,0]
        audited = exact.audit_row(row,constant_fixture())
        self.assertNotEqual(1, F(audited['exp_T1']).denominator)
        self.assertEqual(F(2**81,30**2*4096), F(audited['exp_T1']))

    def test_every_negative_and_noncandidate_is_independently_evaluated(self):
        for raw in (raw_fixture(),raw_fixture(bits=0,active=0)):
            audited = exact.audit_row(raw, constant_fixture())
            with patch.object(certify, 'evaluate', return_value={'G':arb(1)}) as eval_gap:
                result = certify.certify_row(audited, (64,128))
            self.assertEqual('positive',result['outcome'])
            self.assertEqual(1,eval_gap.call_count)
            self.assertEqual(audited['proposed']=='negative',result['sign_disagreement'])

    def test_straddling_is_unresolved_and_escalation_is_bounded(self):
        audited = exact.audit_row(raw_fixture(), constant_fixture())
        with patch.object(certify, 'evaluate', return_value={'G':arb(0,1)}) as eval_gap:
            result = certify.certify_row(audited, (64,128,256))
        self.assertEqual('unresolved',result['outcome'])
        self.assertEqual(3,eval_gap.call_count)
        self.assertEqual([64,128,256], [x['precision'] for x in result['refinements']])
        self.assertEqual('unresolved',certify.sign(arb(-1,1)))
        class ClosedBall:
            def __init__(self,lo,hi): self.lo,self.hi=F(lo),F(hi)
            def is_finite(self): return True
            def __lt__(self,x): return self.hi<x
            def __gt__(self,x): return self.lo>x
            def upper(self): return self.hi
            def lower(self): return self.lo
        self.assertEqual('nonpositive',certify.sign(ClosedBall(-2,0)))
        self.assertEqual('nonnegative',certify.sign(ClosedBall(0,2)))
        self.assertNotEqual('zero',certify.sign(arb(0)))

    def test_zero_variance_endpoints_secant_ties_and_saturation(self):
        with ctx.workprec(128):
            # Three identical two-point rows: all six secant slopes tie.
            values = certify.evaluate([2,2,2],[4,4,4],F(8),F(64))
            self.assertTrue(values['rho'].is_zero())
            self.assertTrue(values['G'].contains(0))
            upper = certify.evaluate([2,2,2],[4,4,4],F(8),F(512))
            self.assertTrue(upper['D'].contains(3*(arb(3)/4).log()))
            self.assertEqual('negative',certify.sign(upper['G']))
            self.assertEqual(6,len(upper['mixtures']))

    def test_proposals_with_nonfinite_or_underflow_are_not_signs(self):
        for error, value in [(2,-1.0),(4,-1.0),(0,float('nan'))]:
            row = exact.audit_row(raw_fixture(error=error,proposal=value),constant_fixture())
            self.assertEqual('indeterminate', row['proposed'])


class PublicationContracts(unittest.TestCase):
    def assert_verified_fixture(self, receipt):
        self.assertEqual('verify',receipt['mode'])
        self.assertEqual(25,receipt['verification_replay_rows'])
        self.assertEqual(0,receipt['new_gpu_raw_rows'])
        self.assertEqual(0,receipt['recovered_gpu_raw_rows'])
        self.assertEqual([],receipt['events'])
        self.assertTrue(receipt['summary']['coverage_complete'])
        self.assertEqual(25,receipt['summary']['completed_rows'])
        self.assertEqual(6,receipt['summary']['cpu_evaluated_active'])
        for key in ('unresolved_ids','invalid_ids','disagreement_ids'):
            self.assertEqual([],receipt['summary'][key])

    def test_run_summary_publication_error_returns_nonzero(self):
        with tempfile.TemporaryDirectory() as d, patch.dict(os.environ,{'GPU5040_SHARED_ROOT':d+'/shared'}):
            args=verification_fixture(d)
            root=Path(args.state_dir); attempted=[]
            checkpoint=root/'window-3072-3072/checkpoint.json'
            before=checkpoint.read_bytes()
            atomic_json=runner.state_store.atomic_json
            def fail_summary(path, value):
                if path==root/'summary.json':
                    attempted.append(value)
                    raise OSError('synthetic summary publication failure')
                atomic_json(path,value)
            with (patch.object(runner.state_store,'atomic_json',side_effect=fail_summary),
                  patch.object(runner,'environment',return_value={'synthetic':True}),
                  patch.object(runner,'MpsRunner',side_effect=AssertionError('GPU forbidden')),
                  redirect_stdout(io.StringIO()) as output):
                code=runner.run(args)
            self.assertEqual(1,len(attempted))
            self.assertEqual('certified_window',attempted[0]['status'])
            self.assertFalse((root/'summary.json').exists())
            self.assertEqual(before,checkpoint.read_bytes())
            printed=json.loads(output.getvalue())
            receipt=json.loads(Path(printed['artifact']).read_bytes())
            self.assert_verified_fixture(receipt)
            self.assertEqual('failed',receipt['status'])
            self.assertEqual('failed',printed['status'])
            self.assertIn('synthetic summary publication failure',receipt['error'])
            self.assertEqual(code,printed['exit_code'])
            self.assertEqual((True,True),(code!=0,receipt['exit_code']!=0),
                             f"run exit={code}, receipt exit={receipt['exit_code']}")

    def assert_process_publication_outcomes(self, through_make):
        for collision in (False,True):
            with (self.subTest(summary_directory_collision=collision),
                  tempfile.TemporaryDirectory() as d,
                  patch.dict(os.environ,{'GPU5040_SHARED_ROOT':d+'/shared'})):
                args=verification_fixture(d)
                root=Path(args.state_dir); summary=root/'summary.json'
                checkpoint=root/'window-3072-3072/checkpoint.json'
                before=checkpoint.read_bytes()
                if collision: summary.mkdir()
                if through_make:
                    command=['make','--no-print-directory','-C',str(Path(runner.__file__).resolve().parents[2]),
                             'prime-slab-verify','SLAB_FIRST=3072','SLAB_LAST=3072','SLAB_CHUNK=1',
                             'SLAB_MAX_CHUNKS=0','SLAB_PRECISIONS=128,256',
                             f'SLAB_STATE={root}',f'SLAB_INPUT={args.input}',
                             f'SLAB_INPUT_SHA={args.input_sha256}']
                else:
                    command=[sys.executable,'-B',str(Path(runner.__file__).resolve()),'verify',
                             '--first-box','3072','--last-box','3072','--chunk-boxes','1',
                             '--precisions','128,256','--state-dir',str(root),
                             '--input',str(args.input),'--input-sha256',args.input_sha256]
                # Only an infrastructure hang guard; elapsed time is not a verdict.
                result=subprocess.run(command,capture_output=True,text=True,check=False,timeout=60)
                receipts=list(root.glob('run-*.json'))
                self.assertEqual(1,len(receipts),result.stdout+result.stderr)
                receipt=json.loads(receipts[0].read_bytes())
                self.assert_verified_fixture(receipt)
                self.assertEqual(before,checkpoint.read_bytes())
                printed=json.loads(result.stdout.splitlines()[-1])
                self.assertEqual(receipt['status'],printed['status'])
                self.assertEqual(receipt['exit_code'],printed['exit_code'])
                if collision:
                    self.assertEqual('failed',receipt['status'])
                    self.assertIn('IsADirectoryError',receipt['error'])
                    self.assertTrue(summary.is_dir())
                else:
                    published=json.loads(summary.read_bytes())
                    self.assertEqual('certified_window',receipt['status'])
                    self.assertEqual(receipt['status'],published['status'])
                    self.assertEqual(receipt['identity'],published['identity'])
                    self.assertEqual(receipt['summary']['classification_stream_sha256'],
                                     published['classification_stream_sha256'])
                self.assertEqual((collision,collision),
                                 (result.returncode!=0,receipt['exit_code']!=0),
                                 f"process exit={result.returncode}, receipt exit={receipt['exit_code']}")

    def test_verify_process_summary_publication_outcomes(self):
        self.assert_process_publication_outcomes(through_make=False)

    def test_make_verify_summary_publication_outcomes(self):
        self.assert_process_publication_outcomes(through_make=True)

    def test_incomplete_batch_and_identity_mismatch_do_not_advance_checkpoint(self):
        with tempfile.TemporaryDirectory() as d:
            store = storage.WindowStore(Path(d), {'program':'a'}, 0, 0)
            store.initialize()
            with self.assertRaises(ValueError): store.commit_chunk(0,0,[], 'raw')
            self.assertEqual([],store.checkpoint['chunks'])
            with self.assertRaisesRegex(ValueError,'identity'):
                storage.WindowStore(Path(d), {'program':'b'}, 0, 0).initialize()
            self.assertFalse((Path(d)/'classified-0-0.jsonl').exists())

    def test_publication_failure_never_certifies_partial_batch(self):
        with tempfile.TemporaryDirectory() as d:
            store = storage.WindowStore(Path(d), {'program':'a'}, 0, 0)
            store.initialize()
            records = [{'raw':{'integers':[i]}, 'cpu':{'outcome':'inactive'},
                        'validation_errors':[]} for i in range(25)]
            with patch.object(storage.state_store, 'atomic_write', side_effect=OSError('injected')):
                with self.assertRaises(OSError): store.commit_chunk(0,0,records,'raw')
            self.assertEqual([],json.loads((Path(d)/'checkpoint.json').read_text())['chunks'])

    def test_checkpoint_binds_stream_bytes_counts_and_pending_raw(self):
        with tempfile.TemporaryDirectory() as d:
            store=storage.WindowStore(Path(d),{'program':'a'},3072,3072); store.initialize()
            raw=transport_fixture()
            path=store.write_raw(3072,3072,raw,{'synthetic':True})
            self.assertEqual(raw,store.pending_raw()[2])
            with self.assertRaises(ValueError): store.write_raw(3072,3072,raw,{'synthetic':True})
            records=runner.verify_rows(raw,constant_fixture(),(128,256))
            store.commit_chunk(3072,3072,records,storage.state_store.file_hash(path))
            summary=store.summary()
            self.assertEqual(25,summary['completed_rows'])
            self.assertEqual(6,summary['cpu_evaluated_active'])
            checkpoint=json.loads(store.path.read_bytes())
            checkpoint['chunks'][0]['counts']['raw_rows']=24
            storage.state_store.atomic_json(store.path,checkpoint)
            with self.assertRaisesRegex(ValueError,'accounting'):
                storage.WindowStore(Path(d),{'program':'a'},3072,3072).initialize()
            storage.state_store.atomic_json(store.path,store.checkpoint)
            path.write_bytes(path.read_bytes()+b'{}\n')
            with self.assertRaisesRegex(ValueError,'raw digest'):
                storage.WindowStore(Path(d),{'program':'a'},3072,3072).initialize()

    def test_lock_busy_is_nonblocking_and_preserves_shared_inode(self):
        with tempfile.TemporaryDirectory() as d, patch.dict(os.environ,{'GPU5040_SHARED_ROOT':d+'/shared'}):
            with storage.state_store.StateLocks(d+'/one'):
                lock=Path(d)/'shared/gpu-verifier.lock'; inode=lock.stat().st_ino
                with self.assertRaisesRegex(ValueError,str(lock)):
                    with storage.state_store.StateLocks(d+'/two'): self.fail('stole shared lock')
                self.assertEqual(inode,lock.stat().st_ino)
            with storage.state_store.StateLocks(d+'/two'): pass
            self.assertEqual(inode,lock.stat().st_ino)

    def test_run_resume_and_reverify_consume_only_returned_rows(self):
        class FakeMps:
            gpu_seconds=0
            def __init__(self,*args): pass
            def search(self,first,last):
                if first!=last or first not in (3072,3073): raise AssertionError('unregistered fixture')
                rows=transport_fixture()
                if first==3073:
                    for row in rows:
                        v=row['integers']; v[0]+=25; v[1]+=1; v[6]=1; v[15]|=1
                        v[16]=int(v[2]<7)
                return rows
        with tempfile.TemporaryDirectory() as d, patch.dict(os.environ,{'GPU5040_SHARED_ROOT':d+'/shared'}):
            args=SimpleNamespace(command='search',first_box=3072,last_box=3073,chunk_boxes=1,
                                 max_chunks=1,precisions='128,256',state_dir=d+'/run',
                                 input='synthetic',input_sha256='synthetic')
            with (patch.object(runner.exact,'load_input',return_value=constant_fixture()),
                  patch.object(runner,'environment',return_value={'synthetic':True}),
                  patch.object(runner,'MpsRunner',FakeMps),redirect_stdout(io.StringIO())):
                self.assertEqual(0,runner.run(args))
                summary=json.loads((Path(d)/'run/summary.json').read_bytes())
                self.assertFalse(summary['coverage_complete'])
                self.assertEqual(3073,summary['next_box'])
                search=FakeMps.search
                def remaining_only(self,first,last):
                    if first!=3073: raise AssertionError('repeated a completed fixture chunk')
                    return search(self,first,last)
                with patch.object(FakeMps,'search',remaining_only):
                    self.assertEqual(0,runner.run(args))
                with patch.object(FakeMps,'search',side_effect=AssertionError('duplicate GPU search')):
                    self.assertEqual(0,runner.run(args))
                    args.command='verify'
                    self.assertEqual(0,runner.run(args))
            runs=[json.loads(p.read_bytes()) for p in (Path(d)/'run').glob('run-*.json')]
            self.assertEqual(50,sum(r['new_gpu_raw_rows'] for r in runs))
            self.assertEqual(50,sum(r['verification_replay_rows'] for r in runs))


def mutation_checks(directory):
    """Break production functions in memory; record predicted and actual named reds."""
    root=storage.state_store.external_path(directory)
    root.mkdir(parents=True,exist_ok=True)
    token=uuid.uuid4().hex
    specs=[(exact,'guard_bits',lambda *a:0,
            ['ExactContracts.test_cutoff_and_all_reflected_guards_are_strict',
             'ExactContracts.test_corrupted_guard_proposal_is_retained_as_disagreement']),
           (exact,'check_coverage',lambda *a:None,
            ['ExactContracts.test_missing_duplicate_reordered_rows_are_never_replaced',
             'PublicationContracts.test_incomplete_batch_and_identity_mismatch_do_not_advance_checkpoint']),
           (certify,'sign',lambda *a:'negative',
            ['CertificationContracts.test_straddling_is_unresolved_and_escalation_is_bounded'])]
    original_certify=certify.certify_row
    def skip_negative(audit,precisions):
        return {'outcome':'negative'} if audit['proposed']=='negative' else original_certify(audit,precisions)
    specs.append((certify,'certify_row',skip_negative,
                  ['CertificationContracts.test_every_negative_and_noncandidate_is_independently_evaluated']))
    prereg=[]
    for module,name,_,names in specs:
        source=Path(module.__file__)
        compile(source.read_text(),str(source),'exec')
        prereg.append(dict(target=module.__name__+'.'+name,expected_red=names,
                           source_sha256=storage.state_store.file_hash(source)))
    storage.state_store.atomic_json(root/f'mutations-{token}-preregistration.json',prereg)
    results=[]; transcript=io.StringIO()
    for (module,name,replacement,names),prediction in zip(specs,prereg):
        original=getattr(module,name)
        suite=unittest.defaultTestLoader.loadTestsFromNames(names,sys.modules[__name__])
        # Imported aliases share the function object, not the module attribute.
        # Mutating its code exercises both exact and storage coverage consumers.
        old_code=original.__code__
        if name=='check_coverage':
            try:
                original.__code__=replacement.__code__
                result=unittest.TextTestRunner(stream=transcript,verbosity=2).run(suite)
            finally:
                original.__code__=old_code
        else:
            with patch.object(module,name,replacement):
                result=unittest.TextTestRunner(stream=transcript,verbosity=2).run(suite)
        observed=['.'.join(test.id().split('.')[-2:]) for test,_ in result.failures]
        restored=(getattr(module,name) is original and original.__code__ is old_code and
                  storage.state_store.file_hash(module.__file__)==prediction['source_sha256'])
        results.append(dict(**prediction,observed_red=observed,errors=len(result.errors),
                            compile_errors=0,mutant_test_exit=0 if result.wasSuccessful() else 1,
                            restored=restored,passed=set(observed)==set(names) and not result.errors and restored))
    log=root/f'mutations-{token}.log'
    storage.state_store.atomic_write(log,lambda f:f.write(transcript.getvalue().encode()))
    output=root/f'mutations-{token}.json'
    storage.state_store.atomic_json(output,dict(results=results,log_ref=str(log),
                                                preregistration=str(root/f'mutations-{token}-preregistration.json')))
    print(json.dumps(dict(artifact=str(output),mutations=len(results),passed=all(r['passed'] for r in results))))
    return 0 if all(r['passed'] for r in results) else 1


if __name__ == '__main__':
    if len(sys.argv)==3 and sys.argv[1]=='--mutation-dir':
        raise SystemExit(mutation_checks(sys.argv[2]))
    unittest.main()

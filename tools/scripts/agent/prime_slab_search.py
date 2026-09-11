#!/usr/bin/env python3
"""Bounded MPS prime-slab windows, complete CPU audits, and external checkpoints.

Use make -C tools prime-slab-{search,test,device-test,verify}. CPU has no
candidate-generation path. Reverification consumes only previously returned IDs.
"""

import argparse
import importlib.metadata
import json
import math
import os
from pathlib import Path
import platform
import shlex
import subprocess
import sys
import time
import uuid

# Set before any code path can import Torch.
os.environ['PYTORCH_ENABLE_MPS_FALLBACK']='0'

from gpu5040 import state_store
from prime_slabs import certify, exact, storage
from prime_slabs.gpu import MpsRunner

PINS={'torch':'2.8.0','numpy':'2.0.2','python-flint':'0.8.0'}


def identities(input_sha, precisions):
    here=Path(__file__).resolve().parent
    sources=[Path(__file__).resolve(),here/'gpu5040/state_store.py']
    sources += sorted(p for p in (here/'prime_slabs').iterdir() if p.suffix in ('.py','.metal'))
    files={str(p.relative_to(here)):state_store.file_hash(p) for p in sources}
    return dict(schema=storage.SCHEMA,program_sha256=state_store.hash_json(files),files=files,
                kernel_sha256=files['prime_slabs/search.metal'],input_sha256=input_sha,
                dependencies=PINS,precisions=list(precisions),python=platform.python_version(),
                fallback='0',normalization='exp(min(c_i))*G; GPU 24 terms; CPU full expression')


def environment():
    deps={name:importlib.metadata.version(name) for name in PINS}
    exact.require(deps==PINS and sys.version_info[:2]==(3,12),'Python/dependency pin mismatch')
    result=dict(python=sys.version,executable=sys.executable,platform=platform.platform(),
                machine=platform.machine(),dependencies=deps,
                flags={k:os.environ.get(k) for k in ('PYTORCH_ENABLE_MPS_FALLBACK',
                       'PYTORCH_MPS_FAST_MATH','PYTORCH_MPS_PREFER_METAL')},
                metal_compile_options='Torch 2.8 compile_shader defaults; no GPU rounding certificate')
    if sys.platform=='darwin':
        for key,cmd in [('cpu',['sysctl','-n','machdep.cpu.brand_string']),
                        ('gpu',['system_profiler','-json','SPDisplaysDataType'])]:
            response=subprocess.run(cmd,capture_output=True,text=True,check=False)
            result[key+'_query_exit']=response.returncode
            if response.returncode:
                result[key+'_query_error']=response.stderr
            elif key=='cpu': result['cpu']=response.stdout.strip()
            else:
                cards=json.loads(response.stdout)['SPDisplaysDataType']
                result['gpu']=[{k:v for k,v in card.items() if k in
                               ('sppci_model','_name','spdisplays_cores','spdisplays_metal',
                                'spdisplays_vendor','spdisplays_device-id')} for card in cards]
    return result


def verify_rows(rows, constants, precisions):
    records=[]
    for raw in rows:
        try:
            audit=exact.audit_row(raw,constants)
            cpu=certify.certify_row(audit,precisions)
            records.append(dict(raw=raw,audit=audit,cpu=cpu,validation_errors=audit['disagreements']))
        except (ValueError,ArithmeticError) as error:
            records.append(dict(raw=raw,cpu=dict(outcome='invalid',refinements=[],sign_disagreement=False),
                                validation_errors=[str(error)]))
    return records


def clean_json(value):
    if isinstance(value,float) and not math.isfinite(value): return value.hex()
    if isinstance(value,dict): return {k:clean_json(v) for k,v in value.items()}
    if isinstance(value,(list,tuple)): return [clean_json(v) for v in value]
    return value


def run(args):
    started=time.perf_counter(); gpu=None; verification_seconds=0.0
    root=state_store.external_path(args.state_dir)
    precisions=tuple(int(x) for x in args.precisions.split(','))
    exact.require(precisions and tuple(sorted(set(precisions)))==precisions and
                  len(precisions)<=6 and all(32<=p<=4096 for p in precisions),'invalid precision ladder')
    exact.require(args.max_chunks>=0,'invalid max-chunks')
    if args.command!='device-test': exact.validate_window(args.first_box,args.last_box,args.chunk_boxes)
    constants=exact.load_input(args.input,args.input_sha256)
    identity=identities(args.input_sha256,precisions)
    attempt_id=uuid.uuid4().hex
    path=root/f'run-{attempt_id}.json'
    command=['uv','run','--python','3.12']
    for name,version in PINS.items(): command += ['--with',f'{name}=={version}']
    command += ['python',str(Path(__file__).resolve()),*sys.argv[1:]]
    receipt=dict(schema=storage.SCHEMA,attempt_id=attempt_id,command=shlex.join(command),
                 argv=[sys.executable,*sys.argv],started_at=state_store.utc_now(),identity=identity,
                 mode=args.command,status='started',events=[],new_gpu_raw_rows=0,
                 recovered_gpu_raw_rows=0,new_cpu_audited_rows=0,verification_replay_rows=0,
                 standing_goal_complete=False,full_campaign_complete=False)

    def publish(): state_store.atomic_json(path,clean_json(receipt))
    def record(kind,event):
        receipt['events'].append(dict(kind=kind,at=state_store.utc_now(),**event)); publish()

    exit_code=1
    try:
        # Reused unchanged: per-run state first, then the shared GPU/verifier lock; LOCK_NB.
        with state_store.StateLocks(root):
            publish()
            receipt['environment']=environment(); publish()
            if args.command=='device-test':
                gpu=MpsRunner(constants,record); gpu.device_tests()
                receipt['status']='device_tests_passed'; exit_code=0
            else:
                store=storage.WindowStore(root/f'window-{args.first_box}-{args.last_box}',
                                          identity,args.first_box,args.last_box)
                store.initialize()
                if args.command=='verify':
                    replay=[]
                    for entry in store.checkpoint['chunks']:
                        rows,_=store.read_raw(store.directory/entry['raw_file'],entry['first_box'],entry['last_box'])
                        start=time.perf_counter()
                        records=verify_rows(rows,constants,precisions)
                        verification_seconds += time.perf_counter()-start
                        saved=store.read_classified(entry)
                        exact.require(records==saved,'saved certification disagrees with independent recomputation')
                        receipt['verification_replay_rows'] += len(rows)
                        replay.append(dict(first_box=entry['first_box'],last_box=entry['last_box'],
                                           counts=storage.counts(records)))
                    receipt['reverified_chunks']=replay
                else:
                    chunks=0
                    while store.next_box<=args.last_box and (not args.max_chunks or chunks<args.max_chunks):
                        first=store.next_box
                        pending=store.pending_raw()
                        if pending:
                            raw_path,last,rows,_=pending
                            receipt['recovered_gpu_raw_rows'] += len(rows)
                        else:
                            last=min(first+args.chunk_boxes-1,args.last_box)
                            record('chunk_intent',dict(first_box=first,last_box=last,raw_rows=25*(last-first+1)))
                            if gpu is None: gpu=MpsRunner(constants,record)
                            rows=gpu.search(first,last)
                            receipt['new_gpu_raw_rows'] += len(rows)
                            raw_path=store.write_raw(first,last,rows,dict(attempt=str(path),device=receipt['environment']))
                        exact.check_coverage(rows,first,last)
                        start=time.perf_counter()
                        records=verify_rows(rows,constants,precisions)
                        verification_seconds += time.perf_counter()-start
                        receipt['new_cpu_audited_rows'] += len(rows)
                        entry=store.commit_chunk(first,last,records,state_store.file_hash(raw_path))
                        record('chunk_audited',entry)
                        chunks+=1
                        if entry['counts']['invalid_ids']: break
                summary=store.summary()
                receipt['summary']=summary
                residuals=summary['unresolved_ids'] or summary['invalid_ids'] or summary['disagreement_ids']
                receipt['status']=('audited_with_residuals' if residuals else
                                   'certified_window' if summary['coverage_complete'] else 'checkpointed')
                exit_code=1 if residuals else 0
                state_store.atomic_json(root/'summary.json',dict(identity=identity,attempt=str(path),
                                                                 status=receipt['status'],**summary))
    except (ValueError,RuntimeError,OSError,KeyError,TypeError) as error:
        exit_code=1
        receipt.update(status='failed',error=repr(error))
    finally:
        gpu_seconds=gpu.gpu_seconds if gpu is not None else sum(
            e.get('dispatch_and_synchronize_seconds',0) for e in receipt['events'])
        total=time.perf_counter()-started
        receipt.update(finished_at=state_store.utc_now(),exit_code=exit_code,
                       timing_seconds=dict(total=total,gpu_dispatch_and_synchronize=gpu_seconds,
                                           cpu_verification=verification_seconds,
                                           orchestration=total-gpu_seconds-verification_seconds))
        # An exclusive attempt name preserves even lock-busy failures without touching a checkpoint.
        root.mkdir(parents=True,exist_ok=True)
        publish()
    print(json.dumps(dict(status=receipt['status'],exit_code=exit_code,artifact=str(path),
                          summary=receipt.get('summary'),error=receipt.get('error')),sort_keys=True))
    return exit_code


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command',choices=('search','verify','device-test'))
    parser.add_argument('--input',required=True,type=Path)
    parser.add_argument('--input-sha256',required=True)
    parser.add_argument('--state-dir',required=True)
    parser.add_argument('--first-box',type=int)
    parser.add_argument('--last-box',type=int)
    parser.add_argument('--chunk-boxes',type=int,default=64)
    parser.add_argument('--max-chunks',type=int,default=0)
    parser.add_argument('--precisions',default='128,256,512')
    args=parser.parse_args()
    try: return run(args)
    except (ValueError,OSError) as error:
        print(json.dumps(dict(status='invalid_configuration',error=str(error)),sort_keys=True)); return 2


if __name__=='__main__':
    raise SystemExit(main())

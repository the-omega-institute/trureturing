#!/usr/bin/env python3
"""Foreground CPU search of the explicitly bounded actual-prime slab nodes."""
import argparse
from datetime import datetime, timezone
import hashlib
import importlib.metadata
import json
import os
from pathlib import Path
import resource
import shutil
import signal
import sys
import time

from prime_slabs import cpu
from prime_slabs.cpu_store import InputGap, Store

ROOT=Path(__file__).resolve().parents[3]
PROGRAMS=['tools/scripts/agent/prime_slab_cpu.py',
          'tools/scripts/agent/prime_slabs/cpu.py',
          'tools/scripts/agent/prime_slabs/cpu_store.py',
          'tools/scripts/agent/prime_slabs/certify.py']
LOW_FREE=2*1024**3
START_FREE=4*1024**3


def sha(path):
    result=hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda:stream.read(1024*1024),b''): result.update(block)
    return result.hexdigest()


def atomic_json(path,value):
    path=Path(path);temporary=path.with_name(path.name+'.tmp')
    with temporary.open('w') as f:
        f.write(cpu.dumps(value)+'\n');f.flush();os.fsync(f.fileno())
    os.replace(temporary,path)


def utc(): return datetime.now(timezone.utc).isoformat()


def timestamp(value):
    date=datetime.fromisoformat(value.replace('Z','+00:00'))
    if date.tzinfo is None: raise ValueError('deadline must include UTC offset')
    return date.timestamp()


def bind_inputs(path,expected,root=ROOT):
    if sha(path)!=expected: raise InputGap('input manifest SHA-256 mismatch')
    document=json.loads(Path(path).read_text())
    if document['experiment']!=cpu.EXPERIMENT:
        raise InputGap('input experiment definition/window/ladder/cap mismatch')
    for binding in document['source_bindings']:
        relative=Path(binding['path']);resolved=(root/relative).resolve()
        if relative.is_absolute() or not resolved.is_relative_to(root.resolve()):
            raise InputGap('source path outside repository: '+str(relative))
        if sha(resolved)!=binding['sha256']:
            raise InputGap('changed deciding source: '+str(relative))
    required={'docs/develop/theory/ARITHMETIC_BOUNDARY_QUANTIZATION.md',PROGRAMS[-1]}
    if not required<={b['path'] for b in document['source_bindings']}:
        raise InputGap('source and evaluator bindings required')
    for record in document['retained_supports']:
        if record.get('support_complete') is not True:
            raise InputGap('complete retained support binding required: '+cpu.dumps(record))
    # A matching support is a concrete input dependency. Never decode omitted legacy rows.
    for q in cpu.EXPERIMENT['q']:
        matches=cpu.matching_supports(((2,0),(3,0),(q,0)),document['retained_supports'])
        if matches: raise InputGap('matching retained support needs exact records: '+cpu.dumps(matches))
    return document


def runtime():
    import flint
    if sys.version_info[:2]!=(3,12) or flint.__version__!='0.8.0':
        raise InputGap('runtime requires established Python3.12/python-flint0.8.0')
    return dict(python=sys.version,python_flint=flint.__version__,
                torch=importlib.metadata.version('torch'),numpy=importlib.metadata.version('numpy'),
                platform=sys.platform)


class Limits:
    """Cooperative foreground signals; one alarm bounds an unfinished Arb call."""
    def __init__(self,store,phase,deadline,output):
        self.store,self.phase,self.deadline,self.output=store,phase,deadline,output
        self.requested=None

    def stop_signal(self,number,frame): self.requested=signal.Signals(number).name

    def remaining_ns(self):
        wall=max(0,int((self.deadline-time.time())*1e9))
        if self.phase=='pilot':
            wall=min(wall,max(0,cpu.PILOT_CAP_NS-self.store.spent_ns('pilot')))
        return 0 if self.requested else wall

    def reason(self):
        if self.requested: return self.requested
        if time.time()>=self.deadline: return 'flight-clock'
        if self.phase=='pilot' and self.store.spent_ns('pilot')>=cpu.PILOT_CAP_NS:
            return 'pilot-evaluation-cap'
        if shutil.disk_usage(self.output).free<LOW_FREE: return 'low-free-space'
        return None

    def evaluate(self,node,precision):
        def expired(number,frame): raise TimeoutError('evaluation budget/flight clock')
        prior=signal.signal(signal.SIGALRM,expired)
        try:
            remaining=self.remaining_ns()
            if remaining<=0: raise TimeoutError('evaluation budget exhausted')
            signal.setitimer(signal.ITIMER_REAL,remaining/1e9)
            return cpu.evaluate_tier(node,precision)
        finally:
            signal.setitimer(signal.ITIMER_REAL,0)
            signal.signal(signal.SIGALRM,prior)


def execute(store,phase,max_boxes,limits,producer):
    """Visit a bounded prefix of unfinished boxes; completed keys never reevaluate."""
    if phase=='window':
        pilot=store.summary('pilot')
        if pilot['boxes_complete']!=64:
            raise InputGap('window requires completed pilot; unresolved pilot work is retained')
    counts=dict(boxes_processed=0,boxes_skipped=0,completed_keys_skipped=0,residual_keys_skipped=0)
    candidates=[key for key, in store.connection.execute("SELECT key FROM nodes WHERE status='candidate'")]
    if candidates:
        for key in candidates:
            record=store.read_node(key)
            node=dict(key=key,input=record['input'],exact=record['exact'],origin=record['origin'])
            store.validate_record(node,record)
        return dict(reason='candidate-needs-independent-certification',candidates=candidates,**counts)
    for pairs in cpu.boxes(phase):
        reason=limits.reason()
        if reason: return dict(reason=reason,**counts)
        found=store.find_box(pairs)
        if not (found and found[1]) and counts['boxes_processed']>=max_boxes:
            return dict(reason='batch-box-limit',**counts)
        box=cpu.make_box(pairs)
        if found and found[0]!={k:v for k,v in box.items() if k!='nodes'}:
            raise InputGap(cpu.dumps(pairs)+': stored exact box/guard binding mismatch')
        # Verify previously bound exact records even when a box claims completion.
        store.register_box(box)
        if found and found[1]:
            if not store.finish_box(pairs): raise InputGap(cpu.dumps(pairs)+': false box completion')
            counts['boxes_skipped']+=1
            continue
        for node in box['nodes']:
            reason=limits.reason()
            if reason: return dict(reason=reason,**counts)
            prior=store.read_node(node['key'])
            if prior['status']=='completed': counts['completed_keys_skipped']+=1
            if prior['status']=='residual': counts['residual_keys_skipped']+=1
            result=store.evaluate_node(node,phase,limits.evaluate,producer,
                                       limits.remaining_ns,time.monotonic_ns)
            if result['status']=='candidate':
                store.finish_box(pairs)
                return dict(reason='candidate-needs-independent-certification',
                            candidates=[node['key']],**counts)
            if result['status']=='pending': return dict(reason=limits.reason() or 'evaluation-budget',**counts)
        store.finish_box(pairs);counts['boxes_processed']+=1
    return dict(reason='fixed-phase-complete',**counts)


def parser():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--input',type=Path,required=True)
    p.add_argument('--input-sha256',required=True)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--phase',choices=('pilot','window'),required=True)
    p.add_argument('--max-boxes',type=int,required=True)
    p.add_argument('--deadline',required=True,help='finite UTC stop-new-work clock')
    return p


def main(argv=None):
    args=parser().parse_args(argv)
    if args.max_boxes<=0: raise InputGap('positive bounded --max-boxes required')
    start=time.monotonic_ns();started=utc();usage0=resource.getrusage(resource.RUSAGE_SELF)
    input_document=bind_inputs(args.input,args.input_sha256)
    deadline=timestamp(args.deadline)
    if not time.time()<deadline: raise InputGap('stop-new-work clock already reached')
    environment=runtime()
    args.output.mkdir(parents=True,exist_ok=True)
    free=shutil.disk_usage(args.output).free
    if free<START_FREE: raise InputGap('startup free space below4GiB: '+str(free))
    producer_document=dict(schema='actual-prime-cpu-producer-v1',input_sha256=args.input_sha256,
        inputs=input_document,program_sha256={p:sha(ROOT/p) for p in PROGRAMS},
        runtime=environment,started_utc=started,deadline_utc=args.deadline,
        phase=args.phase,max_boxes=args.max_boxes)
    producer=cpu.digest(producer_document);exit_code=0
    sources=args.output/'producer-sources';sources.mkdir(exist_ok=True)
    for relative,expected in producer_document['program_sha256'].items():
        target=sources/(expected+'.py')
        if not target.exists():
            content=(ROOT/relative).read_bytes()
            if hashlib.sha256(content).hexdigest()!=expected:
                raise InputGap('program changed during input binding: '+relative)
            temporary=target.with_suffix('.tmp');temporary.write_bytes(content);os.replace(temporary,target)
        if sha(target)!=expected: raise InputGap('retained program digest mismatch: '+expected)
    with Store(args.output/'results.sqlite3',cpu.EXPERIMENT) as store:
        scientific_input={k:input_document[k] for k in ('question','retained_supports','corpus_bindings')}
        old=store.get_meta('scientific_input')
        if old is not None and old!=scientific_input:
            raise InputGap('retained question/corpus binding differs; named input correction required')
        store.set_meta('scientific_input',scientific_input)
        store.add_producer(producer,producer_document)
        limits=Limits(store,args.phase,deadline,args.output)
        previous={s:signal.signal(s,limits.stop_signal) for s in (signal.SIGINT,signal.SIGTERM)}
        before=store.summary()
        try:
            result=execute(store,args.phase,args.max_boxes,limits,producer)
        except (TimeoutError,KeyboardInterrupt) as e:
            result=dict(reason='interrupted-uncompleted-tier',error=type(e).__name__+': '+str(e))
        except (InputGap,ValueError,KeyError,TypeError) as e:
            result=dict(reason='named-input-or-evaluator-gap',error=type(e).__name__+': '+str(e));exit_code=2
        finally:
            for s,handler in previous.items(): signal.signal(s,handler)
        usage=resource.getrusage(resource.RUSAGE_SELF)
        report=dict(schema='actual-prime-cpu-run-result-v2',producer=producer,
            started_utc=started,finished_utc=utc(),exit_code=exit_code,result=result,
            coverage=store.summary(),pilot=store.summary('pilot'),
            measurement=dict(wall_ns=time.monotonic_ns()-start,
                evaluation_ns=store.spent_ns('pilot')+store.spent_ns('window')-
                              before['pilot_evaluation_ns']-before['window_evaluation_ns'],
                user_seconds=usage.ru_utime-usage0.ru_utime,system_seconds=usage.ru_stime-usage0.ru_stime,
                process_peak_rss_bytes=int(usage.ru_maxrss*(1 if sys.platform=='darwin' else 1024)),
                free_bytes_start=free,free_bytes_end=shutil.disk_usage(args.output).free),
            boundary='Directed Arb discovery; no independent candidate adjudication or Lean proof.')
        # Results already live in nodes/boxes/costs. Avoid a second progress snapshot.
        with store.connection: store.connection.execute("DELETE FROM metadata WHERE name='last_result'")
    report['database_sha256']=sha(args.output/'results.sqlite3')
    report['search_phase_measurement']=report['measurement'].copy()
    usage=resource.getrusage(resource.RUSAGE_SELF)
    report['measurement'].update(wall_ns=time.monotonic_ns()-start,
        user_seconds=usage.ru_utime-usage0.ru_utime,system_seconds=usage.ru_stime-usage0.ru_stime,
        process_peak_rss_bytes=int(usage.ru_maxrss*(1 if sys.platform=='darwin' else 1024)),
        scope='Through closed-database streaming hash; excludes only final small JSON/stdout publication.')
    report['finished_utc']=utc()
    atomic_json(args.output/('result-'+producer+'.json'),report)
    print(cpu.dumps(report),flush=True)
    return exit_code


if __name__=='__main__':
    try: sys.exit(main())
    except (InputGap,ValueError,OSError) as e:
        print(cpu.dumps(dict(error=type(e).__name__+': '+str(e))),file=sys.stderr);sys.exit(2)

"""Bounded window checkpoints. Canonical durability/exclusion belongs to gpu5040."""

from collections import Counter
import hashlib
import json
from pathlib import Path

from gpu5040 import state_store
from .exact import check_coverage, require, validate_window

SCHEMA = 'prime-slab-raw-and-arb-v1'
OUTCOMES = {'inactive','negative','positive','nonpositive','nonnegative','unresolved','invalid'}


def line(value):
    return (json.dumps(value,sort_keys=True,separators=(',',':'),allow_nan=False)+'\n').encode()


def counts(records):
    outcomes, kinds, proposals, errors = Counter(), Counter(), Counter(), Counter()
    unresolved, disagreements, invalid = [], [], []
    completed = evaluated = refinements = 0
    for row in records:
        row_id = row['raw']['integers'][0]
        kind = 'adjacent' if row_id % 25 < 7 else 'reflected'
        cpu, audit = row['cpu'], row.get('audit',{})
        outcome = cpu['outcome']
        require(outcome in OUTCOMES, 'unknown certified outcome')
        outcomes[outcome] += 1; kinds[kind] += 1
        proposals[audit.get('proposed','unvalidated')] += 1
        history = cpu.get('refinements',[])
        evaluated += bool(history); refinements += max(0,len(history)-1)
        if outcome == 'unresolved': unresolved.append(row_id)
        if row['validation_errors']: invalid.append(row_id)
        if cpu.get('sign_disagreement') or audit.get('disagreements'):
            disagreements.append(row_id)
        for bit,name in ((1,'integer_overflow'),(2,'nonfinite'),(4,'underflow'),(8,'other')):
            errors[name] += bool(audit.get('gpu_error_bits',0)&bit)
        completed += not row['validation_errors'] and outcome not in ('unresolved','invalid')
    return dict(raw_rows=len(records),by_kind=dict(kinds),by_outcome=dict(outcomes),
                by_proposal=dict(proposals),gpu_flags=dict(errors),completed_rows=completed,
                cpu_evaluated_active=evaluated,extra_precision_evaluations=refinements,
                unresolved_ids=unresolved,disagreement_ids=disagreements,invalid_ids=invalid)


class WindowStore:
    def __init__(self, directory, identity, first, last):
        validate_window(first,last,1)
        self.directory = state_store.external_path(directory)
        self.identity, self.first, self.last = identity, first, last
        self.path = self.directory/'checkpoint.json'
        self.checkpoint = dict(schema=SCHEMA,identity=identity,first_box=first,last_box=last,chunks=[])

    def initialize(self):
        self.directory.mkdir(parents=True,exist_ok=True)
        if self.path.exists():
            doc = json.loads(self.path.read_bytes())
            for key in ('schema','identity','first_box','last_box'):
                require(doc.get(key) == self.checkpoint[key], 'checkpoint identity/schema/window mismatch')
            self.checkpoint = doc
            next_box = self.first
            for entry in doc['chunks']:
                require(entry['first_box'] == next_box and entry['last_box'] <= self.last,
                        'checkpoint missing/overlapping chunk')
                records = self.read_classified(entry)
                require(counts(records) == entry['counts'], 'incomplete checkpoint accounting')
                next_box = entry['last_box']+1
        else:
            state_store.atomic_json(self.path,self.checkpoint)

    @property
    def next_box(self):
        return self.checkpoint['chunks'][-1]['last_box']+1 if self.checkpoint['chunks'] else self.first

    def write_raw(self, first, last, rows, provenance):
        path = self.directory/f'raw-{first}-{last}.jsonl'
        require(not path.exists(), 'refusing to replace existing GPU raw stream')
        # Save even malformed device output. Coverage failure must remain inspectable.
        header = dict(schema=SCHEMA,identity=self.identity,first_box=first,last_box=last,
                      provenance=provenance)
        def writer(stream):
            stream.write(line(header))
            for row in rows: stream.write(line(row))
        state_store.atomic_write(path,writer)
        return path

    def read_raw(self, path, first, last):
        with Path(path).open('rb') as stream:
            header = json.loads(next(stream))
            require(header.get('schema') == SCHEMA and header.get('identity') == self.identity
                    and header.get('first_box') == first and header.get('last_box') == last,
                    'raw stream identity/schema/window mismatch')
            rows = [json.loads(data) for data in stream]
        check_coverage(rows,first,last)
        return rows,header

    def pending_raw(self):
        paths = list(self.directory.glob(f'raw-{self.next_box}-*.jsonl'))
        require(len(paths) <= 1, 'ambiguous pending raw chunks')
        if not paths: return None
        with paths[0].open('rb') as stream: header = json.loads(next(stream))
        last = header['last_box']
        require(self.next_box <= last <= self.last, 'pending raw range mismatch')
        rows,header = self.read_raw(paths[0],self.next_box,last)
        return paths[0],last,rows,header

    def commit_chunk(self, first, last, records, raw_digest):
        require(first == self.next_box and first <= last <= self.last, 'noncontiguous chunk commit')
        check_coverage([r['raw'] for r in records],first,last)
        summary = counts(records)
        # Never publish a batch while some rows still lack their verification result.
        require(all('validation_errors' in r and 'cpu' in r for r in records),
                'incomplete verification batch')
        path = self.directory/f'classified-{first}-{last}.jsonl'
        def writer(stream):
            for row in records: stream.write(line(row))
        state_store.atomic_write(path,writer)
        entry = dict(first_box=first,last_box=last,raw_file=f'raw-{first}-{last}.jsonl',
                     raw_sha256=raw_digest,classified_file=path.name,
                     classified_sha256=state_store.file_hash(path),counts=summary,
                     status='audited_with_residuals' if summary['unresolved_ids'] or
                     summary['invalid_ids'] or summary['disagreement_ids'] else 'certified')
        checkpoint = dict(self.checkpoint,chunks=[*self.checkpoint['chunks'],entry])
        state_store.atomic_json(self.path,checkpoint)
        self.checkpoint = checkpoint
        return entry

    def read_classified(self, entry):
        first,last = entry['first_box'],entry['last_box']
        require(entry['classified_file'] == f'classified-{first}-{last}.jsonl'
                and entry['raw_file'] == f'raw-{first}-{last}.jsonl', 'chunk path mismatch')
        path = self.directory/entry['classified_file']
        require(state_store.file_hash(path) == entry['classified_sha256'], 'classification digest mismatch')
        require(state_store.file_hash(self.directory/entry['raw_file']) == entry['raw_sha256'],
                'raw digest mismatch')
        records = [json.loads(data) for data in path.read_bytes().splitlines()]
        check_coverage([r['raw'] for r in records],first,last)
        return records

    def summary(self):
        # Streaming aggregation: at most one certified chunk resident, even for the full domain.
        classified, raw = hashlib.sha256(), hashlib.sha256()
        summary = dict(raw_rows=0,completed_rows=0,cpu_evaluated_active=0,
                       extra_precision_evaluations=0,by_kind=Counter(),by_outcome=Counter(),
                       by_proposal=Counter(),gpu_flags=Counter(),unresolved_ids=[],
                       disagreement_ids=[],invalid_ids=[])
        for entry in self.checkpoint['chunks']:
            records = self.read_classified(entry)
            chunk = counts(records)
            for key,value in summary.items():
                if isinstance(value,Counter): value.update(chunk[key])
                elif isinstance(value,list): value.extend(chunk[key])
                else: summary[key] += chunk[key]
            for row in records:
                classified.update(line(row)); raw.update(line(row['raw']))
        summary.update(first_box=self.first,last_box=self.last,
                       first_raw_row=25*self.first,last_raw_row=25*(self.last+1)-1,
                       next_box=self.next_box,coverage_complete=self.next_box==self.last+1,
                       classification_stream_sha256=classified.hexdigest(),
                       raw_stream_sha256=raw.hexdigest(),
                       checkpoint=str(self.path))
        return summary

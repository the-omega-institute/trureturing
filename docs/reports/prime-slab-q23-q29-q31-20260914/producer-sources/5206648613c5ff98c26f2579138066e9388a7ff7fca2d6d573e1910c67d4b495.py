"""One experiment's exact-key results and resumable tier expenditures.

SQLite transactions atomically pair completed enclosures with their cost.
There is no daemon, work queue, cross-experiment registry or GPU state access.
An unclean, unmeasured in-flight tier is a named expenditure gap, never zero.
"""
from fractions import Fraction as F
from pathlib import Path
import json
import sqlite3
from . import cpu

COMPLETED={'negative','nonpositive','nonnegative','positive'}
STATUS={'pending','completed','candidate','residual','invalid'}


class InputGap(ValueError):
    pass


class Store:
    def __init__(self,path,experiment):
        self.path=Path(path)
        self.connection=sqlite3.connect(self.path,timeout=0)
        self.connection.execute('PRAGMA locking_mode=EXCLUSIVE')
        self.connection.execute('PRAGMA journal_mode=DELETE')
        self.connection.execute('PRAGMA synchronous=FULL')
        self.connection.executescript('''
          CREATE TABLE IF NOT EXISTS metadata (name TEXT PRIMARY KEY, value TEXT NOT NULL);
          CREATE TABLE IF NOT EXISTS producers (id TEXT PRIMARY KEY, document TEXT NOT NULL);
          CREATE TABLE IF NOT EXISTS boxes
            (id TEXT PRIMARY KEY, document TEXT NOT NULL, complete INTEGER NOT NULL,
             pilot INTEGER NOT NULL, active INTEGER NOT NULL);
          CREATE TABLE IF NOT EXISTS nodes
            (key TEXT PRIMARY KEY, unit TEXT NOT NULL UNIQUE, document TEXT NOT NULL,
             status TEXT NOT NULL, sign TEXT NOT NULL, pilot INTEGER NOT NULL);
          CREATE TABLE IF NOT EXISTS costs (phase TEXT PRIMARY KEY, nanoseconds INTEGER NOT NULL);
        ''')
        stored=self.get_meta('experiment')
        if stored is not None and stored!=experiment:
            self.close();raise InputGap('experiment definition/window/precision/budget mismatch')
        self.set_meta('experiment',experiment)
        with self.connection:
            self.connection.executemany('INSERT OR IGNORE INTO costs VALUES (?,0)',
                                        [('pilot',),('window',)])

    def __enter__(self): return self
    def __exit__(self,*args): self.close()
    def close(self): self.connection.close()

    def get_meta(self,name):
        row=self.connection.execute('SELECT value FROM metadata WHERE name=?',(name,)).fetchone()
        return json.loads(row[0]) if row else None

    def set_meta(self,name,value):
        with self.connection:
            self.connection.execute('INSERT OR REPLACE INTO metadata VALUES (?,?)',(name,cpu.dumps(value)))

    def add_producer(self,name,document):
        value=cpu.dumps(document)
        prior=self.connection.execute('SELECT document FROM producers WHERE id=?',(name,)).fetchone()
        if prior and prior[0]!=value: raise InputGap('conflicting producer '+name)
        with self.connection:
            self.connection.execute('INSERT OR IGNORE INTO producers VALUES (?,?)',(name,value))

    def read_node(self,key):
        row=self.connection.execute('SELECT document FROM nodes WHERE key=?',(key,)).fetchone()
        return json.loads(row[0]) if row else None

    def replace_record(self,key,record):
        with self.connection:
            self.connection.execute('UPDATE nodes SET document=?,status=?,sign=? WHERE key=?',
                (cpu.dumps(record),record['status'],record['sign'],key))

    def validate_record(self,node,record):
        key=node['key']
        def need(test,field):
            if not test: raise InputGap(key+': '+field+' correction required')
        need(record.get('definition')==cpu.DEFINITION,'definition')
        need(record.get('input')==node['input'],'input binding')
        try:
            cpu.validate_node(dict(key=key,input=record['input'],exact=record['exact'],origin=record['origin']))
        except (ValueError,KeyError,TypeError) as e:
            raise InputGap(key+': retained witness/guard correction required: '+str(e)) from e
        # At a coalesced key, witnesses may differ but all endpoint and budget data must agree.
        for field in ('C','D','exp_T0','exp_T1'):
            need(record.get('exact',{}).get(field)==node['exact'][field],'exact '+field)
        need(record.get('status') in STATUS and record['status']!='invalid','invalid status')
        need(record.get('inflight') is None,'unmeasured interrupted evaluation expenditure')
        tiers=record.get('tiers',[])
        need([t.get('precision') for t in tiers]==list(cpu.PRECISIONS[:len(tiers)]),'precision history')
        for index,t in enumerate(tiers):
            need(type(t.get('evaluation_ns')) is int and t['evaluation_ns']>=0,'tier expenditure')
            need(t.get('outcome') in COMPLETED|{'unresolved'},'tier outcome')
            need(index==len(tiers)-1 or t['outcome']=='unresolved','completed ladder replay')
            need(self.connection.execute('SELECT 1 FROM producers WHERE id=?',
                                         (t.get('producer'),)).fetchone() is not None,'producer binding')
            bounds=t.get('bounds',{}).get('G')
            if t['outcome'] in COMPLETED:
                need(type(bounds) is list and len(bounds)==2,'sign enclosure')
                lo,hi=map(F,bounds);need(lo<=hi,'enclosure order')
                need(dict(negative=hi<0,positive=lo>0,nonpositive=hi<=0,nonnegative=lo>=0)[t['outcome']],
                     'sign/enclosure conflict')
        sign=tiers[-1]['outcome'] if tiers else 'unresolved'
        expected='candidate' if sign=='positive' else 'completed' if sign in COMPLETED else (
                 'residual' if len(tiers)==len(cpu.PRECISIONS) else 'pending')
        need(record['sign']==sign and record['status']==expected,'completion/sign binding')
        for event in record.get('interruptions',[]):
            need(event.get('precision') in cpu.PRECISIONS and
                 type(event.get('evaluation_ns')) is int and event['evaluation_ns']>=0,
                 'interrupted expenditure')

    def register_node(self,node):
        try: cpu.validate_node(node)
        except (ValueError,KeyError,TypeError) as e: raise InputGap(node['key']+': '+str(e)) from e
        record=self.read_node(node['key'])
        if record is not None:
            self.validate_record(node,record);return
        # Excluding the definition label detects an unknown meaning at the same physical input.
        unit=cpu.dumps({k:v for k,v in node['input'].items() if k!='definition'})
        conflict=self.connection.execute('SELECT key FROM nodes WHERE unit=?',(unit,)).fetchone()
        if conflict: raise InputGap(node['key']+': definition binding conflicts with '+conflict[0])
        record=dict(definition=cpu.DEFINITION,input=node['input'],exact=node['exact'],
                    origin=node['origin'],status='pending',sign='unresolved',tiers=[],
                    interruptions=[],inflight=None)
        with self.connection:
            self.connection.execute('INSERT INTO nodes VALUES (?,?,?,?,?,?)',
                (node['key'],unit,cpu.dumps(record),'pending','unresolved',
                 int(cpu.pilot_box(node['input']['coordinates']))))

    def spent_ns(self,phase):
        return self.connection.execute('SELECT nanoseconds FROM costs WHERE phase=?',(phase,)).fetchone()[0]

    def evaluate_node(self,node,phase,evaluator,producer,remaining_ns,clock):
        """Return prior completed/residual data, or run only its uncompleted tiers."""
        record=self.read_node(node['key'])
        if record is None: raise InputGap(node['key']+': absent input binding')
        self.validate_record(node,record)
        if record['status']!='pending': return record
        if not self.connection.execute('SELECT 1 FROM producers WHERE id=?',(producer,)).fetchone():
            raise InputGap(node['key']+': current producer binding missing')
        for precision in cpu.PRECISIONS[len(record['tiers']):]:
            if remaining_ns()<=0: break
            record['inflight']=dict(precision=precision,phase=phase,producer=producer)
            self.replace_record(node['key'],record)
            start=clock();tier=None;failure=None
            try:
                tier=evaluator(node,precision)
            except BaseException as e:
                failure=e
            elapsed=max(0,clock()-start)
            record['inflight']=None
            if failure is not None:
                record['interruptions'].append(dict(precision=precision,phase=phase,
                    producer=producer,evaluation_ns=elapsed,kind=type(failure).__name__))
                if not isinstance(failure,(KeyboardInterrupt,TimeoutError)):
                    record['status']='invalid'
                    record['error']=str(failure)
            else:
                tier.update(producer=producer,phase=phase,evaluation_ns=elapsed)
                record['tiers'].append(tier);record['sign']=tier['outcome']
                record['status']='candidate' if tier['outcome']=='positive' else (
                    'completed' if tier['outcome'] in COMPLETED else (
                    'residual' if precision==512 else 'pending'))
            # Cost and result/progress are one atomic update; no precision restart after commit.
            with self.connection:
                self.connection.execute('UPDATE costs SET nanoseconds=nanoseconds+? WHERE phase=?',
                                        (elapsed,phase))
                self.connection.execute('UPDATE nodes SET document=?,status=?,sign=? WHERE key=?',
                    (cpu.dumps(record),record['status'],record['sign'],node['key']))
            if failure is not None: raise failure
            self.validate_record(node,record)
            if record['status']!='pending': break
        return record

    def find_box(self,pairs):
        row=self.connection.execute('SELECT document,complete FROM boxes WHERE id=?',
                                    (cpu.dumps(cpu.coordinates(pairs)),)).fetchone()
        return (json.loads(row[0]),bool(row[1])) if row else None

    def register_box(self,box):
        for node in box['nodes']: self.register_node(node)
        document={k:v for k,v in box.items() if k!='nodes'}
        with self.connection:
            self.connection.execute('INSERT OR IGNORE INTO boxes VALUES (?,?,0,?,?)',
                (cpu.dumps(box['coordinates']),cpu.dumps(document),int(cpu.pilot_box(box['coordinates'])),
                 sum(s['active'] for s in box['slots'])))

    def finish_box(self,pairs):
        doc,_=self.find_box(pairs)
        for slot in doc['slots']:
            if slot['key'] and self.read_node(slot['key'])['status'] in ('pending','invalid'):
                return False
        with self.connection:
            self.connection.execute('UPDATE boxes SET complete=1 WHERE id=?',(cpu.dumps(cpu.coordinates(pairs)),))
        return True

    def summary(self,phase=None):
        condition=' WHERE pilot=1' if phase=='pilot' else ''
        box_count,complete,active=self.connection.execute(
            'SELECT count(*),coalesce(sum(complete),0),coalesce(sum(active),0) FROM boxes'+condition).fetchone()
        statuses=dict(self.connection.execute('SELECT status,count(*) FROM nodes'+condition+' GROUP BY status'))
        signs=dict(self.connection.execute('SELECT sign,count(*) FROM nodes'+condition+' GROUP BY sign'))
        return dict(boxes_enumerated=box_count,boxes_complete=complete,raw_slots=25*box_count,
            active_slots=active,inactive_slots=25*box_count-active,exact_keys=sum(statuses.values()),
            completed_exact_keys=statuses.get('completed',0)+statuses.get('candidate',0),
            statuses=statuses,signs=signs,pilot_evaluation_ns=self.spent_ns('pilot'),
            window_evaluation_ns=self.spent_ns('window'))

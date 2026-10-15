"""Independently decode every emitted Lean record and bind it to the DAG.

Checks the real literal BST, module intervals and all 1,558,777 native tuples.
This source/input binding is not Lean kernel acceptance.
"""
import hashlib
import json
import pathlib
import re
import struct

wt=pathlib.Path(__file__).resolve().parent.parent
source=wt/'D5/S3/Quantum/Entanglement/EJM'
cp=pathlib.Path('/Users/macstudio/omega/.formalization-goal-01a12631/checkpoints/ejm-mdd-global/existing-cover-original-suffix-alignment-20261014')
inputs=cp/'original-source-identity-stream'
manifest=json.loads((inputs/'original-global-dag-source.json').read_text())
checkpoint=(inputs/'stream-checkpoint.txt').read_text().splitlines()
raw=(inputs/checkpoint[2]).read_bytes()
magic,size=struct.unpack_from('<II',raw)
assert magic==0x454a4d32 and size==manifest['records']
assert hashlib.sha256(raw).hexdigest()==manifest['dag_sha256']
all_chunks={}
for block in manifest['blocks']:
    text=(source/(block['module']+'.lean')).read_text()
    rhs=text.split('def chunks : PackedTree :=',1)[1].split('\nend ')[0]
    tokens=re.findall(r'\.node|\.empty|0x[0-9a-f]+|\d+|[()]',rhs)
    at=0
    def parse():
        global at
        token=tokens[at];at+=1
        if token=='(':
            tree=parse();assert tokens[at]==')';at+=1;return tree
        if token=='.empty':return None
        assert token=='.node'
        key=int(tokens[at]);payload=int(tokens[at+1],16);at+=2
        assert key not in all_chunks;all_chunks[key]=payload
        left,right=parse(),parse()
        assert left is None or left[1]<key
        assert right is None or key<right[0]
        return (left[0] if left else key,right[1] if right else key,
            1+(left[2] if left else 0)+(right[2] if right else 0))
    tree=parse();assert at==len(tokens)
    assert tree==(block['first_chunk'],block['end_chunk']-1,block['end_chunk']-block['first_chunk'])
expected_chunks=(size+127)//128
assert sorted(all_chunks)==list(range(expected_chunks))
root_source=(source/'EJMOriginalGlobalDAGData.lean').read_text()
selectors=re.findall(r'if index < (\d+) then (EJMOriginalDAGBlock\d+).chunks.get index else',root_source)
assert selectors==[(str(b['end_chunk']),b['module']) for b in manifest['blocks'][:-1]]
assert manifest['blocks'][-1]['module']+'.chunks.get index' in root_source
expanded=[0]*size
bound_counts=[0]*size
for j in range(size):
    literal=all_chunks[j//128]>>(103*(j%128))&((1<<103)-1)
    decoded=(literal&3,(literal>>2)&131071,
        *((literal>>(19+21*a))&((1<<21)-1) for a in range(4)))
    original=struct.unpack_from('<6I',raw,8+24*j)
    assert decoded==original,(j,decoded,original)
    kind,payload,*children=decoded
    if kind==2:
        assert payload<20 and all(c<j for c in children)
        expanded[j]=1+sum(expanded[c] for c in children)
        bound_counts[j]=sum(bound_counts[c] for c in children)
    else:
        expanded[j]=1
        bound_counts[j]=int(kind==0)
assert expanded[1558776]==87458265
source_bindings={}
for item in manifest['modules']:
    p=source/(item['module']+'.lean');sha=hashlib.sha256(p.read_bytes()).hexdigest()
    assert sha==item['sha256'];source_bindings[p.name]=sha
plans=[]
for cap in [1024,4096,16384,65536]:
    summary=dict(maximum_segment_contexts=cap,segments=0,prefix_contexts=0,
        segment_contexts=0,minimum_depth=20,maximum_depth=0,actual_maximum_segment_contexts=0)
    stack=[(1558776,0)]
    while stack:
        j,depth=stack.pop()
        if expanded[j]<=cap:
            summary['segments']+=1;summary['segment_contexts']+=expanded[j]
            summary['minimum_depth']=min(summary['minimum_depth'],depth)
            summary['maximum_depth']=max(summary['maximum_depth'],depth)
            summary['actual_maximum_segment_contexts']=max(summary['actual_maximum_segment_contexts'],expanded[j])
        else:
            summary['prefix_contexts']+=1
            kind,payload,*children=struct.unpack_from('<6I',raw,8+24*j)
            assert kind==2 and payload==depth
            stack.extend((c,depth+1) for c in children)
    assert summary['prefix_contexts']+summary['segment_contexts']==87458265
    plans.append(summary)
record=dict(status='all_original_Lean_literals_independently_bound_not_kernel',kernel_accepted=False,
    records_checked=size,chunks_checked=expected_chunks,root=1558776,
    complete_expanded_contexts=expanded[1558776],dag_sha256=manifest['dag_sha256'],
    source_files=source_bindings,measured_segment_options=plans,
    kernel_obligations=['compile original DAG data and actual symmetry owner',
        'use actual initial/step/lower and unchanged original score soundness',
        'earn each suffix at its exact original prefix cache and partial event',
        'splice every suffix and complete prefix with checked_prefix_and_frontier',
        'derive unconditional original score bound and original locality exclusion'])
(inputs/'original-global-dag-source-binding.json').write_text(json.dumps(record,indent=2)+'\n')
# A real, nonempty numerical suffix is prepared for the first kernel cost
# measurement. Its cache is the actual original initial state followed by
# every literal prefix update; no native state snapshot replaces that term.
stack=[(1558776,())]
pilot=None
while stack:
    j,prefix=stack.pop()
    if 64<=expanded[j]<=256 and bound_counts[j]>=16:
        pilot=dict(global_index=j,depth=len(prefix),fuel=21-len(prefix),prefix=list(prefix),
            actual_contexts=expanded[j],bound_leaves=bound_counts[j],dag_sha256=manifest['dag_sha256'])
        break
    if expanded[j]>64:
        kind,payload,*children=struct.unpack_from('<6I',raw,8+24*j)
        if kind==2:
            assert payload==len(prefix)
            stack.extend((children[a],prefix+(a,)) for a in reversed(range(4)))
assert pilot is not None
depth=pilot['depth'];fuel=pilot['fuel'];index=pilot['global_index']
ns='D5.S3.Quantum.Entanglement.EJM'
pilot_source=f'''/- Transient exact original-suffix cost probe, not yet compiled.
The original initial cache and every actual prefix update are retained.
This suffix alone asserts no universal score bound or locality exclusion. -/
import {ns}.EJMOriginalCachedGlobalReplay
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace {ns}.EJMOriginalGlobalSuffixPilot
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (check)
open {ns}.EJMCacheState
open {ns}.EJMPartialBoundData (scale)

private def prefix : Fin {depth} → Fin 4 := ![{','.join(map(str,pilot['prefix']))}]
private def cache : Cache :=
  (List.finRange {depth}).foldl
    (fun cache i => step cache ⟨i.val, by have h := i.isLt; omega⟩ (prefix i))
    initial
private def partial : Partial (Fin 20) (Fin 4) := fun g =>
  if h : g.val < {depth} then some (prefix ⟨g.val, h⟩) else none

set_option trace.profiler true in
private theorem suffix_accepted :
    check EJMOriginalGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale {fuel} ⟨{index}, by decide⟩ cache partial = true := by
  decide +kernel

#print axioms suffix_accepted
end {ns}.EJMOriginalGlobalSuffixPilot
'''
pilot_path=source/'EJMOriginalGlobalSuffixPilot.lean';pilot_path.write_text(pilot_source)
pilot['source']=str(pilot_path);pilot['source_sha256']=hashlib.sha256(pilot_source.encode()).hexdigest()
pilot['status']='prepared_actual_suffix_kernel_cost_probe_not_compiled'
(inputs/'original-global-suffix-pilot.json').write_text(json.dumps(pilot,indent=2)+'\n')
print(json.dumps(dict(records_checked=size,measured_segment_options=plans)),flush=True)
print(json.dumps(pilot),flush=True)

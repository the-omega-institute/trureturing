"""Emit complete original DAG literals under independent Lean module names.

All records retain their native IDs, actual action/pivot payload, actual split
Node and all four earlier children. No acceptance or numeric premise is emitted.
"""
import hashlib
import json
import pathlib
import struct

wt=pathlib.Path(__file__).resolve().parent.parent
source=wt/'D5/S3/Quantum/Entanglement/EJM'
cp=pathlib.Path('/Users/macstudio/omega/.formalization-goal-01a12631/checkpoints/ejm-mdd-global/existing-cover-original-suffix-alignment-20261014')
inputs=cp/'original-source-identity-stream'
checkpoint=(inputs/'stream-checkpoint.txt').read_text().splitlines()
dag=inputs/checkpoint[2]
assert hashlib.sha256(dag.read_bytes()).hexdigest()=='bf188b5ef8d359fc12872297ba3c3db9b633debdec7db6eddf924265c880bf59'
raw=dag.read_bytes();magic,size=struct.unpack_from('<II',raw)
assert magic==0x454a4d32 and size==1558777 and len(raw)==8+24*size
ns='D5.S3.Quantum.Entanglement.EJM'
bits=103
chunk_size=128
chunks_per_module=512
modules=[]
def header(name,digest):
    return f'''/- GID: D5/S3/Quantum/Entanglement/EJM/{name}
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/{name}
   mirror-E: none(waiver:actual-complete-original-dag-input)
   anchors: []
   utility: none
   digest: {digest} -/

/- Untrusted exact certificate input. Source generation and native binding do
not assert Lean acceptance. Actual bound and symmetry predicates must be
checked at every reached partial context of the complete original domain. -/
'''

name='EJMOriginalDAGEncoding'
encoding=header(name,'Balanced literal storage decodes exact complete-original-DAG words without importing local score tables.')+f'''
import Mathlib.Data.Nat.Basic
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace {ns}.{name}

inductive PackedTree where
  | empty
  | node (index word : ℕ) (left right : PackedTree)

def PackedTree.get : PackedTree → ℕ → ℕ
  | .empty, _ => 0
  | .node index word left right, j =>
    if j = index then word else if j < index then left.get j else right.get j

end {ns}.{name}
'''
(source/(name+'.lean')).write_text(encoding);modules.append(name)
chunks=[]
for start in range(0,size,chunk_size):
    packed=0
    for j in reversed(range(start,min(start+chunk_size,size))):
        kind,payload,*children=struct.unpack_from('<6I',raw,8+24*j)
        assert kind<3 and payload<131072 and all(c<2**21 for c in children)
        if kind==0:assert j==0 and payload==0 and children==[0]*4
        if kind==1:assert payload<92160 and children==[0]*4
        if kind==2:assert payload<20 and all(c<j for c in children)
        word=kind+(payload<<2)+sum(c<<(19+21*a) for a,c in enumerate(children))
        assert word<2**bits
        packed=(packed<<bits)|word
    chunks.append(packed)

blocks=[]
for block,start in enumerate(range(0,len(chunks),chunks_per_module)):
    name=f'EJMOriginalDAGBlock{block:02}'
    end=min(start+chunks_per_module,len(chunks))
    def tree(lo,hi):
        if lo==hi:return '.empty'
        mid=(lo+hi)//2
        return f'(.node {mid} 0x{chunks[mid]:x} {tree(lo,mid)} {tree(mid+1,hi)})'
    text=header(name,'Original DAG records retain exact native IDs, action pivots, split Nodes and all four children.')+f'''
import {ns}.EJMOriginalDAGEncoding
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option linter.style.longLine false
namespace {ns}.{name}
open {ns}.EJMOriginalDAGEncoding

@[noinline] def chunks : PackedTree :=
  {tree(start,end)}

end {ns}.{name}
'''
    (source/(name+'.lean')).write_text(text);modules.append(name)
    blocks.append(dict(module=name,first_chunk=start,end_chunk=end))

name='EJMOriginalGlobalDAGData'
text=header(name,'The complete original DAG decodes its actual action pivots and natural split Nodes with fuel checks.')
text+='\n'.join(f'import {ns}.{b["module"]}' for b in blocks)+'\n'
text+=f'''import {ns}.EJMGlobalScoreSymmetry
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace {ns}.{name}
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open {ns}.EJMGlobalScoreSymmetry

abbrev Size := {size}

private def packedChunk (index : ℕ) : ℕ :=
'''
for b in blocks[:-1]:
    text+=f'  if index < {b["end_chunk"]} then {b["module"]}.chunks.get index else\n'
text+=f'  {blocks[-1]["module"]}.chunks.get index\n'
text+=f'''
def word (index : ℕ) : ℕ :=
  packedChunk (index / {chunk_size}) / 2 ^ ({bits} * (index % {chunk_size})) % 2 ^ {bits}

/-- A mismatching fuel/record is rejected by the identity cut. Valid splits
use the literal original Node, and never infer a different variable ordering. -/
def nodes (fuel : ℕ) (index : Fin Size) :
    Node Size (Fin 20) (Fin 4) Cut :=
  let w := word index.val
  if w % 4 = 0 then .bound
  else if w % 4 = 1 then
    let payload := w / 4 % 131072
    .symmetry (cutOfTag ⟨payload / 20 % 4608, Nat.mod_lt _ (by decide)⟩
      ⟨payload % 20, Nat.mod_lt _ (by decide)⟩)
  else if w / 4 % 131072 = (21 - fuel) % 20 then
    .split ⟨w / 4 % 131072 % 20, Nat.mod_lt _ (by decide)⟩
      (fun a => ⟨(w / 2 ^ (19 + 21 * a.val) % 2 ^ 21) % Size,
        Nat.mod_lt _ (by decide)⟩)
  else .symmetry (cutOfTag 0 0)

def root : Fin Size := ⟨1558776, by decide⟩

end {ns}.{name}
'''
(source/(name+'.lean')).write_text(text);modules.append(name)
record=dict(status='complete_original_DAG_Lean_source_emitted_pending_kernel',kernel_accepted=False,
    dag_sha256=hashlib.sha256(raw).hexdigest(),records=size,root=1558776,word_bits=bits,
    chunk_size=chunk_size,blocks=blocks,
    modules=[dict(module=m,sha256=hashlib.sha256((source/(m+'.lean')).read_bytes()).hexdigest(),
        bytes=(source/(m+'.lean')).stat().st_size) for m in modules])
(inputs/'original-global-dag-source.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(dict(records=size,modules=len(modules),bytes=sum(x['bytes'] for x in record['modules']))),flush=True)

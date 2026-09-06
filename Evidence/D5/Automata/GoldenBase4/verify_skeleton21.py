"""Check exact correspondence to the total first-return skeleton of PR #5405."""
import json
from pathlib import Path
from verify21 import zeck, oracle

root=Path(__file__).resolve().parent
m=json.loads((root/'machine21.json').read_text())['states']
k=json.loads((root/'skeleton21.json').read_text())
assert k['start']==0 and k['A'][0]==0 and k['F'][0]==0
for q in range(14):
    t=14+k['signature_selection'][q]
    assert m[q]['type']=='R' and m[t]['type']=='T'
    assert m[q]['zero']==k['A'][q]
    assert m[q]['one']==t
    assert m[q]['output']==k['F'][q]
    assert m[t]['zero']==k['J'][q]
    assert m[t]['output']==k['G'][q]
    s=k['signature_selection'][q]
    assert k['signature_output'][s]==k['G'][q]
    assert k['signature_return'][s]==k['J'][q]
assert len(set(zip(k['G'],k['J'])))==7
assert set(k['signature_selection'])==set(range(7))
weights=[1,2]
while weights[-1]<=1 << 3998:weights.append(weights[-1]+weights[-2])
for n in range(2000):
    w=zeck(1 << (2*n),weights);q=0;i=0
    while i<len(w):
        if w[i]=='0':q=k['A'][q];i+=1
        elif i+1<len(w):
            assert w[i+1]=='0'
            q=k['J'][q];i+=2
        else:break
    out=k['G'][q] if i<len(w) else k['F'][q]
    assert out==oracle(1 << (2*n))
report={'status':'PASS','recurrent_rows_checked':14,'used_signatures':7,'canonical_state_cost':21,
        'block_evaluation_power_checks':2000,'lean_transport_theorem_checked':False}
(root/'skeleton_verification21.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))

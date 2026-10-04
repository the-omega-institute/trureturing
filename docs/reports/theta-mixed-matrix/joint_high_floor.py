"""Directed complete high-frequency form lower bound from the joint row."""
import ast
import json
import hashlib
import sys
import flint
from pathlib import Path
from flint import arb, fmpq, ctx

run = Path(__file__).parent
source = (run/'deficit_profile.py').resolve()
tree = ast.parse(source.read_bytes())
stop = next(i for i,node in enumerate(tree.body)
            if isinstance(node,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='best_hi' for t in node.targets))
scope = {'__file__':str(source)}
exec(compile(ast.Module(body=tree.body[:stop],type_ignores=[]),str(source),'exec'),scope)
phi2,upper_s = scope['density_s2'],scope['upper_s']
terms,tail,exterior,CG = (scope[k] for k in ('terms','tail','exterior','CG'))
band_source=run/'derivative-bandwidth-result.json'
band_bytes=band_source.read_bytes()
band=json.loads(band_bytes)


def read_endpoint(item):
    man,e=map(int,item['dyadic'])
    return arb(man)*arb(2)**e


def endpoint(value):
    return {'display':str(value),'dyadic':[str(v) for v in value.man_exp()]}


mlo=read_endpoint(band['m_N_over_2_lower'])
leak=read_endpoint(band['leakage_product_upper'])
coeff=(mlo-CG.upper()).lower()
if not coeff>0:
    raise RuntimeError('Positive scalar coefficient not certified')
GRID=128
best=arb(2)
cells=[]
for j in range(GRID):
    left,right=fmpq(3*j,2*GRID),fmpq(3*(j+1),2*GRID)
    x=arb((left+right)/2,arb((right-left)/2).upper())
    s2=phi2(x)
    sm=s2.sqrt().upper()
    row=arb(0)
    for n,p,w,t in terms:
        row+=w.upper()*sm*(upper_s(x+t)+upper_s(x-t))
    value=(arb(fmpq(1,2))+coeff*s2.lower()-row.upper()-tail).lower()
    best=min(best,value)
    cells.append({'left':str(left),'right':str(right),
                  's2_lower':endpoint(s2.lower()),'s2_upper':endpoint(s2.upper()),
                  'row_upper':endpoint(row.upper()),'joint_floor_lower':endpoint(value)})
outer=(arb(fmpq(1,2))-exterior.upper()).lower()
full=min(best,outer)
high=(full-leak).lower()
result={'scope':'Directed complete even high-frequency form lower bound; no center matrix or RH certificate; no new Lean certification',
        'runtime':{'python':sys.version.split()[0],'python_flint':flint.__version__,'precision_bits':ctx.prec},
        'derivative_source':band_source.name,'derivative_source_sha256':hashlib.sha256(band_bytes).hexdigest(),
        'bandwidth_N':64,'matrix_c':'3/8','grid_boxes':GRID,'radius':'3/2',
        'interior_joint_floor_lower':endpoint(best),'exterior_floor_lower':endpoint(outer),
        'global_joint_floor_lower':endpoint(full),'leakage_product_upper':endpoint(leak.upper()),
        'complete_high_block_floor_lower':endpoint(high),
        'margin_above_matrix_c_lower':endpoint((high-arb(fmpq(3,8))).lower()),
        'passed_joint_2_over_5':bool(full>=arb(fmpq(2,5))),
        'passed_high_above_3_over_8':bool(high>arb(fmpq(3,8))),
        'cells':cells}
(run/'joint-high-floor-result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='cells'}),flush=True)
if not result['passed_joint_2_over_5'] or not result['passed_high_above_3_over_8']:
    raise RuntimeError('Declared joint high-block certificate not obtained')

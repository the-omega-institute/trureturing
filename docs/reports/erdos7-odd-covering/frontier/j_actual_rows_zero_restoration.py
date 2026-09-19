"""Actual J row budgets and complete restored retained375 covering prices."""
from pathlib import Path
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
import argparse
from itertools import product
import sys
sys.dont_write_bytecode = True

def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    obj = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(obj)
    return obj

def require(p, message):
    if not p:
        raise ValueError(message)

def enc(value):
    if isinstance(value, F): return str(value)
    if isinstance(value, dict): return {str(k): enc(v) for k,v in value.items()}
    if isinstance(value, (list, tuple)): return [enc(v) for v in value]
    return value

CERTIFICATE = 'certificates/source_norms/j_actual_rows_zero_restoration.json'
PINS = {'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232', 'frontier/j_face_retained375_survival_heads.py': 'c5d2e171d97d3d21e1b95373e2731c13d067808537c856658e17129ff9ec5c2b', 'frontier/j_face_retained375_heavy_heads.py': 'd3d5b78e394522b9e6f6066f2bdbb711ccbdd4466e216cf5f9a1c9d37d0169ad', 'frontier/second_depth_seven_comparison.py': '5544b70201a721be7ca0dfa92155c4b186235a19f52a5fd85346f85c02cfc950', 'certificates/source_norms/j_face_retained375_heavy_heads.json': '3eb30852d99bf04dcfdf4dd525fdc0b742d7faa683b785b3ce0d625433db2be4', 'profile-notes/71-global-j-k-control-faces-and-exact-escape-gaps.md': '1ba67485969c424f5523b77dd03a0dc0823f82f9d06f4c3dc719e9cfb66024c1', 'profile-notes/116-signed-face-duals-transport-one-shared-finite-source.md': '9bdf7109a369d8da169021d210e58da068529bf005af6d012b7c81d532c7f369', 'profile-notes/130-the-whole-j-face-forces-source-anti-alignment.md': 'a57717f7d0432a2d0365d85b4fa471729e52630fff2be75aafe6b3c4e4db7db7', 'profile-notes/132-the-whole-j-face-has-a-quantitative-surplus-neighborhood.md': '96e9e828e1a6af113a3543e2f85b38ea89591416faa8d3c2fabb2679d7c0efba', 'profile-notes/136-a-whole-j-source-neighborhood-has-a-complete-labelwise-bound.md': '137aacdd1de6890568edc6d0490fe00c7df41e2c1ff35f95c7732d79829e3806', 'profile-notes/219-one-late-source-split-controls-complete-saturated-j-heads.md': '1ab67a37ff16722068d71e186f79619175dea1ba049d65deae7269ba1306c204', 'profile-notes/220-the-assigned-source-losses-share-one-complete-j-error-budget.md': '04acbbe74fcf4a83c8e1b6b0f3ae0542025525101265240eb9588cb0389d6290', 'profile-notes/227-the-actual-deletion-mask-rows-have-one-off-face-error-budget.md': 'fe7d244cf14ee5b0f7f7f41efeb8ad3cfd61ee41a7c60ed712361cbf88a68c5e', 'profile-notes/244-three-complete-j-heads-share-raw-survivor-and-marked-deletion.md': '47ee1f78c3b5c2e4163d433aac3d1f9cd21955c9c6fd494938fa3b743e30565e', 'profile-notes/251-two-retained-original-tests-sharpen-the-complete-j-heads.md': '92d00b93193b8a06da4c30921c91cf77b8bfe6d1c38f3ee846a37d73142d7d88', 'profile-notes/256-a-second-seven-depth-sharpens-the-complete-retained-j-heads.md': 'f1f9ef68d15df741b23c880d877d3afe1e2fc6435490d0702da53b43f3a17a3b', 'profile-notes/264-seven-retained-states-and-two-seven-depths-control-complete-j-heads.md': 'f2ace79a9ad70bb57b36f3fdd66e72552bff4787811f5d721fc1f79585b20c7f', 'profile-notes/288-retaining375-strengthens-the-complete-j-survival-hinge.md': '471e21713ee2ced6488fe0c3385450594f80fb1ba771e86ae1e8a7d723d9474f', 'profile-notes/296-joint-positive175189-strengthens-the-complete-j-survival-hinge.md': '8026a540ec18d4d6fc018f3b1a7afe212f183a20160c9a3dd9126288ae20b6a7', 'profile-notes/298-retaining375-certifies-the-complete-heavy-cost.md': '30d84967f20bfba68142c83574a78f20224e5b933742cb7de215e5f685303e9d'}

def calculate(B):
    io = load('zero_transport_io', B/'certificate_io.py')
    for rel, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(B/rel)).hexdigest() == pin, 'Pinned mathematical source '+rel)
    provider = load('zero_transport288', B/'frontier/j_face_retained375_survival_heads.py')
    data = provider.make_extended_model(B)
    lp, codec = data['lp'], data['codec']
    path = B/'certificates/source_norms/j_face_retained375_heavy_heads.json'
    raw = io.read_artifact_bytes(path)
    doc = json.loads(raw)
    proof = doc['proof_data']
    require(data['model'] == doc['model'], 'Exact original288 matrix')
    require(lp.nvars == 12941 and len(lp.rows) == 30454 and len(lp.equalities) == 20,
            'Whole original row/column domain')

    def unbatch(parts):
        out = []
        for part in parts:
            require(part['start'] == len(out) and part['stop'] == len(out)+len(part['rows']),
                    'Contiguous established proof rows')
            out.extend(part['rows'])
        return out

    bounds = {}
    steps = []
    for step in unbatch(proof['zero_induction_batches']):
        kind, sign, index = step['kind'], step['sign'], step['row']
        require(kind in ('inequality', 'equality'), 'Original row kind')
        rows, rhs = (lp.rows, lp.rhs) if kind == 'inequality' else (lp.equalities, lp.erhs)
        require(sign in ((1,) if kind == 'inequality' else (1,-1)) and rhs[index] == 0,
                'Permitted zero-right-side row orientation')
        row = {j: sign*a for j,a in rows[index].items()}
        negative = sorted(j for j,a in row.items() if a < 0)
        require(negative == step['negative_antecedents'] and set(negative) <= bounds.keys(),
                'Every negative coordinate already quantitatively bounded')
        new = sorted(j for j,a in row.items() if a > 0 and j not in bounds)
        require(new == step['new_zero_columns'], 'No extra column removed')
        budget = 1 + sum(-row[j]*bounds[j] for j in negative)
        for j in new:
            bounds[j] = budget/row[j]
            require(bounds[j] > 0, 'Positive exact perturbation bound')
        steps.append({'kind':kind,'row':index,'sign':sign,'budget':budget,'new_columns':new})
    require(len(bounds) == 4634 and len(steps) == 2645, 'Whole original strong-zero induction')
    slope = F(doc['complete_late_slope'])
    require(slope == F(403,8), 'Original complete heavy hinge slope')
    co = {int(t):F(a) for t,a in doc['original_coefficients'].items()}
    require(set(co) == set(range(1,9)) and all(a>0 for a in co.values()) and sum(co.values()) == slope,
            'Original nonnegative complete hinge combination')
    # H(v)<=14L for1<=v<=14. Raw increment g(v) is nonnegative,
    # nondecreasing and bounded by L*(6/35*5+6/245*5+1/245)<L.
    # Consequently every original or coordinatewise-max physical coefficient
    # is <=14L, including OU/OV and NU/NV increments. Profile coefficients=0.
    raw_ratio = F(6,35)*5+F(6,245)*5+F(1,245)
    require(raw_ratio < 1, 'Whole raw increment bound')
    coefficient_bound = 14*slope
    restoration = coefficient_bound*sum(bounds.values())
    uniform_restoration = restoration
    # Same six physical categories as the established full298 objective. Every
    # original head has1<=b<=6, and each independent depth has0<=m,e<=4.
    hs = {v:sum(a*max(v-k,0) for k,a in co.items()) for v in range(1,15)}
    gs = {(m,e):{v:sum(a*data['depth'].seven_increment(k,v,m,e) for k,a in co.items())
                  for v in range(1,15)} for m,e in product(range(5), repeat=2)}
    specs = {}
    def put(col, spec):
        require(col not in specs and 0<=col<12941, 'Unique full original objective column')
        specs[col] = spec
    for cell, mask in product(range(25),range(16)):
        k=16*cell+mask; q=mask.bit_count()
        put(k,('X',q,0)); put(425+k,('Y',q,0))
        for state in range(1,8):
            n=state.bit_count()
            put(data['triple'].U+400*(state-1)+k,('OU',q,n))
            put(data['triple'].V+400*(state-1)+k,('OV',q,n))
        for state in range(8):
            n=state.bit_count()
            put(6531+400*state+k,('NU',q,n)); put(9731+400*state+k,('NV',q,n))
    require(len(specs)==12800, 'Whole physical objective inventory')
    for col in set(range(12941))-specs.keys():specs[col]=('profile',0,0)
    def coefficient(spec,b,m,e):
        kind,q,n=spec;v=b+q;g=gs[m,e]
        if kind=='X':return g[v]
        if kind=='Y':return hs[v]
        if kind=='OU':return g[v+n]-g[v]
        if kind=='OV':return hs[v+n]-hs[v]
        if kind=='NU':return g[v+n+1]-g[v+n]
        if kind=='NV':return hs[v+n+1]-hs[v+n]
        require(kind=='profile','Known objective category');return F(0)
    caps={}
    for spec in set(specs.values()):
        values=[coefficient(spec,b,m,e) for b,m,e in product(range(1,7),range(5),range(5))]
        require(min(values)>=0 and max(values)<=coefficient_bound,
                'Each complete coefficient lies in its uniform nonnegative envelope')
        caps[spec]=max(values)
    restoration=sum(bounds[col]*caps[specs[col]] for col in bounds)
    require(0<restoration<=uniform_restoration,'Category restoration strengthens the full uniform price')
    # These are arithmetic relaxations of the ordinary common-measure proof,
    # with coordinates delta,E5,E15,E5d,E15d,E3,omega and sumE<=rho+7delta/36.
    row_prices={
        'raw25':([F(19,36),5,0,0,0,0,0],6),
        'density':([1,10,10,0,0,0,1],11),
        'e3_root1':([0,0,0,0,0,3,0],3),
        'e3_slot':([F(1,72),F(2,9),0,0,0,4,0],5),
        'e5_cell':([F(1,450),0,0,1,5,0,0],6),
        'marked27_81':([F(901,900),10,10,1,5,0,1],17),
        'marked25_75':([F(361,360),F(91,9),10,0,0,7,1],19),
        'pretable':([F(1,36),F(20,27),0,0,0,0,0],1)}
    row_checks={}
    for name,(values,claimed) in row_prices.items():
        values=list(map(F,values));c=max(values[1:]);slope_bound=max(c,values[0]+F(7,36)*c)
        require(slope_bound<=claimed,'Shared actual defect budget for '+name)
        row_checks[name]={'prices':values,'exact_slope':slope_bound,'containing_slope':claimed}
    t=F(1,1000)
    require(t/72<F(1,675) and 5*t+t/72<F(1,135),'Original135 common-cell guards')
    require((2+2*t)/(1-t)<=3 and F(331,360)<=1,'Wrong-root and actual mass guards')

    bank = codec.decode_dual_bank(proof['encoded_covering_duals'], inequality_count=30454,equality_count=20)
    seed = codec.decode_dual_bank(proof['encoded_prefix_seed_duals'], inequality_count=30454,equality_count=20)

    def price(dual):
        ys = [F(v) for v in dual['nonzero_inequality_duals'].values()]
        zs = [F(v) for v in dual['equality_duals']]
        require(all(y>=0 for y in ys) and len(zs)==20, 'Valid signed price domain')
        return sum(ys)+sum(map(abs,zs))

    prices = {key:price(dual) for key,dual in bank.items()}
    seedprices = {key:price(dual) for key,dual in seed.items()}
    nodes = unbatch(proof['covering_node_batches'])
    require(len(nodes)==1177 and len(bank)==981 and len(seed)==50,
            'Complete existing covering and seed banks')
    require({node['dual_id'] for node in nodes} == set(bank), 'All existing covering nodes priced')
    maxkey = max(prices, key=prices.__getitem__)
    maxseed = max(seedprices, key=seedprices.__getitem__)
    result = {'schema':'erdos7-j-actual-rows-zero-restoration-v1',
              'source_sha256':PINS,
              'model':doc['model'], 'hypothesis':'x>=0; every original inequality residual and absolute equality residual <=r',
              'zero_columns':len(bounds),'zero_rows':len(steps),
              'column_bound_batches':[{'start':i,'stop':min(i+128,len(bounds)),
                                       'rows':sorted(bounds.items())[i:i+128]}
                                      for i in range(0,len(bounds),128)],
              'maximum_column_bound':max(bounds.values()),'sum_column_bounds':sum(bounds.values()),
              'original_objective_coefficient_bound':coefficient_bound,
              'uniform_restoration_price':uniform_restoration,'restoration_price':restoration,
              'objective_specification_caps':{'/'.join(map(str,k)):v for k,v in sorted(caps.items())},
              'row_residual_arithmetic':row_checks,'covering_node_count':len(nodes),
              'covering_dual_count':len(bank),'maximum_covering_price':prices[maxkey],
              'maximum_covering_key':maxkey,'maximum_seed_price':seedprices[maxseed],
              'maximum_seed_key':maxseed,'complete_covering_error_price':prices[maxkey]+restoration,
              'row_error_100t_covering_price':100*(prices[maxkey]+restoration),
              'scope':'Conditional error for all1177 existing covering nodes and50 seeds. Full original columns restored. The fixed face tail constant has not been transported. No full prefix/tail/basis transport or numerical J radius, no new LP, no Lean result.'}
    return enc(result)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[1])
    parser.add_argument('--certificate',type=Path)
    parser.add_argument('--output',type=Path)
    parser.add_argument('--write',action='store_true')
    parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    require(not(args.write and args.check),'Choose writing or checking')
    B=args.base.resolve();io=load('actual_j_rows_cli_io',B/'certificate_io.py')
    result=calculate(B)
    if args.write:
        io.write_certificate_text(args.output or B/CERTIFICATE,json.dumps(result,indent=2)+'\n')
    else:
        old=json.loads(io.read_artifact_bytes(args.certificate or B/CERTIFICATE))
        require(result==old,'Complete row/restoration certificate regenerated exactly')
    print('PASS: actual J row arithmetic;4634 restored columns;1177 covering nodes and50 seeds')
    print('Conditional restored covering price per row error:',float(F(result['complete_covering_error_price'])))


if __name__=='__main__':main()

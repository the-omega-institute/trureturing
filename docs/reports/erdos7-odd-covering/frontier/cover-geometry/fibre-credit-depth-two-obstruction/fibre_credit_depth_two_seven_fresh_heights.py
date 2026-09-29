#!/usr/bin/env python3
"""Recompile and execute the exact seven-direction enclosure, then check its budget.

The ordinary source and carving proofs remain inherited mathematical premises.
All native large-integer expressions have a checked static range, with UBSan
abort enabled. Only an explicit temporary build directory is used.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
from math import prod
from hashlib import sha256
import argparse,json,runpy,shutil,subprocess,tempfile
FIXED={'capacities': [28, 30, 36, 40, 42, 46, 52], 'thresholds': [1, 8, 10, 12, 16, 20, 24, 32, 40, 48], 'coefficient_denominator': 100, 'unary_hinge_coefficient_numerators': [[0, 17433, 0, 60373, 42972, 0, 0, 0, 0, 0], [0, 12486, 0, 48905, 43923, 0, 0, 0, 0, 0], [0, 13379, 0, 23152, 1976, 22346, 36800, 0, 0, 0], [0, 7808, 0, 6200, 25538, 0, 43974, 0, 0, 0], [0, 5254, 0, 2173, 20259, 0, 52573, 0, 0, 0], [0, 6900, 0, 0, 6653, 10259, 23239, 38770, 0, 0], [0, 0, 0, 4597, 0, 3250, 19992, 42974, 0, 0]], 'kappa': '1/100000', 'target': 15050, 'Y_knots': [1, 8, 10, 12, 16, 20, 24, 32, 40, 48, 64, 80, 96, 128, 160, 192, 256, 384], 'pair_penalty': 'Y-chord square', 'triple_penalty_weight': '1/24', 'higher_support_min_size': 4, 'higher_support_mean_coefficient': 1931112, 'unary_expected_cost': '2817942055817788/288377958375', 'total_expected_cost': '3755372306935950419/252330713578125', 'target_minus_cost': '42204932414830831/252330713578125', 'outside_unary_lower': '426784/25'}
DEPENDENCIES={'fibre_credit_depth_two_conditioned_convex_source.py': '4bf5f7610dc21b0b410074d54ee23f7d10a2d08c0c726c1827adad1da3bab251', 'fibre_credit_depth_two_conditioned_convex_source.json': '2b74e5eb1fbcacf2b9f9493affdc1df9ff17af6c8096df46a23d678d491df8a3', 'fibre_credit_depth_two_seven_fresh_heights.cpp': 'ea3bc5620689abdf27ccc8ef855a27ece9527cf3a99fb149602d218aea1b6691'}


def require(ok,msg):
    if not ok:raise RuntimeError(msg)


def integer_envelope():
    r=FIXED['capacities'];rows=FIXED['unary_hinge_coefficient_numerators']
    total=sum(map(sum,rows));E=819200000;steps=8192;v=384;contexts={}
    for den in (256,512):
        u=tuple(x*den for x in r)
        pair=tuple(prod(u[i] for i in J) for J in combinations(range(7),5))
        triple=tuple(prod(u[i] for i in J) for J in combinations(range(7),4))
        derivative=prod(u)+den**2*sum(pair)*v+den**3*sum(triple)*v
        value=24*steps*derivative+E*den**7*(24*21+35)*v**2
        bounds={'coordinates_and_differences':2*max(u),'products_and_volume':prod(u),
                'pair_sum':sum(pair)*v,'triple_sum':sum(triple)*v,
                'derivative_absolute':derivative,'value_absolute':value,
                'vertex_numerator':max(steps*max(pair),24*steps*max(triple)),
                'vertex_denominator':E*den**5,'denominator_power':den**7}
        if den==256:
            line=sum(sum(row)*(x*den+48*den) for row,x in zip(rows,r))
            bounds.update(unary_line_absolute=line,
                          gate_lhs_absolute=line*24*E*den**6+100*value,
                          gate_rhs=15050*2400*E*den**7,
                          cheap_gate=max(24*total*max(u)+53900*den,15050*2400*den))
        require(max(bounds.values())<2**127,'every signed128 intermediate bound in context '+str(den))
        contexts[str(den)]={k:str(x) for k,x in bounds.items()}
    small=max(30000000,total*48,2*52*512,E,15050*2400*256)
    require(small<2**63,'all signed64 temporaries')
    return {'contexts':contexts,'small_temporary_bound':small,
            'signed128_bound_passed':True,'center_is_not_multiplied_by_corner_factor100':True}


def calculate():
    directory=Path(__file__).resolve().parent
    for name,digest in DEPENDENCIES.items():
        require(sha256((directory/name).read_bytes()).hexdigest()==digest,'pinned seven-direction dependency: '+name)
    api=runpy.run_path(str(directory/'fibre_credit_depth_two_conditioned_convex_source.py'))
    source=json.loads(json.dumps(api['calculate']()))
    require(source==json.loads((directory/'fibre_credit_depth_two_conditioned_convex_source.json').read_text()),'replayed conditioned source result')
    bounds=integer_envelope()
    compiler=shutil.which('c++')
    require(compiler is not None,'C++17 compiler is required for exact native replay')
    flags=['-std=c++17','-O2','-fsanitize=undefined','-fno-sanitize-recover=all']
    with tempfile.TemporaryDirectory(prefix='e7_seven_native_',dir='/tmp') as tmp:
        exe=Path(tmp)/'enclosure'
        built=subprocess.run([compiler,*flags,str(directory/'fibre_credit_depth_two_seven_fresh_heights.cpp'),'-o',str(exe)],capture_output=True,text=True)
        require(built.returncode==0,'native verifier compilation: '+built.stderr)
        executed=subprocess.run([str(exe)],capture_output=True,text=True)
        require(executed.returncode==0,'native exact enclosure: '+executed.stderr)
        raw=json.loads(executed.stdout)
    f=FIXED;r=f['capacities'];rows=f['unary_hinge_coefficient_numerators'];ts=f['thresholds']
    require(raw['parameters']=={'grid_denominator':256,'lambda_steps':8192,'lambda_denominator':819200000,
            'target':15050,'capacities':r,'knots':f['Y_knots'],'thresholds':ts,'coefficients':rows},'native parameters match fixed dual and overflow envelope')
    require(all(c>=0 for row in rows for c in row),'convex nonnegative hinge penalties')
    require(raw['complete'] and raw['nodes']==2*raw['leaves']-1,'complete binary enclosure')
    require(raw['leaves']==sum(raw['depths'].values())==sum(raw['branches'].values()),'all accepted leaf counters')
    require(int(raw['volume'])==int(raw['full_volume'])==prod((x-1)*256 for x in r),'exact full seven-dimensional volume')
    Y=[(F(row['probability']),row['value']) for row in source['Y']]
    require(sum(p for p,_ in Y)==1 and [1]+[v for _,v in Y]==f['Y_knots'],'one comparison law')
    beta=[sum(p*max(v-t,0) for p,v in Y) for t in ts]
    G1=sum(p*v for p,v in Y);G2=sum(p*v*v for p,v in Y)
    unary=sum(F(c,100)*b for row in rows for c,b in zip(row,beta))
    hcoef=sum(prod(r[i]-1 for i in J) for k in range(4) for J in combinations(range(7),k))
    cost=unary+F(539,24)*G2+F(hcoef,100000)*G1
    require(str(cost)==f['total_expected_cost'] and hcoef==1931112,'common-source exact cost')
    exterior=min(sum(F(c,100)*max(r[i]-t,0) for c,t in zip(rows[i],ts)) for i in range(7))
    require(exterior>f['target'],'complete exterior controlled by unary penalties')
    EW=100000*(f['target']-cost);density=F(104726,6084351)*EW/prod(r)
    require(EW>0 and density>F(1,500000),'actual positive Haar reserve')
    max_pair=max(F(prod(r[i]-1 for i in range(7) if i not in J),100000) for J in combinations(range(7),2))
    max_triple=max(F(24*prod(r[i]-1 for i in range(7) if i not in J),100000) for J in combinations(range(7),3))
    require(max_pair<1285 and max_triple<1285,'conditional unbounded mixed-field extension slope')
    return {'scope':'Ordinary full-ICX seven-direction proof with recompiled exact native enclosure; old shallow exponents retained, no new Lean verification.',
            'fixed_penalties':FIXED,'dependency_hashes':DEPENDENCIES,'source_arithmetic_replayed':True,
            'native_full_enclosure':raw,'integer_envelope':bounds,'native_compile_flags':flags,
            'grid_denominator':256,'lambda_steps':8192,'target':f['target'],
            'unary_cost':str(unary),'higher_mean_coefficient':hcoef,'total_cost':str(cost),
            'target_minus_cost':str(f['target']-cost),'mean_W_lower':str(EW),
            'Haar_lower':str(density),'Haar_lower_decimal':float(density),'simple_Haar_lower':'1/500000',
            'outside_unary_lower':str(exterior),'max_pair_conjugate_argument':str(max_pair),
            'max_triple_conjugate_argument':str(max_triple),'conditional_unbounded_field_slope':1285}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    result=calculate();rendered=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output is None:
        require(json.loads(Path(__file__).resolve().with_suffix('.json').read_text())==result,'retained result agrees with seven-direction native enclosure')
        print(rendered,end='')
    else:args.output.write_text(rendered)


if __name__=='__main__':main()

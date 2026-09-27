"""Complete squared-load counterexamples to universal common CRT-center reduction."""
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations, product
from math import gcd, lcm, prod
from pathlib import Path
import importlib.util
import json
import sys
import time
sys.dont_write_bytecode=True
_spec=importlib.util.spec_from_file_location('shared_phase_io',Path(__file__).with_name('adaptive_phase_io.py'))
_io=importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_io)
require=_io.require

CERTIFICATE='certificates/source_norms/source-budgets/common_center_counterexample.json'
SOURCES=('certificate_io.py', 'frontier/source-budgets/adaptive_phase_io.py', 'problem-details/66-shared-phase-triangles-and-common-center-obstruction.md', 'frontier/source-budgets/common_center_counterexample_input.json')

def enumerate_square_load(moduli, weights):
    """All fixed class layouts for nonnegative integer mass on Z/lcm(moduli)."""
    moduli=tuple(moduli);weights=tuple(weights)
    n=lcm(*moduli)
    require(len(weights)==n and all(type(w) is int and w>=0 for w in weights),
            'complete nonnegative integer measure on the common residue space')
    require(all(type(m) is int and m>1 for m in moduli),'positive nonunit class moduli')
    rows=[]
    for residues in product(*(range(m) for m in moduli)):
        value=sum(w*(1+sum(x%m==a for m,a in zip(moduli,residues)))**2
                  for x,w in enumerate(weights))
        rows.append({'residues':list(residues),'value':value})
    values={tuple(r['residues']):r['value'] for r in rows}
    common=[values[tuple(x%m for m in moduli)] for x in range(n)]
    best=max(values.values());restricted=max(common);W=sum(weights)
    require(W>0,'positive total mass')
    return {'weights':list(weights),'total_weight':W,'support_size':sum(w>0 for w in weights),
            'full_layout_count':len(rows),'common_center_count':len(common),
            'unrestricted_max':best,'common_center_max':restricted,'gap':best-restricted,
            'unrestricted_argmax':[list(a) for a,v in values.items() if v==best],
            'common_center_argmax':[x for x,v in enumerate(common) if v==restricted],
            'normalized_unrestricted_max':str(F(best,W)),
            'normalized_common_center_max':str(F(restricted,W)),
            'normalized_gap':str(F(best-restricted,W)),
            'selected_terms_max':best-W,'selected_terms_common_center_max':restricted-W,
            'layout_scores':rows,'common_center_scores':common}


def grid_value(weights, a, b, t):
    """Independent expansion for a 3 by 5 CRT table."""
    at=next(x for x in range(15) if x%3==a and x%5==b)
    R=sum(w for x,w in enumerate(weights) if x%3==a)
    C=sum(w for x,w in enumerate(weights) if x%5==b)
    return sum(weights)+3*R+3*C+2*weights[at]+weights[t]*(3+2*(t%3==a)+2*(t%5==b))


def calculate(base):
    ctx=_io.Context(base,SOURCES,__file__)
    data=ctx.read('frontier/source-budgets/common_center_counterexample_input.json')
    require(data['modulus']==15 and data['class_moduli']==[3,5,15] and data['uniform_shifts']==[0,1],
            'stated CRT counterexample and its strictly positive shift')
    weights=data['weights'];records=[]
    for shift in data['uniform_shifts']:
        current=[w+shift for w in weights]
        record=enumerate_square_load(data['class_moduli'],current)
        require(all(r['value']==grid_value(current,*r['residues']) for r in record['layout_scores']),
                'all direct scores agree with the independent row-column expansion')
        record['uniform_shift']=shift;records.append(record)
    first,positive=records
    require((first['total_weight'],first['unrestricted_max'],first['common_center_max'])==(12,63,60),
            'six-support exact counterexample')
    require((positive['total_weight'],positive['unrestricted_max'],positive['common_center_max'])==(27,109,108),
            'strictly positive exact counterexample')
    require(first['unrestricted_argmax']==positive['unrestricted_argmax']==[[0,0,10]],
            'unique unrestricted maximizer of both measures')
    uniform=[]
    for original,shifted in zip(first['layout_scores'],positive['layout_scores']):
        a,b,t=original['residues'];increment=shifted['value']-original['value']
        require(increment==44+2*(t%3==a)+2*(t%5==b),'uniform shift formula for every layout')
        uniform.append(increment)
    require(min(positive['weights'])>0 and all(r['gap']>0 for r in records),
            'common-center restriction fails even for a strictly positive probability law')
    case_rows=[]
    for a in range(3):
        for columns in ((0,),(1,2,3,4)):
            maxima=[];common=[]
            for b in columns:
                maxima.append(max(grid_value(weights,a,b,t) for t in range(15)))
                t=next(x for x in range(15) if x%3==a and x%5==b)
                common.append(grid_value(weights,a,b,t))
            require(len(set(maxima))==len(set(common))==1,'all columns in each displayed case agree')
            case_rows.append({'row':a,'columns':list(columns),'unrestricted_max':maxima[0],
                              'common_center_value':common[0]})
    return ctx.finish({'schema':'common-center-counterexample-v1','status':'PASS',
                       'modulus':15,'class_moduli':data['class_moduli'],'records':records,
                       'row_column_cases':case_rows,'uniform_shift_min':min(uniform),
                       'uniform_shift_max':max(uniform),'scope':data['scope']})


if __name__=="__main__":
    _io.run(CERTIFICATE,calculate,__file__)

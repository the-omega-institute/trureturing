"""Exact same-source consequences of the refined20-leaf source mass.

Reuse779's complete capped factor arithmetic and780's exact upper-quantile
and conditional-cap arithmetic. The new source mass1/11250 is supplied by
e7_refined_capped_source, not inferred from a comparison measure.
"""
import argparse
from fractions import Fraction as F
import json
from math import prod
from pathlib import Path
import runpy

M8=F(1,11250)
M9=F(1,750000)
EXPECTED=((3,F(1,2),F(1)),(5,F(3,4),F(1)),(7,F(1),F(3,2)),
          (11,F(1),F(5,3)),(13,F(1),F(3,2)),(17,F(1),F(2)),
          (19,F(1),F(9,5)),(23,F(1),F(11,5)))


def need(condition,message):
    if not condition:raise ValueError(message)


def calculate(base,bridge):
    need(base['FACTORS']==EXPECTED and base['SOURCE_MASS']==F(1,33750),
         'Same original anchor/cap interface; strengthened mass is supplied separately')
    need(bridge['LIMIT']==640,'Complete finite atom window resolves declared trim operations')
    raw={k:prod(bridge['factor_moment'](p,a,c,k)for p,a,c in EXPECTED)for k in(1,2,4)}
    need(raw[4]==base['full_fourth'](),'Inherited infinite fourth moment agrees')
    atoms=base['finite_atoms'](640)
    a8,k8,c8=bridge['trim'](atoms,F(3,8),raw,M8)
    need(c8['cutoff']==144,'Strengthened-source upper-mass cutoff144')
    mean=k8[1]/M8
    need(196<mean<198,'Reference prime197 fails this mean test and199 passes')
    safe8=F(634300)
    need(k8[4]<safe8,'Full mixed fourth query bound below634300')
    tau8=base['tail_allowance'](5500,7);margin8=M8-safe8*tau8
    need(margin8>F(1,1000000),'Every finite tail above5500 retains positive mass')
    q,delta,cap=199,F(8,11),F(11,3)
    threshold=delta*(q-1)
    need(threshold==144 and cap==1/(1-delta)and cap<=q,'Legal normalized199 clipping kernel')
    sl=bridge['stoploss'](a8,M8,k8[1],threshold)
    need(sl==k8[1]-144*M8,'All upper comparison mass is at loads at least144')
    actual=M8-sl/((1-delta)*(q-1))
    need(actual>M9,'One actual ninth source has enough mass before fixed global scaling')
    ap,kp=bridge['append_cap'](a8,k8,q,cap)
    a9,k9,c9=bridge['trim'](ap,M8,kp,M9)
    need(c9['cutoff']==480,'Ninth-source upper-mass cutoff480')
    safe9=F(577300)
    need(k9[4]<safe9,'Ninth complete mixed fourth query bound below577300')
    tau9=base['tail_allowance'](18000,8);margin9=M9-safe9*tau9
    need(margin9>F(1,5000000),'Every finite tail above18000 retains positive mass')
    interval=bridge['interval']
    return {
      'premise':'Same actual eight-prime source has mass>=1/11250 by the20-leaf refinement; '
                '779 full conditional-cap comparison and transport,780 normalized clipping,734 analytic tail.',
      'eight_head':{'mass':M8,'upper_quantile':c8,'mean':interval(mean),
                    'complete_moments':{str(k):interval(v)for k,v in k8.items()},
                    'safe_fourth':safe8,'tail_cutoff':5500,'ell':7,
                    'tail_allowance':tau8,'distorted_mass_lower':margin8,
                    'strict_simple_lower':F(1,1000000),
                    'scope':'At most8 original support primes<=5500; arbitrary finite larger support and all heights.'},
      'ninth_bridge':{'prime':q,'threshold':threshold,'delta':delta,'cap':cap,
                      'actual_mass_lower':interval(actual),'prescribed_mass':M9,'upper_quantile':c9,
                      'complete_moments':{str(k):interval(v)for k,v in k9.items()},
                      'safe_fourth':safe9,'tail_cutoff':18000,'ell':8,
                      'tail_allowance':tau9,'distorted_mass_lower':margin9,
                      'strict_simple_lower':F(1,5000000),
                      'scope':'At most8 original support primes<199 and at most9<=18000; '
                              'arbitrary finite larger support and all heights.'},
      'comparison_coefficients_are_not_physical_independence':True,
      'all_queries_use_one_source_before_query_selection':True,
      'original_phase_and_complete_label_accounting':'As in779/780; completion preserves original covered-set containment.',
      'infinite_comparison_tails_included':True,'lean_verification':False,
    }


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parent.parent/'fibre-credit-depth-two-obstruction/capped_anchor_quantile_tail.py')
    parser.add_argument('--bridge',type=Path,default=Path(__file__).resolve().parent.parent/'fibre-credit-depth-two-obstruction/ninth_271_quantile_tail.py')
    parser.add_argument('--source-result',type=Path,default=Path(__file__).with_name('refined_capped_source.json'))
    parser.add_argument('--write-result',type=Path)
    args=parser.parse_args()
    source=json.loads(args.source_result.read_text())
    need(source['guaranteed_same_source_mass']==str(M8) and source['baseline_count']==28001
         and source['unchanged_count']==27981 and source['refined_count']==20
         and source['guaranteed_integer_surplus']==12
         and source['conditional_caps']==[[p,str(c)] for p,a,c in EXPECTED[2:]],
         'Same refined-source mass and conditional caps; source-case proof is checked separately')
    bridge=runpy.run_path(str(args.bridge))
    base=bridge['load_base'](args.base)
    result=json.loads(json.dumps(calculate(base,bridge),default=str))
    if args.write_result:args.write_result.write_text(json.dumps(result,indent=2)+'\n')
    else:need(result==json.loads(Path(__file__).with_suffix('.json').read_text()),'Exact retained arithmetic equals fresh computation')
    print(json.dumps({'source_mass':result['eight_head']['mass'],'eight_head_tail_cutoff':5500,
                      'ninth_reference_prime':199,'ninth_head_tail_cutoff':18000,
                      'strict_mass_bounds':['1/1000000','1/5000000'],'lean_verification':False},indent=2))

if __name__=='__main__':main()

"""Two separate initial profiles retaining all first-depth grouped roles.

All inputs are explicit. Load definitions only; no dependency main, finite
control, or prime continuation is executed. Canonical source weights are
used only to recover their actual addresses and selected-root assignments.
Actual profile masses are the literal depth-two Haar row masses.
"""
import argparse
from collections import defaultdict
from fractions import Fraction as F
import hashlib
import json
from math import prod
from pathlib import Path
import runpy


def source_roles(source, name, require):
    private = (11,13,17,19,23,29,31,37,41)
    require(tuple(source['private_primes']) == private, 'canonical private coordinate order')
    expected_first = [[2,0,3,3],[2,2,4,4],[1,1,2,2],[3,3,2,2],
                      [2,2,1,5],[1,3,1,1],[1,3,1,5],[1,2,4,4],[1,2,4,5]]
    expected_rows = expected_first if name == 'FC110' else source['final_rows']
    masks = source['masks'] if name == 'FC110' else source['final_masks']
    require(masks == [510,0], 'declared selected-root masks')
    rows, roles = [], {}
    for qi,q in enumerate(private):
        row, role = [], {}
        for hi,p in enumerate((5,7)):
            raw = source['private_sources'][str(q)][str(p)]
            free = [F(x) for x in raw['free']]
            require(len(free) == p and sum(x != 0 for x in free) == 1,
                    'one fixed physical free address')
            free_row = next(i for i,x in enumerate(free) if x)
            require(free[free_row] == F(1,q-2), 'source token amplitude used only for address')
            selected = {r:[F(x) for x in raw['selected_increment'][str(r)]] for r in (1,2)}
            nonzero = [(r,i,x) for r,v in selected.items() for i,x in enumerate(v) if x]
            require(all(len(v) == p for v in selected.values()) and len(nonzero) == 1,
                    'one actual selected address and root')
            root, selected_row, value = nonzero[0]
            require(value == F(1,q-2), 'selected source token amplitude')
            require(root == (1 if masks[hi] & (1 << qi) else 2), 'root mask agrees with raw source')
            row.extend((free_row,selected_row))
            role[p] = {'free_row':free_row,'selected_row':selected_row,'selected_root':root}
        rows.append(row)
        roles[q] = role
    require(rows == expected_rows, 'actual raw addresses agree with the declared source table')
    return roles,rows,masks


def head_rows(p, root):
    rows = [F(1,p) for _ in range(p)]
    rows[p-1] = F(0)
    rows[p-2] -= F(1,p*p)
    if (p,root) in ((5,1),(7,2)):
        rows[0] = F(0)
        rows[1] -= F(1,p*p)
    return rows


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--first-source',type=Path,required=True)
    parser.add_argument('--second-source',type=Path,required=True)
    parser.add_argument('--arithmetic-library',type=Path,required=True)
    parser.add_argument('--coloured-library',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args()
    lib = runpy.run_path(str(args.arithmetic_library),run_name='profile_arithmetic_library')
    coloured = runpy.run_path(str(args.coloured_library),run_name='coloured_profile_library')
    require,factor_moments,snapshot,trim = (
        lib[n] for n in ('require','factor_moments','snapshot','trim'))
    primes,orders,limit = lib['PRIMES'][1:],lib['ORDERS'],lib['LIMIT']
    private = primes[2:]
    require(primes == (5,7,11,13,17,19,23,29,31,37,41), 'fixed nonternary primes')
    require(orders == (0,1,2,4) and limit == 256, 'fixed complete moments and low inventory')
    h = 1/lib['D0']
    require(h == F(36518862868606981,1816999451688960000), 'unchanged actual source mass')
    base_atoms,base_moments,allowed,base_patterns,base_cells = coloured['build_coloured_profile'](
        lib,{p:F(1,p)+F(1,p*p) for p in primes},h)
    zero = {r:{p:allowed[r][p]-F(1,p) for p in primes} for r in (1,2)}
    heads = {r:{p:head_rows(p,r) for p in (5,7)} for r in (1,2)}
    for r in (1,2):
        for p in (5,7):
            require(sum(heads[r][p],F(0)) == allowed[r][p], 'literal n2 head row mass')
    positive_moments = {
        p:[m-F(p-1,p) for m in factor_moments(p,F(1),F(1))] for p in primes}
    ternary_long = [m-F(2,3) for m in factor_moments(3,F(1),F(1))]
    # Only patterns with both head runs zero can change. Reuse the ordinary
    # positive-product load convolution, once for both actual source cases.
    cells = {(3,1):F(1)}
    for offset,q in enumerate(private,start=2):
        nxt = defaultdict(F)
        for (mask,z),weight in cells.items():
            nxt[(mask | (1 << offset),z)] += weight
            for v in range(2,limit//z+1):
                nxt[(mask,z*v)] += weight*F(q-1,q**v)
        cells = dict(nxt)

    cases = {}
    for name,path in (('FC110',args.first_source),('FC131',args.second_source)):
        source = json.loads(path.read_text())
        roles,rows,masks = source_roles(source,name,require)
        root_data,root_delta = {},{}
        direct_mass = F(0)
        for r in (1,2):
            b5,b7 = heads[r][5],heads[r][7]
            weights = [b5[i]*b7[j] for i in range(5) for j in range(7)]
            w,conditional = {},{}
            for q in private:
                w[q] = []
                for i in range(5):
                    for j in range(7):
                        role5,role7 = roles[q][5],roles[q][7]
                        count = (int(i == role5['free_row'])+int(j == role7['free_row'])
                                 +int(r == role5['selected_root'] and i == role5['selected_row'])
                                 +int(r == role7['selected_root'] and j == role7['selected_row']))
                        debit = F(count,q)
                        require(0 <= debit < zero[r][q], 'each literal conditional private zero factor positive')
                        w[q].append(debit)
                conditional[q] = [1-x/zero[r][q] for x in w[q]]
            actual_root_mass = sum((weights[k]*prod(allowed[r][q]-w[q][k] for q in private)
                                    for k in range(35)),F(0))
            direct_mass += actual_root_mass/3
            total_threshold = allowed[r][5]*allowed[r][7]-zero[r][5]*zero[r][7]
            full_h = [prod(conditional[q][k] for q in private) for k in range(35)]
            full_H = [sum((b5[i]*full_h[7*i+j] for i in range(5)),F(0)) for j in range(7)]
            full_M = sum((b7[j]*full_H[j] for j in range(7)),F(0))
            require(all(full_H[j] >= F(1,5) for j in range(7) if b7[j]), 'FG4 fullQ live row conditions')
            require(full_M >= total_threshold, 'FG4 fullQ total condition')
            h_cells = {0:[F(1) for _ in range(35)]}
            k_product = {0:F(1)}
            deltas,pattern_rows = {},{}
            for mask in range(512):
                if mask:
                    bit = mask & -mask
                    qi = bit.bit_length()-1
                    q = private[qi]
                    previous = mask ^ bit
                    h_cells[mask] = [x*y for x,y in zip(h_cells[previous],conditional[q])]
                    k_product[mask] = k_product[previous]*zero[r][q]
                H = [sum((b5[i]*h_cells[mask][7*i+j] for i in range(5)),F(0)) for j in range(7)]
                M = sum((b7[j]*H[j] for j in range(7)),F(0))
                require(all(x >= y for x,y in zip(h_cells[mask],full_h)), 'subset h dominates fullQ pointwise')
                require(all(H[j] >= F(1,5) for j in range(7) if b7[j]), 'all512 live-row conditions')
                require(total_threshold <= M <= allowed[r][5]*allowed[r][7], 'all512 total positive conditions')
                delta = k_product[mask]*(allowed[r][5]*allowed[r][7]-M)
                capacity = k_product[mask]*zero[r][5]*zero[r][7]
                require(0 <= delta <= capacity, 'each joint headzero correction within capacity')
                deltas[mask] = delta
                pattern_rows[mask] = {'K':str(k_product[mask]),'H_rows':[str(x) for x in H],
                                      'M':str(M),'delta':str(delta),'headzero_capacity':str(capacity)}
            require(deltas[0] == 0, 'empty private zero set unchanged')
            root_delta[r] = deltas
            root_data[str(r)] = {
                'head5_rows':[str(x) for x in b5],'head7_rows':[str(x) for x in b7],
                'fullQ_H_rows':[str(x) for x in full_H], 'fullQ_M':str(full_M),
                'total_threshold':str(total_threshold),
                'fullQ_live_row_min_margin':str(min(full_H[j]-F(1,5) for j in range(7) if b7[j])),
                'fullQ_total_margin':str(full_M-total_threshold),
                'direct_reference_mass':str(actual_root_mass),
                'private_zero_patterns':{str(k):v for k,v in pattern_rows.items()},
            }
        corrected,debit_patterns = {},{}
        debit_moments = [F(0) for _ in orders]
        for mask,(lo,hi,z1,z2) in base_patterns.items():
            root = {1:z1,2:z2}
            if mask & 3 == 3:
                for r in (1,2):
                    root[r] -= root_delta[r][mask >> 2]
            nl,nh = min(root.values()),max(root.values())
            require(0 <= nl <= nh and nl <= lo and nh <= hi, 'joint source-specific fullpattern positivity')
            dl,dh = lo-nl,hi-nh
            corrected[mask] = (nl,nh,root[1],root[2])
            debit_patterns[mask] = (dl,dh)
            for ki in range(len(orders)):
                positive = prod(positive_moments[p][ki] for i,p in enumerate(primes)
                                if not mask & (1 << i))
                debit_moments[ki] += (dl/3+dh*ternary_long[ki])*positive
        debit_atoms = [F(0) for _ in range(257)]
        for (mask,z),weight in cells.items():
            dl,dh = debit_patterns[mask]
            debit_atoms[z] += weight*dl/3
            for v in range(2,limit//z+1):
                debit_atoms[z*v] += weight*dh*F(2,3**v)
        atoms = [a-d for a,d in zip(base_atoms,debit_atoms)]
        moments = [m-d for m,d in zip(base_moments,debit_moments)]
        require(all(0 <= d <= a for d,a in zip(debit_atoms,base_atoms)), 'source-specific scalar debit positive')
        require(moments[0] == direct_mass, 'FG12 direct actual reference mass identity')
        require(moments[0] >= h, 'same physical source mass fits this profile')
        raw,debit = snapshot(atoms,moments),snapshot(debit_atoms,debit_moments)
        atoms,moments,certificate = trim(atoms,moments,h)
        cases[name] = {
            'source_file':path.name,'source_hash':hashlib.sha256(path.read_bytes()).hexdigest(),
            'actual_rows':rows,'selected_root_masks':masks,'root_conditions':root_data,
            'full_zero_patterns':{str(mask):{'min_product':str(lo),'max_product':str(hi),
                                           'root1_product':str(z1),'root2_product':str(z2)}
                                  for mask,(lo,hi,z1,z2) in corrected.items()},
            'direct_reference_mass':str(direct_mass),'raw_grouped':raw,'group_debit':debit,
            'initial_trim':certificate,'initial':snapshot(atoms,moments),
        }
    result = {
        'scope':'two distinct FC159 sources; same eta0/h each; actual N>=max(2,N_plus); n2 pure/star and all36 depth1 groups',
        'evidence':'ordinary conditional theorem and exact arithmetic; no Lean claim',
        'source_mass':str(h),'retained_depth':2,'retained_group_depth':1,
        'atom_limit':limit,'orders':orders,'old_nonternary_primes':primes,
        'canonical_dependency_basenames':['depth_two_profile.py','coloured_star_profile.py'],
        'dependency_hashes':{
            args.arithmetic_library.name:hashlib.sha256(args.arithmetic_library.read_bytes()).hexdigest(),
            args.coloured_library.name:hashlib.sha256(args.coloured_library.read_bytes()).hexdigest()},
        'base_pattern_low_atom_cells':base_cells,'debit_pattern_low_atom_cells':len(cells),
        'cases':cases,'prime_updates_executed':0,'checks':require.__globals__['CHECKS'],
    }
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'checks':result['checks'],'prime_updates_executed':0,
        'cases':{name:{'raw_mass':float(F(case['raw_grouped']['moments']['0'])),
                        'initial_cutoff':case['initial_trim']['cutoff'],
                        'initial_mean':float(F(case['initial']['mean'])),
                        'initial_moments':{k:float(F(v)) for k,v in case['initial']['moments'].items()}}
                 for name,case in cases.items()},'output':str(args.output)}))


if __name__ == '__main__':
    main()

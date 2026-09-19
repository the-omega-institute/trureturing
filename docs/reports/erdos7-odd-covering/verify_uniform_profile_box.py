#!/usr/bin/env python3
"""Verify Gamma<=35 on an entire actual uniform deletion-profile box.

All256 profile corners use exact270-depth moments plus the full geometric
remainder, row-count group bounds, and the originalmod3 signed criterion.
The result applies by concavity to the entire box and its allowed old maps.
Actual carrier membership, support gains and minimality are reconstructed.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parent
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text
from pathlib import Path
from itertools import product
from fractions import Fraction as F
import argparse
import hashlib
import importlib.util
import json
import numpy as np

SCHEMA = "erdos7-uniform-profile-box-v1"
SOURCE = 'certificates/uniform_profile_geometry_certificate.json'
SHAPE = "root1_same_other_column"

def require(ok, why):
    if not ok: raise ArithmeticError(why)

def module(name, path):
    spec=importlib.util.spec_from_file_location(name,path)
    result=importlib.util.module_from_spec(spec);spec.loader.exec_module(result)
    return result

def setup(points):
    mods=(3,5,9,15)
    choices=list(product(*(sorted({x%d for x in points}) for d in mods)))
    features=np.array([[[int(x%d==a) for x in points] for d,a in zip(mods,row)] for row in choices],dtype=np.int64)
    roots=np.array([row[0] for row in choices])
    return features,roots

def profile_squares(points, profiles, pg, geo):
    """Eliminate B and both old45 singletons exactly, sharing all layouts."""
    features,roots=setup(points);rs=6-np.array(profiles,dtype=np.int64)
    values=np.empty((len(profiles),2,270),dtype=np.int64)
    zi=0
    for z3,z5 in product(range(9),range(6)):
        L=1+np.einsum('ajn,j->an',features,np.array([1,1+z5,1+z3,1+z5],dtype=np.int64))
        n=len(L);s=(z3+1)*(z5+1);gram=L@L.T;q=(L*L).sum(axis=1)
        maxload=int(L.max())+s
        bound=(int(rs.sum(axis=1).max())+35*len(points))*maxload*maxload
        require(bound<2**63,'all nonnegative square terms and partial sums fitint64')
        oldbase=rs@(L*L).T
        for z7 in range(5):
            u=z7+1;cross=2*u*gram+u*u*q[None,:]
            bmax=np.zeros((n,n),dtype=np.int64)
            for i in range(len(points)):
                bi=2*u*s*L[:,i,None]+u*u*(2*s*L[None,:,i]+s*s)
                np.maximum(bmax,bi,out=bmax)
            best=np.zeros((len(profiles),2),dtype=np.int64)
            for i in range(len(points)):
                bi=2*u*s*L[:,i,None]+u*u*(2*s*L[None,:,i]+s*s)
                J=(cross+2*u*s*L[None,:,i]+np.maximum(bmax,bi+2*u*s*s)).max(axis=1)
                scores=oldbase+rs[:,i,None]*(2*s*L[None,:,i]+s*s)+J[None,:]
                for j,root in enumerate((1,2)):
                    np.maximum(best[:,j],scores[:,roots==root].max(axis=1),out=best[:,j])
            values[:,:,zi]=best;zi+=1
    return values

def grouped_profiles(points, profiles, f):
    n=len(points);mods=(1,3,5,9,15,45);cyl={}
    for d in mods:
        rows=[np.array([int(x%d==a) for x in points],dtype=np.int64) for a in range(d)]
        keep=[];empty=False
        for row in rows:
            if row.any() or not empty: keep.append(row);empty=empty or not row.any()
        cyl[d]=np.array(keep)
    aa=np.array([a+b for a,b in product(cyl[9],cyl[45])]);bb=np.array([a+b+c for a,b,c in product(cyl[5],cyl[15],cyl[45])])
    A=np.repeat(aa,len(bb),axis=0);B=np.tile(bb,(len(aa),1));T=2-A
    base=(24*A+6*T*B)*np.array(f,dtype=np.int64)
    ft=T*np.array(f,dtype=np.int64);fm=ft*(4-B)
    const=6*(ft@cyl[5].T).max(axis=1)
    for d in mods:const+=(fm@cyl[d].T).max(axis=1)
    bound=6*int(base.sum(axis=1).max())+int(const.max())
    require(bound<2**53,'every nonnegative integer matmul partial sum fitsbinary64')
    bf=base.astype(float);cf=const.astype(float);rs=6-np.array(profiles,dtype=np.int64);values=[]
    for left in range(0,len(rs),32):
        matrix=rs[left:left+32].astype(float)@bf.T+cf
        require(np.all(matrix==np.rint(matrix)),'exact integer group matrix')
        values.extend(matrix.max(axis=1).astype(np.int64).tolist())
    return values,{'layout_pairs':len(base),'exact_integer_bound':bound}


def evaluate(data, directory):
    require(type(data) is dict and data.get('schema') == SCHEMA, 'profile-box schema')
    require(data.get('source_certificate') == SOURCE and data.get('target') == '35',
            'specified source and target')
    source_bytes = read_artifact_bytes(directory / SOURCE)
    require(hashlib.sha256(source_bytes).hexdigest() == data.get('source_sha256'),
            'parent uniform-profile certificate fingerprint')
    cert = json.loads(source_bytes)
    require(cert.get('shape') == SHAPE and cert.get('target') == '35'
            and cert.get('depth_box') == [8, 5, 4], 'specified parent profile')
    pg = module('box_point', directory / 'verify_point_geometry.py')
    geo = module('box_geometry', directory / 'verify_seven_digit_classification.py')
    dom = module('box_dominance', directory / 'verify_carrier_dominance.py')
    geometries = geo.read_geometries(directory / 'certificates/actual_deletion_profile_certificate.json')
    old_case = next(row for row in geometries if row['shape'] == SHAPE)
    points = old_case['old_points']
    require(points == cert['result']['old_points'], 'canonical old geometry agrees with parent')
    source = cert['profile']
    require(type(source) is list and len(source) == len(points)
            and all(type(b) is int and 0 <= b <= 5 for b in source), 'integer source profile')
    support = [i for i, b in enumerate(source) if b]
    profiles = []
    for bits in product((0, 1), repeat=len(support)):
        b = [0] * len(source)
        for i, bit in zip(support, bits):
            b[i] = source[i] * bit
        profiles.append(b)
    require(len(profiles) == 256, 'eight varying coordinates and all256 corners')
    ds, _, _, rem, depths, probs, beta, eo = pg.coeffs((8, 5, 4))
    rem[ds.index(35)] -= F(1, 4)
    require(min(rem) >= 0 and min(eo) >= 0 and 0 < beta < 1,
            'nonnegative residual and full geometric tail coefficients')
    squares = profile_squares(points, profiles, pg, geo)
    require(squares.shape == (256, 2, 270), 'all root and depth cases')
    for j, row in enumerate(cert['result']['shared_pure7_bounds']):
        require(geo.digest(squares[-1, j].tolist()) == row['depth_maxima_sha256'],
                'canonical source270-depth square identity')
    weights = [[1] * len(points)] + [
        [34 - 3 * int(x % 3 == root) for x in points] for root in (1, 2)]
    group_results = [grouped_profiles(points, profiles, f) for f in weights]
    groups = [row[0] for row in group_results]
    parent_groups = [cert['result']['cases'][0]['group_numerator48']] + [
        row['weighted_group_numerator48'] for row in cert['result']['cases'][0]['roots']]
    require([g[-1] for g in groups] == parent_groups, 'canonical source group numerators')
    corners, minq, minmargin = [], None, [None, None]
    for k, b in enumerate(profiles):
        r = [6 - bi for bi in b]
        denominator = sum(r)
        caps = [[max(sum((1 if d % 7 == 0 else ri) * fi
                        for x, ri, fi in zip(points, r, f)
                        if x % (d // 7 if d % 7 == 0 else d) == a)
                    for a in range(d // 7 if d % 7 == 0 else d))
                 for d in ds] for f in weights]
        survival = 1 - F(groups[0][k], 48 * denominator) - sum(
            (e * F(c, denominator) for e, c in zip(rem, caps[0])), F())
        if minq is None or survival < minq[0]:
            minq = (survival, k)
        require(survival > 0, 'positive same-law higher survival at every box corner')
        tail = sum((e * c for e, c in zip(eo, caps[0])), F())
        roots = []
        for j, root in enumerate((1, 2)):
            upper = (1 - beta) * int(squares[k, j, 0]) + tail + sum(
                (p * int(v) for p, v in zip(probs, squares[k, j])), F())
            deletion = F(groups[j + 1][k], 48) + sum(
                (e * c for e, c in zip(rem, caps[j + 1])), F())
            margin = 35 * denominator - upper - deletion
            require(margin >= 0, 'signed originalmod3 criterion at every box corner')
            if minmargin[j] is None or margin / denominator < minmargin[j][0]:
                minmargin[j] = (margin / denominator, k)
            roots.append({'root': root, 'moment_numerator': str(upper),
                          'deletion_numerator': str(deletion), 'margin_numerator': str(margin),
                          'normalized_margin': str(margin / denominator),
                          'depth_maxima_sha256': geo.digest(squares[k, j].tolist())})
        corners.append({'b': b, 'denominator': denominator, 'survival_lower': str(survival),
                        'group_numerators': [g[k] for g in groups], 'roots': roots})

    # A positive lower bound for a normalized slack extends from all corners:
    # subtract that lower bound times N before applying concavity.
    maps = geo.old_maps(points)
    require(all(points[p[i]] % 3 == points[i] % 3 for p in maps for i in range(len(points))),
            'both original mod3 roots preserved by every old map')
    images = set()
    for p in maps:
        b = [0] * len(points)
        for i, bi in enumerate(source):
            b[p[i]] = bi
        images.add(tuple(b))
    states, _, _ = geo.digit_union_states(points)
    require(len(states) == old_case['digit_union_states'], 'all actual carrier states reconstructed')
    box, profiles_present, sources = set(), set(), set()
    for state in states:
        b = geo.deletion_vector(state, len(points))
        if b in images:
            sources.add(state)
        if any(all(x <= y for x, y in zip(b, image)) for image in images):
            box.add(state)
            profiles_present.add(b)
    source_representatives = dom.carrier_orbits(sources, maps, geo)
    require(len(sources) == cert['result']['profile_carriers']
            and len(source_representatives) == cert['result']['profile_carrier_orbits'],
            'all parent profile sources reconstructed')
    used = {u for state in states for u in state}
    edges = [{b: sum(1 << j for j, a in enumerate(source_state) if b & ~a == 0) for b in used}
             for source_state in sorted(sources)]
    former = {state for state in states if any(
        dom.injection(tuple(sorted(edge[b] for b in state))) for edge in edges)}
    require(former <= box, 'former source-support family is contained in the profile box')
    former_representatives = dom.carrier_orbits(former, maps, geo)
    require(len(former) == cert['result']['covered_carriers']
            and len(former_representatives) == cert['result']['covered_carrier_orbits'],
            'former support coverage agrees with parent')
    representatives = dom.carrier_orbits(box, maps, geo)
    solve, targets, _, _ = dom.resource_problem(
        representatives, dom.old_cylinders(points, geo.MODULI))
    minimals = [state for state in representatives
                if solve(targets(state), 31) == sum(u.bit_count() for u in state)]
    new_states = box - former
    new_representatives = dom.carrier_orbits(new_states, maps, geo)
    return {
        'shape': SHAPE, 'old_points': points, 'source_profile': source,
        'profile_images': [list(b) for b in sorted(images)], 'box_vertices': len(corners), 'corners': corners,
        'minimum_survival': str(minq[0]), 'minimum_survival_vertex': minq[1],
        'minimum_root_margins': [str(x[0]) for x in minmargin],
        'minimum_root_margin_vertices': [x[1] for x in minmargin],
        'group_integer_ranges': [r[1] for r in group_results],
        'actual_geometry': {
            'all_states': len(states), 'covered_states': len(box),
            'covered_orbits': len(representatives), 'covered_profiles': len(profiles_present),
            'covered_minimal_orbits': len(minimals), 'minimal_representatives': [list(s) for s in minimals],
            'covered_states_sha256': geo.digest(sorted(box)),
            'covered_orbits_sha256': geo.digest(representatives),
            'covered_profiles_sha256': geo.digest(sorted(profiles_present)),
            'former_states': len(former), 'former_orbits': len(former_representatives),
            'additional_states': len(new_states), 'additional_orbits': len(new_representatives),
            'additional_minimal_orbits': len(minimals) - cert['result']['profile_minimal_orbits'],
            'additional_orbits_sha256': geo.digest(new_representatives)}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--directory', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--write', type=Path)
    parser.add_argument('--check', type=Path)
    args = parser.parse_args()
    require(not (args.write and args.check), 'select writer or replay')
    if args.write:
        data = {'schema': SCHEMA, 'source_certificate': SOURCE, 'target': '35',
                'source_sha256': hashlib.sha256(read_artifact_bytes(args.directory / SOURCE)).hexdigest()}
        data['result'] = evaluate(data, args.directory)
        write_certificate_text(args.write, json.dumps(data, indent=2) + '\n')
    else:
        path = args.check or args.directory / 'certificates/uniform_profile_box_certificate.json'
        data = json.loads(read_artifact_text(path))
        require(evaluate(data, args.directory) == data['result'], 'complete profile-box certificate replay')
    result = data['result']
    print(json.dumps({'schema': SCHEMA, 'box_vertices': result['box_vertices'],
                      'minimum_survival': result['minimum_survival'],
                      'minimum_root_margins': result['minimum_root_margins'],
                      'actual_geometry': result['actual_geometry']}, sort_keys=True))


if __name__ == '__main__':
    main()

"""Validate constant inputs and GPU-returned rows. No exponent-box generator."""

import hashlib
import itertools
import json
import math
from fractions import Fraction as F
from pathlib import Path

PRIMES = (2, 3, 5, 7, 11, 13, 17, 19)
BOX_COUNT = math.comb(len(PRIMES), 3) * 16**3
SLOTS = 25
INTEGER_FIELDS = ('row_id', 'box_id', 'slot', 'triple_index', 'b0', 'b1', 'b2',
                  'p0', 'p1', 'p2', 'lower_mask', 'upper_mask', 'next_mask',
                  'j', 'i', 'guard_bits', 'active', 'error_bits')
FLOAT_FIELDS = ('M0', 'M1', 'ell', 'L', 'H', 'V0', 'scaled_gap', 'tail',
                'permutation_0', 'permutation_1', 'permutation_2',
                'permutation_3', 'permutation_4', 'permutation_5')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def validate_constants(rows, primes):
    require(primes == list(PRIMES), 'fixed prime alphabet mismatch')
    require(all(p > 1 and all(p % d for d in range(2, math.isqrt(p)+1))
                for p in primes), 'composite prime label')
    triples = list(itertools.combinations(primes, 3))
    require(type(rows) is list and len(rows) == len(triples), 'constant row count')
    for t, (row, triple) in enumerate(zip(rows, triples)):
        require(set(row) == {'triple_index','primes','sorted_masks','subset_products'},
                'constant row schema')
        require(type(row['triple_index']) is int and row['triple_index'] == t
                and row['primes'] == list(triple), 'constant triple order/identity')
        masks, products = row['sorted_masks'], row['subset_products']
        require(all(type(x) is int for x in row['primes']+masks+products),
                'constant integer types')
        require(sorted(masks) == list(range(8)), 'each binary mask must occur once')
        expected = [math.prod(p for i,p in enumerate(triple) if m >> i & 1) for m in masks]
        require(products == expected and all(a < b for a,b in zip(products,products[1:])),
                'corner product or ordering mismatch')


def load_input(path, expected_sha256):
    data = Path(path).read_bytes()
    require(hashlib.sha256(data).hexdigest() == expected_sha256, 'input identity mismatch')
    doc = json.loads(data)
    require(set(doc) == {'schema_version','kind','primes','rows','triple_order',
                         'mask_convention','search_executed','exponent_boxes_generated'},
            'input schema mismatch')
    require(doc['schema_version'] == 1 and doc['kind'] == 'constant-prime-corner-order-input'
            and doc['search_executed'] is False and doc['exponent_boxes_generated'] == 0,
            'input is not a prospective constant certificate')
    validate_constants(doc['rows'], doc['primes'])
    return doc['rows']


def validate_window(first, last, chunk):
    require(all(type(x) is int for x in (first,last,chunk)) and
            0 <= first <= last < BOX_COUNT and 1 <= chunk <= BOX_COUNT,
            'invalid bounded box window or chunk size')


def check_coverage(raw_rows, first, last):
    """Only compare returned IDs with the required sequence; never construct a row."""
    require(len(raw_rows) == SLOTS*(last-first+1), 'missing/extra raw rows')
    for offset, row in enumerate(raw_rows):
        values = row.get('integers', [])
        require(values and type(values[0]) is int and values[0] == SLOTS*first+offset,
                'missing/duplicate/reordered/out-of-window raw row ID')


def guard_bits(R, cube=None, X=None, E=None, middle=None, upper=None):
    if cube is None:
        return int(R > 5040)
    return sum(int(flag) << i for i, flag in enumerate(
        (R > 5040, cube < X, X*X < E, middle < E, E < upper)))


def audit_row(raw, constants):
    """Decoding is permitted here ONLY because raw has already returned from MPS."""
    v = raw['integers']
    require(len(v) == len(INTEGER_FIELDS) and all(type(x) is int for x in v),
            'raw integer shape/types')
    row_id = v[0]
    require(0 <= row_id < BOX_COUNT*SLOTS, 'raw ID outside fixed domain')
    box, slot = divmod(row_id, SLOTS)
    t, rem = divmod(box, 4096)
    b = [rem//256, rem//16 % 16, rem % 16]
    p, masks = constants[t]['primes'], constants[t]['sorted_masks']
    j, i = (slot+1, -1) if slot < 7 else (1+(slot-7)//3, (slot-7)%3)
    lower, upper = masks[j-1], masks[j]
    following = -1 if i == -1 else masks[j+1]
    expected = [row_id,box,slot,t,*b,*p,lower,upper,following,j,i]
    require(v[:15] == expected, 'GPU returned parameters disagree with row ID')
    require(0 <= v[15] <= 31 and v[16] in (0,1) and 0 <= v[17] <= 15,
            'unknown guard/activity/error bits')
    fp = raw['floats']
    require(len(fp) == len(FLOAT_FIELDS) and all(type(x) is str for x in fp),
            'raw float shape/types')
    floating = [float.fromhex(x) for x in fp]
    P = math.prod(p)
    # These integers audit a returned row; this module exposes no search iterator.
    R = math.prod(p[k]**(b[k]+((lower >> k)&1)) for k in range(3))
    Ru = math.prod(p[k]**(b[k]+((upper >> k)&1)) for k in range(3))
    X = P*R
    C = [p[k]**(b[k]+1) for k in range(3)]
    D = [p[k]**(b[k]+2) for k in range(3)]
    if i == -1:
        bits, active, q1, T1 = guard_bits(R), R > 5040, F(P*Ru), F(Ru)
    else:
        Rn = math.prod(p[k]**(b[k]+((following >> k)&1)) for k in range(3))
        E = p[i]**(3*(2*b[i]+3))
        bits = guard_bits(R, C[i]**3, X, E, P*P*R*Ru, P*P*R*Rn)
        active, q1, T1 = bits == 31, F(E,X), F(E,P*P*R)
        require(T1.denominator > 1, 'reflected exp(T1) must be nonintegral')
    disagreements = []
    if v[15] != bits: disagreements.append('guard_bits')
    if bool(v[16]) != active: disagreements.append('activity')
    if v[17] & 1: disagreements.append('integer_error')
    proposed = 'inactive'
    if v[16]:
        if v[17] or not all(math.isfinite(x) for x in floating):
            proposed = 'indeterminate'
        elif floating[6]+floating[7] < 0:
            proposed = 'negative'
        elif floating[6]-floating[7] > 0:
            proposed = 'positive'
        else:
            proposed = 'indeterminate'
    return dict(row_id=row_id, kind='adjacent' if i == -1 else 'reflected',
                C=C, D=D, q0=str(X), q1=str(q1), exp_T1=str(T1), R_lower=R,
                guard_bits=bits, active=active, proposed=proposed,
                disagreements=disagreements, gpu_error_bits=v[17])

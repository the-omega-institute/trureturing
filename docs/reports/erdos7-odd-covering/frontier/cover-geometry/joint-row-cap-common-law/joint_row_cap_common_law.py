#!/usr/bin/env python3
"""Exact shared-row-tail certificates for the seven-component cap architecture.

For any fixed full-five cap probability and six fixed pair-three cap
probabilities on the same actual source, some convex mixture fixed before
all phases has original-divisor squared load <= 407237/70076 < 6.
The height-three bound is 146409/26585 < 152/27; the universal bound
already beats the finite target at every height >= 4.

This is a standard-library rational certificate checker, not an LP solver
or Lean proof. Its 108 duals cover every beta-cell vertex and all 256
length-four row words; the accompanying report supplies the infinite-tail
and finite-minimax arguments. A separate exact example shows why a
root-row-mass refinement of this relaxation does not settle height two.
Only stdout is written. Row indices in this program are 0,1,2,3.
"""
from fractions import Fraction as F
from itertools import combinations, product
import argparse
import json

ROWS = tuple(range(4))
PAIRS = tuple(combinations(ROWS, 2))
LIMIT = F(407237, 70076)
HEIGHT_THREE = F(146409, 26585)
HEIGHT_FOUR = F(1716541, 301925)

# Lexicographically ordered beta vertices from beta_vertices(). Each row:
# six pair multipliers, three root-order multipliers, tail multiplier,
# full-law multiplier, and the unrestricted normalization multiplier.
# The data are exact feasible dual witnesses; no optimizer is executed.
DUALS = r"""
2349/13697 2349/13697 0 2349/13697 0 0 7047/13697 0 0 4698/13697 6650/13697 39672/13697
15903/68863 9855/68863 0 9855/68863 0 0 14403/68863 0 0 25758/68863 33250/68863 202350/68863
369603/1179038 810/12031 0 810/12031 0 0 0 99573/1179038 0 448983/1179038 650675/1179038 3453699/1179038
4671/14371 0 0 0 0 0 0 0 8730/14371 4671/14371 9700/14371 39444/14371
4482/14807 0 0 0 0 0 0 0 18162/14807 4482/14807 10325/14807 37848/14807
4374/14699 0 0 0 0 0 0 0 20277/14699 4374/14699 10325/14699 36936/14699
4234/32239 7202/32239 0 4178/32239 0 0 176779/290151 0 0 11436/32239 16625/32239 864880/290151
891/4616 891/4616 0 459/4616 0 0 0 0 0 891/2308 2375/4616 13965/4616
2397234/8247461 137/1154 0 117231/8497165 0 0 0 1188131/9890542 0 3005191/7340821 46649017788997551/80872362638067010 11035843188020846353/3639256318713015450
351/1321 0 0 0 0 0 0 0 4074/6605 351/1321 970/1321 20058/6605
486/2177 0 216/2177 0 0 0 0 0 2050/2177 702/2177 1475/2177 5973/2177
486/2119 0 108/2119 0 0 0 0 0 2653/2119 594/2119 1525/2119 5767/2119
18142/257317 1235653/4028162 0 41551/886940 0 0 0 0 0 391033438005/1036514561354 4068771/7065134 7523662685415710434009997/2519675289959527726233300
48843/342626 46899/171313 0 9045/685252 0 0 0 0 0 142641/342626 390925/685252 2082723/685252
54/463 54/463 0 0 0 0 0 0 0 108/463 355/463 1527/463
27/392 0 0 0 0 0 0 0 219/392 27/392 365/392 27/8
18/431 0 18/431 0 0 0 0 0 2608/2155 36/431 395/431 1339/431
35829/415822 0 49059/207911 0 0 0 0 0 112362/207911 297/922 625/922 1172925/415822
0 0 0 0 0 0 0 4/5 2/5 0 1 17/5
0 108/733 0 0 0 0 0 780/733 270/733 108/733 625/733 2181/733
0 0 108/733 0 0 0 0 780/733 510/733 108/733 625/733 2181/733
0 729/2704 0 0 0 0 0 1187/1352 1181/2704 729/2704 1975/2704 7349/2704
0 0 729/2704 0 0 0 0 1187/1352 1193/2704 729/2704 1975/2704 7349/2704
0 108/791 108/791 0 0 0 0 956/791 478/791 216/791 575/791 2083/791
0 1377/6076 81/1519 0 0 0 0 12643/9114 16543/18228 243/868 625/868 45715/18228
0 81/1519 1377/6076 0 0 0 0 12643/9114 1249/2604 243/868 625/868 45715/18228
0 1701/13205 1701/13205 0 0 1053/13205 0 16877/13205 361/695 3402/13205 1750/2641 31507/13205
4234/32239 4178/32239 0 7202/32239 0 0 0 0 0 11436/32239 16625/32239 864880/290151
891/4616 459/4616 0 891/4616 0 0 0 0 0 891/2308 2375/4616 13965/4616
2478573/8536618 29401/1735551 0 201813/1668668 0 0 0 585783/6886582 0 225257/547686 5363421/9380366 1358830734083318785258786024381189/449168408884536250512623018769081
171/521 0 0 0 0 0 0 0 294/521 171/521 350/521 4510/1563
486/2177 0 0 0 216/2177 0 0 0 2050/2177 702/2177 1475/2177 5973/2177
486/2119 0 0 0 108/2119 0 0 0 2653/2119 594/2119 1525/2119 5767/2119
7305/79462 7233/39731 0 7233/39731 0 0 0 0 0 14466/39731 43225/79462 366472/119193
1809/12077 1809/12077 0 1809/12077 0 0 0 0 0 3618/12077 6650/12077 37734/12077
248832/1006427 73710/1006427 0 73710/1006427 0 0 0 25303/1006427 0 322542/1006427 610175/1006427 3136244/1006427
3429/13129 0 0 0 0 0 0 0 7566/13129 3429/13129 9700/13129 39432/13129
2943/12643 0 0 0 0 0 0 0 15714/12643 2943/12643 9700/12643 35328/12643
567/2507 0 0 0 0 0 0 0 17654/12535 567/2507 1940/2507 34416/12535
71109/2423249 658701/2423249 0 233289/2423249 0 0 0 0 0 891990/2423249 1460150/2423249 7532360/2423249
298550/4067447 423873/1768313 0 301601/5453692 0 0 0 0 0 962971/3075557 24774741174090508249/39225785549315265412 8402048861719265325373/2647740524578780415310
621/5317 621/5317 0 0 0 0 0 0 0 1242/5317 4075/5317 17538/5317
243/3893 0 0 0 0 0 0 0 1971/3893 243/3893 3650/3893 13002/3893
63/2101 0 63/2101 0 0 0 0 0 2584/2101 126/2101 1975/2101 6464/2101
867/25667 0 2100/25667 0 0 0 0 0 93889/77001 2967/25667 22700/25667 227786/77001
0 0 0 0 0 0 0 18/25 9/25 0 1 84/25
0 108/733 0 0 0 0 0 730/733 245/733 108/733 625/733 2156/733
0 0 108/733 0 0 0 0 730/733 485/733 108/733 625/733 2156/733
0 108/733 0 0 0 0 0 2597/2199 553/2199 108/733 625/733 6286/2199
0 0 108/733 0 0 0 0 2597/2199 2044/2199 108/733 625/733 6286/2199
0 1350/21257 1782/21257 0 0 0 0 1202/733 16341/21257 108/733 625/733 1984/733
0 1512/18295 54/18295 0 0 54/18295 0 37563/18295 3851/3659 1566/18295 3335/3659 49002/18295
0 54/18295 1512/18295 0 0 54/18295 0 37563/18295 18146/18295 1566/18295 3335/3659 49002/18295
0 27/656 27/656 0 0 27/656 0 4061/1968 1909/1968 27/328 575/656 5101/1968
18142/257317 41551/886940 0 1235653/4028162 0 0 0 0 0 391033438005/1036514561354 4068771/7065134 7523662685415710434009997/2519675289959527726233300
1444662/8855635 209358/8855635 0 466668/1771127 0 0 0 0 0 3778002/8855635 973655/1771127 26729409/8855635
63963/245266 0 0 18864/122633 0 0 8357/122633 0 0 101691/245266 143575/245266 381127/122633
162/1237 0 0 0 0 0 183/1237 0 645/1237 162/1237 1075/1237 3924/1237
162/1349 0 0 0 162/1349 0 20/1349 0 50/71 324/1349 1025/1349 3955/1349
162/1259 0 0 0 72/1259 0 877/3777 0 4000/3777 234/1259 1025/1259 10994/3777
71109/2423249 233289/2423249 0 658701/2423249 0 0 0 0 0 891990/2423249 1460150/2423249 7532360/2423249
298550/4067447 301601/5453692 0 423873/1768313 0 0 4791001/8460341 0 0 962971/3075557 24774741174090508249/39225785549315265412 8402048861719265325373/2647740524578780415310
50760/339523 0 0 39663/339523 0 0 0 0 0 90423/339523 249100/339523 1090338/339523
162/1237 0 0 0 0 0 1597/2474 0 1161/2474 162/1237 1075/1237 7719/2474
9072/69635 0 0 0 1188/69635 0 42111/139270 0 135417/139270 108/733 625/733 412923/139270
9072/69635 0 0 0 1188/69635 0 51611/139270 0 159167/139270 108/733 625/733 403423/139270
0 2511/13922 0 2511/13922 0 0 0 0 0 2511/6961 4450/6961 21204/6961
19062/406265 54864/406265 0 54864/406265 0 0 0 6419/81253 0 109728/406265 55495/81253 1260002/406265
1944/32719 1431/32719 0 594/32719 0 0 0 1275/32719 0 3375/32719 28750/32719 104625/32719
27/757 0 0 0 0 0 0 0 219/757 27/757 730/757 2418/757
0 0 0 0 0 0 1/20 1/10 123/100 0 1 59/20
0 0 0 0 0 0 9/100 9/50 147/100 0 1 291/100
0 0 0 0 0 0 0 2/5 1/5 0 1 16/5
0 9/1013 0 9/1013 0 0 44/1013 5813/5065 0 18/1013 995/1013 2991/1013
0 0 0 0 0 0 1/20 59/50 123/100 0 1 59/20
0 81/4862 0 81/4862 0 0 18/221 3216/2431 0 81/2431 2350/2431 7077/2431
0 0 0 0 0 0 9/100 69/50 147/100 0 1 291/100
0 0 0 0 0 0 1/4 103/50 103/100 0 1 11/4
0 0 0 0 0 54/629 331/2516 2263/1258 1493/2516 54/629 575/629 6641/2516
0 0 0 0 0 54/629 331/2516 2263/1258 2385/2516 54/629 575/629 6641/2516
0 0 0 0 0 891/4316 0 6165/4316 873/2158 891/4316 3425/4316 2643/1079
0 0 0 0 0 0 9/20 3/10 3/20 0 1 63/20
27/1682 0 0 0 0 0 9627/8410 0 0 27/1682 1655/1682 2487/841
0 9/1013 0 9/1013 0 0 5593/5065 5813/5065 0 18/1013 995/1013 2991/1013
0 0 0 0 0 0 113/100 59/50 123/100 0 1 59/20
243/8518 0 0 0 0 0 5586/4259 0 0 243/8518 8275/8518 12453/4259
0 81/4862 0 81/4862 0 0 3018/2431 3216/2431 0 81/2431 2350/2431 7077/2431
0 0 0 0 0 0 129/100 69/50 147/100 0 1 291/100
0 0 0 27/226 0 0 7761/5650 1434/2825 0 27/226 199/226 303/113
0 0 0 0 0 0 181/100 39/50 103/100 0 1 11/4
0 0 0 0 0 0 181/100 103/50 103/100 0 1 11/4
11/15482 0 0 1148/7741 0 0 598685/418014 133789/418014 0 2307/15482 13175/15482 1088323/418014
0 0 0 0 54/629 0 4195/2516 581/1258 1493/2516 54/629 575/629 6641/2516
0 11/15482 0 1148/7741 0 0 598685/418014 139460/209007 0 2307/15482 13175/15482 1088323/418014
0 0 0 0 54/629 0 4195/2516 1027/1258 2385/2516 54/629 575/629 6641/2516
0 0 0 0 0 54/629 4195/2516 2263/1258 1493/2516 54/629 575/629 6641/2516
0 0 0 0 0 54/629 4195/2516 2263/1258 2385/2516 54/629 575/629 6641/2516
0 0 0 243/1018 0 0 2685/2036 333/1018 105/2036 243/1018 775/1018 4917/2036
0 0 0 0 243/1018 0 2685/2036 333/1018 561/2036 243/1018 775/1018 4917/2036
0 0 0 0 0 243/1018 2685/2036 645/509 561/2036 243/1018 775/1018 4917/2036
0 0 0 0 0 0 249/100 83/50 83/100 0 1 51/20
0 0 0 0 0 0 53/20 79/50 79/100 0 1 251/100
0 0 0 0 0 0 53/20 93/50 79/100 0 1 251/100
0 0 0 0 0 0 53/20 93/50 107/100 0 1 251/100
0 0 0 243/1018 0 0 3739/2036 1015/1018 1779/2036 243/1018 775/1018 4607/2036
0 0 0 0 243/1018 0 3739/2036 1015/1018 251/2036 243/1018 775/1018 4607/2036
0 0 0 0 0 243/1018 3739/2036 490/509 251/2036 243/1018 775/1018 4607/2036
0 0 0 243/2279 243/2279 243/2279 14715/9116 3447/4558 1989/9116 486/2279 1550/2279 19413/9116
"""


def require(condition, message):
    if not condition:
        raise ValueError(message)


def beta_vertices():
    """Vertices of simplex cells cut at beta_r=1/25 and beta_r=1/5."""
    cuts = (F(0), F(1, 25), F(1, 5), F(1))
    result = set()
    for free in ROWS:
        for values in product(cuts, repeat=3):
            remaining = 1-sum(values)
            if 0 <= remaining <= 1:
                result.add(values[:free]+(remaining,)+values[free:])
    return tuple(sorted(result))


def row_weights(word):
    """All original ordered-label pairs, with incompatible rows removed."""
    require(bool(word) and all(r in ROWS for r in word), 'invalid row word')
    labels = [(j, None) for j in range(len(word))]+list(enumerate(word))
    pure = [0]*len(word)
    weights = [[0]*len(word) for _ in ROWS]
    for (i, r), (j, s) in product(labels, repeat=2):
        depth = max(i, j)
        if r is None and s is None:
            pure[depth] += 1
        elif r is None:
            weights[s][depth] += 1
        elif s is None or r == s:
            weights[r][depth] += 1
    require(pure == [2*j+1 for j in range(len(word))], 'pure coefficient')
    for j, selected in enumerate(word):
        previous = sum(r == selected for r in word[:j])
        for r in ROWS:
            closed = (2*j+3+2*previous)*(r == selected)+2*word[:j].count(r)
            require(weights[r][j] == closed, 'row coefficient identity')
        require(sum(w[j] for w in weights) <= 6*j+3, 'row coefficient tail bound')
    return tuple(tuple(w) for w in weights)


def geometric_sum(base, height):
    if height is None:
        return F(base*(base+1), (base-1)**2)
    require(type(height) is int and height >= 0, 'invalid height')
    return sum((F(2*j+1, base**j) for j in range(height+1)), F())


def constants(height):
    require(height is None or type(height) is int and height >= 3,
            'certificate RHS requires height >= 3 or an infinite tail')
    s3, s5 = geometric_sum(3, height), geometric_sum(5, height)
    tail = 3*(s3-geometric_sum(3, 3))
    full_base = 4*s5-3*geometric_sum(5, 2)
    require(tail >= 0, 'negative shared tail budget')
    return s3, tail, full_base


def finite_target(height):
    require(type(height) is int and height >= 0, 'invalid target height')
    return 6-F(2*(height+2), 3**height)


def certify_architecture():
    """Check every real-beta cell via all exact dual columns and RHS values."""
    vertices = beta_vertices()
    certificates = tuple(tuple(map(F, line.split())) for line in DUALS.splitlines() if line.strip())
    require(len(vertices) == len(certificates) == 108, 'complete beta-vertex coverage')
    words = tuple(product(ROWS, repeat=4))
    weighted_words = tuple((word, row_weights(word)) for word in words)
    bounds = {height: [] for height in (None, 3, 4)}
    columns = 0
    for beta, cert in zip(vertices, certificates):
        require(len(cert) == 12, 'dual vector length')
        y, normalization = cert[:11], cert[11]
        require(min(y) >= 0, 'negative inequality multiplier')
        for word, weights in weighted_words:
            pair_prices = tuple(3*(word[0] == s)+sum(
                (F(weights[r][j]+weights[s][j], 3**j) for j in range(1, 4)), F())
                for r, s in PAIRS)
            full_price = sum((weights[r][j]*min(beta[r], F(1, 5**j))
                              for r in ROWS for j in range(3)), F())
            order = sum((y[6+r]*((word[0] == r)-(word[0] == r+1)) for r in range(3)), F())
            slack = normalization+order-sum((y[i]*p for i, p in enumerate(pair_prices)), F())-y[10]*full_price
            require(slack >= 0, f'negative word column: beta={beta}, word={word}')
            columns += 1
        for r in ROWS:
            require(y[9] >= sum((y[i] for i, pair in enumerate(PAIRS) if r in pair), F()),
                    f'negative shared-tail column: beta={beta}, row={r}')
            columns += 1
        require(sum(y[:6])+y[10] >= 1, f'value normalization: beta={beta}')
        columns += 1
        for height in bounds:
            s3, tail, full_base = constants(height)
            value = normalization+s3*sum(y[:6])+tail*y[9]+full_base*y[10]
            bounds[height].append((value, beta))
    maxima = {height: max(values) for height, values in bounds.items()}
    require(maxima[None][0] == LIMIT, 'universal certificate value')
    require(maxima[3][0] == HEIGHT_THREE, 'height-three certificate value')
    require(maxima[4][0] == HEIGHT_FOUR, 'height-four certificate value')
    require(HEIGHT_THREE < finite_target(3), 'height-three target')
    require(LIMIT < finite_target(4) < 6, 'universal bound beats height-four target')
    # (K+2)/3^K strictly decreases: 3(K+2)-(K+3)=2K+3>0.
    require(3*(4+2)-(4+3) > 0, 'target monotonicity base case')
    return {'beta_vertices': len(vertices), 'complete_row_words': len(words),
            'exact_dual_columns': columns,
            'universal_upper': LIMIT, 'universal_winning_beta': maxima[None][1],
            'height_three_upper': HEIGHT_THREE, 'height_three_margin': finite_target(3)-HEIGHT_THREE,
            'height_four_upper': HEIGHT_FOUR, 'universal_height_four_margin': finite_target(4)-LIMIT,
            'scope': 'arbitrary seven fixed actual cap laws; one convex mixture before phases; target for all K>=3'}


def root_mass_relaxation_boundary():
    """An exact obstruction to a relaxed price estimate, not an actual source."""
    beta = (F(1, 25), F(1, 5), F(1, 5), F(14, 25))
    distribution = (((1, 1, 1), F(5, 16)), ((2, 2, 2), F(5, 16)), ((3, 3, 0), F(3, 8)))
    require(sum(p for _, p in distribution) == 1, 'layout distribution normalization')
    rho = tuple(sum((p for word, p in distribution if word[0] == r), F()) for r in ROWS)
    require(tuple(sorted(rho)) == rho, 'root ordering')
    averaged = tuple(tuple(sum((p*row_weights(word)[r][j] for word, p in distribution), F())
                           for j in range(3)) for r in ROWS)
    full = geometric_sum(5, 2)+sum((averaged[r][j]*min(beta[r], F(1, 5**j))
                                   for r in ROWS for j in range(3)), F())
    cuts = (F(0), F(1, 9), F(1, 3), F(2, 3), F(8, 9), F(1))
    pair_values = tuple(max(geometric_sum(3, 2)+sum(
        (averaged[r][j]*min(gamma, F(1, 3**j))
         +averaged[s][j]*min(1-gamma, F(1, 3**j)) for j in range(3)), F())
        for gamma in cuts) for r, s in PAIRS)
    require(full == F(1029, 200), 'full relaxed price')
    require(pair_values == (F(185, 36), F(185, 36), F(185, 36), F(923, 144), F(917, 144), F(917, 144)),
            'pair relaxed prices')
    value = min((full,)+pair_values)
    require(value-finite_target(2) == F(1, 36), 'height-two relaxation gap')
    return {'beta': beta, 'distribution': distribution, 'full_relaxed_price': full,
            'pair_relaxed_prices': pair_values, 'relaxed_value': value,
            'target': finite_target(2), 'excess': value-finite_target(2),
            'scope': 'obstruction only to row-mass price relaxation; no actual-source obstruction'}


def controls():
    return {'architecture': certify_architecture(), 'height_two_boundary': root_mass_relaxation_boundary(),
            'verification': 'exact Fraction inequalities; standard library only; ordinary proof, not Lean certification'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compact', action='store_true', help='emit one-line JSON')
    args = parser.parse_args()
    print(json.dumps(controls(), default=str, indent=None if args.compact else 2, sort_keys=True))


if __name__ == '__main__':
    main()

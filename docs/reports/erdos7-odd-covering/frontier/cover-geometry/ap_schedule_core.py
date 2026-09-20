"""Complete missing-class and finite-core bounds for actual AP(4,5)."""
from fractions import Fraction as F
from math import prod


def require(condition, message):
    if not condition:
        raise ValueError(message)


def fallbacks(source, caps, G, targets, main_rho):
    rows, rho = [], main_rho
    for name, pure, density in source.FALLBACK_INPUTS:
        original = tuple((p, 1 / u) for p, u in zip((3, 5, 7), pure))
        factor = density * prod(pure)
        hinge = lambda t: factor * source.product_hinge(original, F(t))
        survival = F(919, 924) - hinge(4) / 6 - F(4, 33) * hinge(5) - hinge(F(5, 2)) / 22
        require(survival > 0, 'Positive new-law missing-class survival')
        square = lambda t: factor * source.product_square_hinge(original, t)

        def energy(threshold):
            finite, tail = source.ap_product_distribution(caps, source.rootceil(F(threshold)))
            return (G * tail[2] - threshold * tail[0]
                    + sum(prob * n * n * min(square(F(threshold, n * n)), G - 1)
                          for n, prob in finite.items())) / survival

        gamma, t81 = 16 + energy(16), energy(81)
        hs = {h: factor * source.product_hinge(original + caps, F(h)) / survival
              for h in (5, 6, 7, 8)}
        joint = source.WHOLE_CONST + source.AC * (targets['Gamma13'] - 16)
        joint += sum(c * hs[h] for h, c in source.WEIGHT17)
        joint += source.P17 * sum(c * hs[h] for h, c in source.WEIGHT19)
        joint += source.EXTRA5 * hs[5]
        row = {'branch': name, 'survival_lower': survival,
               'Gamma13': gamma, 'T13_81': t81, 'bound': joint}
        require(all(row[key] <= targets[key] for key in targets), 'Every complete new-law fallback bound')
        rho = min(rho, survival)
        rows.append(row)
    require(len(rows) == len({r['branch'] for r in rows}) == 8, 'Eight distinct source branches')
    return rows, rho


def core_errors(kc, source_inputs, gamma, rho, t81, joint):
    """Use generic KC factors/step without setting any source module globals."""
    G0, D0 = F(source_inputs['G']), 1 / F(source_inputs['survivor_density_lower'])
    require((G0, D0) == (F(3849, 106), F(432, 53)), 'Same complete actual357 source')
    D = F(20, 7) * D0 / rho
    rows = []
    for heights, current in (([20] * 7, (8, 8)), ([17, 10, 8, 7, 6, 6, 6], (6, 6))):
        box = list(zip((3, 5, 7, 11, 13, 17, 19), heights))
        b3, b4 = box[:3], box[:4]
        e0w = D0 * (G0 * kc.factors(b3, False)[0] + kc.factors(b3, True)[0])
        e0m = 2 * D0 * kc.factors(b3, False)[0]
        ew = F(61, 42) * (F(23, 15) * e0w + kc.step(11, 4, b3, heights[3], D0, G0, True))
        ew += kc.step(13, 5, b4, heights[4], F(5, 3) * D0, F(23, 15) * G0, True)
        em = e0m + kc.step(11, 4, b3, heights[3], D0, F(1), False)
        em += kc.step(13, 5, b4, heights[4], F(5, 3) * D0, F(1), False)
        incoming_w, incoming_m = (ew + gamma * em) / rho, 2 * em / rho
        a2 = kc.step(17, 8, box[:5], current[0], D, gamma, True)
        a0 = kc.step(17, 8, box[:5], current[0], D, F(1), False)
        b2 = kc.step(19, 8, box[:6], current[1], 2 * D, F(89, 64) * gamma, True)
        b0 = kc.step(19, 8, box[:6], current[1], 2 * D, F(1), False)
        mask = F(59, 45) * a2 + b2 + 483 * (a0 + b0)
        incoming = F(5251, 2880) * incoming_w + 242 * incoming_m
        full = prod(F(p * (p + 1), (p - 1) ** 2) for p, _ in box)
        head = prod(1 + sum(F(2 * a + 1, p ** a) for a in range(1, k + 1)) for p, k in box)
        test = F(18, 5) * D * (full - head)
        total = mask + incoming + test
        allowance = 403 - t81 - total
        scaled = 1000000 * allowance
        safe = F(scaled.numerator // scaled.denominator, 1000000)
        if safe == allowance:
            safe -= F(1, 1000000)
        require(0 < total and 0 < safe < allowance, 'Strict new-law sufficient allowance')
        P5, P6 = prod(k + 1 for _, k in box[:5]), prod(k + 1 for _, k in box[:6])
        rows.append({'box': box, 'current': current, 'steps': [a2, a0, b2, b0],
                     'source': [incoming_w, incoming_m], 'incoming_mass_coefficient': 242,
                     'mask': mask, 'incoming': incoming, 'test': test, 'total': total,
                     'test_labels': prod(k + 1 for _, k in box),
                     'forbidden_label_count_upper': [P5 - 1, current[0] * P5, current[1] * P6],
                     'common_period': prod(p ** max(k, current[0] if p == 17 else current[1] if p == 19 else k)
                                           for p, k in box),
                     'allowance': allowance, 'safe_allowance': safe, 'gap': joint - allowance,
                     'criterion': 'Joint frontier <= safe_allowance implies strict negative Q; using exact allowance requires <.'})
    require(rows[1]['test_labels'] == 4889808
            and sum(rows[1]['forbidden_label_count_upper']) == 4889807, 'Complete unequal-box label counts')
    return {'G357': G0, 'D357': D0, 'Gamma13': gamma, 'rho13': rho, 'D13': D}, rows

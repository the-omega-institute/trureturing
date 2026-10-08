---
slug: bona-maga-richey-2026-half-frequency-balanced-borders
bibkey: bonamagarichey2026letter
doi: null
url: https://arxiv.org/abs/2606.06655v2
triage: theorem
motivation_gids:
  - D5/S1/Words/Forbidden/BonaMagaRicheyHalfFrequency.result
---

# Half letter frequency characterizes balanced borders

## Problem

Miklós Bóna, Balázs Maga and Jacob Richey, *Letter frequency in shifts of finite type with one forbidden word*, arXiv:2606.06655v2, Section 6, Conjecture 6.1: “A word $w$ has $\rho^w = 1/2$ if and only if $w$ has balanced borders. The same holds with $\rho^w$ replaced by $q^w$.”

Only the first sentence is settled. For every nonempty binary word $w$, let $\Omega_m^w$ be the length-$m$ binary words without $w$ as a factor and let

$$
\rho_m^w=\frac{\sum_{u\in\Omega_m^w}|u|_1}{m|\Omega_m^w|}.
$$

A border is a nonempty prefix that is also a suffix, including $w$ itself. Balanced borders means $2|b|_1=|b|$ for every border $b$. Since the source defines $\rho^w$ as the limit if it exists, the literal settlement is $\rho_m^w\to1/2$ if and only if every border is balanced; no independent convergence assumption is added.

## Motivation

`D5/S1/Words/Forbidden/BonaMagaRicheyHalfFrequency.result` proves the characterization for every nonempty `List Bool`, with `true` representing the letter 1 and `List.IsInfix` representing factor containment. Issue #14224 is the preregistered external open-problem route.

## Gap

The source's Proposition 3.3 proves the balanced-border direction and Theorem 3.5 treats one-sided border bias. The remaining issue is cancellation between borders with opposite imbalance. The literature screen in #14224 finds no settlement in its searched scope. Unconditional convergence and the $q$ sentence are outside the formal claim.

## Route

Let $n=|w|$, $B$ be the nonempty border lengths, $d_j=2|w_{[1,j]}|_1-j$, $C(x)=\sum_{j\in B}x^j$, $H(x)=\sum_{j\in B}d_jx^j$ and $P(x)=(2-x)C(x)-x$.

The first-hit decomposition and overlap bijection prove the cleared-denominator counting identity (`ForbiddenWordCounting.forbidden_word_counting_identity`). A take/drop injection proves count submultiplicativity (`ForbiddenWordGrowth.avoidCount_submultiplicative`); Mathlib's `Subadditive.tendsto_lim`, used through `growthLog_tendsto`, supplies the growth limit. The scalar counting identity and a divergent geometric lower bound prove `ForbiddenWordRationalBoundary.growthRadius_denominator_zero` without a Pringsheim premise. Escaping length-weighted Abel averages turn convergence to $1/2$ into a vanishing boundary signed moment. `BorderImbalanceExclusion.unbalanced_hEval_ne_zero` contradicts that vanishing for an unbalanced word of length at least three. The short words are handled directly. Balanced borders yield exact half frequency at every positive length.

## Falsifier

A nonempty word whose averages tend to $1/2$ but which has an unbalanced border, or a balanced-border word whose averages do not tend to $1/2$, would contradict the delivered theorem in its stated Lean definitions. The finite gcd search below corroborates the algebraic exclusion; it is not a proof for unbounded lengths.

## Evidence

The six Lean modules and their Scribe definitions encode the literal average and border predicates. The settling declaration is `D5/S1/Words/Forbidden/BonaMagaRicheyHalfFrequency.result : claim`. The claim is universal in $w\ne[]$ and has no unconditional limit-existence premise. The source locators and verbatim definitions are in `Library/Words/bonamagarichey2026letter.md`.

## Triage

### What the settlement shows

1. **Proved — kernel-checked declaration.** Opposite border biases cannot cancel at the growth root. If $k$ is the longest border with $d_k\ne0$, a bit flip makes $d_k\ge1$. Prefix increments give $d_j\ge1-(k-j)$ and hence

   $$
   H(\lambda)\ge F_k(\lambda)>0,\qquad
   F_k(x)=x^k-\sum_{j=1}^{k-2}(k-j-1)x^j.
   $$

   The identity

   $$
   (x-1)^2F_k(x)=-(2-x)x^{k+1}+(k-1)x^2-(k-2)x
   $$

   and the root envelope $(2-\lambda)\lambda^{n-1}\le1$ make the lower bound positive; $k=1,2$ are immediate. Evidence: `D5/S1/Words/Forbidden/BorderImbalanceExclusion.unbalanced_hEval_ne_zero`, its private lower-envelope identity and positivity chain, and `root_equation_envelope`. The source's Guibas–Odlyzko irreducibility question is unnecessary for this exclusion and remains outside the settlement.

2. **Proved — kernel-checked declarations.** Exceptional words of length at most two are covered, including $01$ and $10$. `BalancedBordersHalfFrequency.singleton_not_tendsto_half` excludes singleton words. `not_tendsto_half_11` and the settling module's private `not_tendsto_half_00` exclude the constant pairs. Its private `balanced_mixed_pair` and `BalancedBordersHalfFrequency.balanced_tendsto_half` cover both mixed pairs. All are on `BonaMagaRicheyHalfFrequency.result`'s proof path. In fact balanced words have $\rho_m^w=1/2$ for every $m>0$ (`balanced_rho_eq_half`, private), so convergence follows without a rate estimate.

3. **Open — formalization boundary, source assertion.** Existence of $\rho^w$ for every nonempty $w$ is not proved by this delivery. The source asserts existence; the open status records the missing Lean result, not a claim that the literature lacks it. The delivered characterization only needs the forward premise $\rho_m^w\to1/2$.

4. **Proved — paper argument under its root hypotheses; not a Lean theorem of this delivery.** When the limiting frequency exists, the simple dominant-root reduction for $n\ge3$, with $2C(\lambda)^2-\lambda^2C'(\lambda)>0$, gives

   $$
   2\rho^w-1=-\frac{\lambda H(\lambda)}{2C(\lambda)^2-\lambda^2C'(\lambda)}.
   $$

   For clarity, its algebraic derivation uses the weighted correlation $C_z(x)=\sum_{j\in B}x^jz^{|w|_1-|w_{[1,j]}|_1}$ and the root equation $((1+z)-x)C_z(x)=xz^{|w|_1}$. At $z=1$, logarithmic differentiation gives $x'(1)/x=\rho^w$ for the simple dominant root, and $2\partial_zC_z|_{z=1}=2|w|_1C-H-xC'$. Substitution and $(2-\lambda)C(\lambda)=\lambda$ give the displayed formula. Identification of the root derivative with the limiting frequency and positivity of the denominator use the simple-root asymptotic argument recorded in #14224. These are paper-level hypotheses, not claimed as kernel-checked here. The formal necessity proof instead uses `scalar_counting_identity`, `scalar_length_identity`, `scalar_moment_identity` and escaping Abel averages, so it does not require this formula or simplicity. The singleton and constant-pair limits are direct; mixed pairs have $\lambda=1$ and exact half frequency, outside the simple-root reduction.

5. **Open — published conjecture.** The $q$ clause of Conjecture 6.1 is not settled. The source's results involving $\rho^w=1/2$ gain the characterization in item 1; no conclusion about $q^w$, irreducibility, or unconditional convergence follows from this theorem. A uniform density formula remains a separate formalization target.

6. **Computed — exact rational polynomial arithmetic.** For all 30,608 binary words of lengths $1$ through $14$ with $H\not\equiv0$, $\gcd(P,H)=t$ as a monic polynomial over $\mathbb Q$. The scope contains 32,766 total words, 2,158 with $H\equiv0$, and 1,558 distinct nonzero polynomial pairs. SymPy 1.14.0 reports zero failures. Command: `python3 /Users/auric/.sshx/8a8b0a4b854c38aa231bd8d5/attempt-1/gcd-border-check.py`; exit 0. Script SHA-256: `9c9980a09ee60229702965abd086ca21b66a540e6c971af9abcca99ff3c4e859`. Its source is below; save it as `gcd-border-check.py` and run `python3 gcd-border-check.py`. The extension of this gcd statement to all lengths is **open**, with no uniform computational or Lean proof asserted.

```python
import sympy as s
import json, sys, hashlib, pathlib
from itertools import product
x=s.Symbol("t")
expected=s.Poly(x,x,domain=s.QQ)
checked=0;balanced=0;total=0;cache={};failures=[]
for n in range(1,15):
    for word in product((0,1),repeat=n):
        total+=1
        borders=[j for j in range(1,n+1) if word[:j]==word[n-j:]]
        c=[0]*(n+1);h=[0]*(n+1);p=[0]*(n+2)
        for j in borders:
            c[j]=1;h[j]=2*sum(word[:j])-j
        if not any(h):
            balanced+=1;continue
        for j,a in enumerate(c):
            p[j]+=2*a;p[j+1]-=a
        p[1]-=1
        key=(tuple(p),tuple(h))
        if key not in cache:
            P=s.Poly.from_list(p[::-1],gens=x,domain=s.QQ)
            H=s.Poly.from_list(h[::-1],gens=x,domain=s.QQ)
            cache[key]=P.gcd(H)==expected
        checked+=1
        if not cache[key]:failures.append({"word":"".join(map(str,word)),"P":p,"H":h})
    print(json.dumps({"length":n,"total_words":total,"H_nonzero_words":checked,"failures":len(failures)}),flush=True)
result={"sympy_version":s.__version__,"maximum_length":14,"total_words":total,"balanced_words":balanced,"H_nonzero_words":checked,"distinct_polynomial_pairs":len(cache),"gcd_is_monic_t_for_every_H_nonzero_word":not failures,"failures":failures,"P_definition":"(2-t) * sum_{j in nonempty border lengths} t^j - t","H_definition":"sum_{j in nonempty border lengths} (2*ones(prefix j)-j) * t^j","domain":"QQ","script_sha256":hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()}
pathlib.Path(__file__).with_suffix(".json").write_text(json.dumps(result,indent=2))
print(json.dumps(result),flush=True)
sys.exit(0 if not failures and checked==30608 else 1)
```

## ASSUMED-UNVERIFIED

The complete density formula and unconditional convergence are not delivered Lean results. The paper argument uses simple-root asymptotics, while the kernel proof of the characterization avoids that obligation. Information-escape registration is paused under CLAUDE.md §3.9.

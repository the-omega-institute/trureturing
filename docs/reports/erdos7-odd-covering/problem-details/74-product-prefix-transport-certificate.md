[Index](../../../../Problems/erdos-7-odd-covering-systems.md)

# Product prefix transport for one common source law

The missing-anchor audit left a finite interface obligation: coordinatewise
Haar averaging had to be upgraded to the mixed original-cylinder events used
by one common transported submeasure. The standard-library checker
[`verify_product_prefix_transport.py`](../frontier/cover-geometry/verify_product_prefix_transport.py)
discharges that finite lemma for the three interfaces used by the current
source rows.

Let (p_i\le q_i) be odd primes and let (h_i) be finite heights. For each
coordinate choose an arbitrary digit-shift table
(\sigma_i\in(\mathbb Z/q_i\mathbb Z)^{h_i}), and map source base-(p_i)
digits to target base-(q_i) digits by addition modulo (q_i). The checker
verifies, for every shift table and every mixed target cylinder using any
subset of coordinates and any depths (e_i\le h_i), that the pullback is
exactly one mixed source cylinder or is empty. It also checks the complete
event vector for a family of distinct target moduli, so original labels are
not replaced by marginal events.

For every target atom (y), the number of pairs
((\sigma,x)) with (F_\sigma(x)=y) is constant. Thus, writing
(X=\prod_i\mathbb Z/p_i^{h_i}\mathbb Z), (Y=\prod_i\mathbb
Z/q_i^{h_i}\mathbb Z),

\[
\frac1{|\Sigma|}\sum_\sigma H_X(F_\sigma^{-1}\{y\})=H_Y(\{y\}).
\]

Consequently, if every source row (\mu_\sigma) has atom bound
\(\mu_\sigma(\{x\})\le\alpha/|X|\), the averaged pushforward has
\(\nu(\{y\})\le\alpha/|Y|\), and summing atoms gives the target marginal-cap
inequality for every target subset. This is one common averaged law; no
separate optimization over target marginals is used.

The exact run is:

```text
python3 -I docs/reports/erdos7-odd-covering/frontier/cover-geometry/verify_product_prefix_transport.py
```

The three profiles pass with source/target state counts \((45,175)\),
\((45,63)\), and \((105,165)\); the atom-preimage counts are (45,45,105).
The run checks 97,069 mixed-cylinder instances and 28,035 event-vector
instances. The result is finite-height transport evidence only. It does
not prove the source survival rows, root orientation, attachment budgets,
block-tree gluing, later-prime monotonicity, or unrestricted
Erdős--Selfridge #7.

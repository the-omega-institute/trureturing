# Even expanding paths in the original centered source

## Abstract

Actual source paths: actual even expanding paths force every oriented prefix into [0,r] and their physical energy below the consumed endpoint's energy.

**Theorem 1.1 (Source-forced prefix and exponential estimates).**

$$\forall k \in \mathrm{Nat},\; \forall t \in \mathrm{Nat},\; \forall p \in \operatorname{Fin}\left(k\right),\; \forall m \in \mathrm{Nat},\; \forall negative \in \mathrm{Bool},\; \left(3 \le k \land \left(2 \le m \land \left(\operatorname{mod}\left(m, 2\right) = 0 \land \left(0 < 3 \cdot \operatorname{orient}\left(negative, \operatorname{actualSource}\left(k, t, p\right)\right) - \operatorname{modulus}\left(k\right) \land \left(\forall j \in \mathrm{Nat},\; j < m \Rightarrow \operatorname{Large}\left(k, t, \operatorname{phase}\left(p, j\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(0 < \operatorname{orient}\left(negative, \operatorname{actualSource}\left(k, t, \operatorname{phase}\left(p, m\right)\right)\right) \land \left(\operatorname{Large}\left(k, t, \operatorname{phase}\left(p, m\right)\right) \land \left(\left(\forall n \in \mathrm{Nat},\; 0 \le \operatorname{orient}\left(negative, \operatorname{sum}\left(\operatorname{map}\left(\operatorname{actualSource}\left(k, t\right), \operatorname{take}\left(n, \operatorname{path}\left(p, m\right)\right)\right)\right)\right) \land \operatorname{orient}\left(negative, \operatorname{sum}\left(\operatorname{map}\left(\operatorname{actualSource}\left(k, t\right), \operatorname{take}\left(n, \operatorname{path}\left(p, m\right)\right)\right)\right)\right) \le \operatorname{orient}\left(negative, \operatorname{actualSource}\left(k, t, \operatorname{phase}\left(p, m\right)\right)\right)\right) \land \left(\operatorname{abs}\left(\operatorname{actualSource}\left(k, t, \operatorname{phase}\left(p, m\right)\right)\right) - \operatorname{abs}\left(\operatorname{actualSource}\left(k, t, \operatorname{phase}\left(p, m - 2\right)\right)\right) = 2^{m - 2} \cdot \left(3 \cdot \operatorname{orient}\left(negative, \operatorname{actualSource}\left(k, t, p\right)\right) - \operatorname{modulus}\left(k\right)\right) \land \left(\operatorname{intCast}\left(m\right) - 1 \le \operatorname{abs}\left(\operatorname{actualSource}\left(k, t, \operatorname{phase}\left(p, m\right)\right)\right) - \operatorname{abs}\left(\operatorname{actualSource}\left(k, t, \operatorname{phase}\left(p, m - 2\right)\right)\right) \land \operatorname{sum}\left(\operatorname{map}\left(\operatorname{sourcePowerEnergy}\left(k, t\right), \operatorname{path}\left(p, m\right)\right)\right) < 3^{\operatorname{natAbs}\left(\operatorname{actualSource}\left(k, t, \operatorname{phase}\left(p, m\right)\right)\right)}\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/ExpandingSourcePath.expanding_path_estimates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source is exactly SourceWidth.actualSource(k,t,p) = centered(2^k-1,2^p*t), with physical p in Fin(k). Q=2^(k-2), N=4Q-1, C=N/2=2Q-1, k>=3. LARGE means Q<=|s(p)|. phase(p,j) has value (p.val+j) mod k, and path(p,m) is its first m physical occurrences. The omitted proof argument of phase/path is only 0<k. sourcePowerEnergy in the displayed formula abbreviates the lambda q => 3^(natAbs(actualSource k t q)); it is notation here, not an added Lean definition.

The orientation flag changes signs of values only. Its premise d=3*orient(s(p))-N>0 forces a positive oriented start. The LARGE and centered-bound hypotheses of the private recurrence lemma are discharged by the native source, rather than passed through as an uninstantiated scalar model. phase_step uses SourceWidth.centered_double for ordinary edges and centered_full_period for the physical seam.

The recurrence induction derives both sign alternation and 3*w_j = (N for even j, -N for odd j) + 2^j*d. A second induction derives 3*F_j = (0 for even j, N for odd j) + (2^j-1)*d. Since d is a positive integer and j<=m with m even, these imply 0<=F_j<=r=w_m. Taking min(n,m) proves the bound for every natural take, including empty and overlength takes.

The largest inserted magnitude is M=|w_(m-2)|: even-indexed magnitudes increase, and each odd-indexed magnitude is below N/3. The exact integer gap r-M=2^(m-2)*d is proved from the two native even-index equations. Induction gives 2^(m-2)>=m-1 and 3^(m-1)>m, hence sum_(j<m)3^|s(a_j)| <= m*3^M < 3^r. The desired energy drop is a conclusion, never a premise.

This module supplies the analytic estimates consumed by MixedSuffixEnergy.mixed_suffix_energy_exchange. The physical unusedness, distinctness, prefix A, and inventory argument belong to that consumer. No unit, primitivity, distinct-value, or full numerical-period assumption occurs. This path theorem does not cover d=0 or k<3, and does not assert that an eligible path exists in an arbitrary incomplete word.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/ExpandingSourcePath.expanding_path_estimates`
- Dependency: [D5/S3/Combinatorics/Circle/SourceWidth](SourceWidth.md)

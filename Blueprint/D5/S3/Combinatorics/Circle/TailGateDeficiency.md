# Two gates sharing one physical tail

## Abstract

An original ALL-Legal minimum forces a sharp sign-supply deficiency at one of two retained negative gates.

Let f be the actual centered source on all physical Fin(k) labels. Keep the literal signed prefix A in W=A,[x],T0,[y],T1,[z1],T2,[z2],E, where n=rho(p), x=rho^2(p), p is positive, n is LARGE, N<3f(p), p and n are unused, all four T/E batches are SMALL, z1 and z2 are negative LARGE, and -f(y)>f(p). Legal W is a minimum of the original lexicographic objective J over EVERY Legal physical list. No numerical injectivity, least numerical period, clearance condition or supplied old-margin hypothesis is assumed. Zeros, coincident numerical values and every physical label remain in scope.

**Definition 1.1 (Complete physical sign pools).**

Lean statement: `D5/S3/Combinatorics/Circle/TailGateDeficiency.signPool`

*Formalization.* `D5/S3/Combinatorics/Circle/TailGateDeficiency.signPool` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

signPool(f,T,v) filters every occurrence i of T satisfying 0<f(i)<=v. The negative pool uses -f. Mass sums occurrences, so distinct labels with equal values contribute separately.

**Theorem 1.2 (Sharp gate-specific deficiency).**

Lean statement: `D5/S3/Combinatorics/Circle/TailGateDeficiency.actualSource_threeNegative_twoGate_tail_deficiency`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/TailGateDeficiency.actualSource_threeNegative_twoGate_tail_deficiency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write P=f(p), D=|f(n)|, B=C-P, delta=-f(y)-P>0. Let cj be the OLD departure before zj, aj=cj+f(zj) its arrival, Zj=-f(zj), theta_j=C-cj, and gamma_j=C-Zj+1. The theorem proves theta_1+Mminus(gamma_1)<delta OR theta_2+Mplus(gamma_2)<delta, where Mminus and Mplus are the masses of the complete negative and positive sign pools of the SAME actual T2. The original minimum derives B<h<D and aj>B: a legal fresh LARGE append would lower G, and an old arrival at most B permits prefix truncation followed by [p,n], also lowering G. Thus gamma_j>=B+2.

If both supplies were sufficient, first crossing at target max(0,delta-theta_j), with width C-Zj, would select negative mass nsel and positive mass psel. Empty targets use the empty list. The sharp cutoff gamma_j is width plus one; the upper selected mass is exactly delta+aj. Signs make the two physical selections disjoint. One complement R satisfies (Nminus++R++Pplus).Perm T2. Set S0=T0++T1++Nminus and S2=E++Pplus. Starting after the fresh [p,n] at b=mass(A)+P-D, the complete batches and retained gates have endpoints S0: b to c1+delta-nsel; z1: c1+delta-nsel to a1+delta-nsel; R: a1+delta-nsel to c2+delta-psel; z2: c2+delta-psel to a2+delta-psel; S2: a2+delta-psel to h+delta. The second shift cancels nsel because both selections share R. Every endpoint lies in [0,C]; the existing SMALL ordering theorem orders each COMPLETE batch between them.

The competitor retains A literally and satisfies (V++[x,y]).Perm(W++[p,n]). Exact physical inventory gives G(V)=G(W), U(V)=U(W), and H(V)+3^|f(x)|+3^|f(y)|=H(W)+3^|f(p)|+3^|f(n)|. Native geometry gives 3^|f(p)|+3^|f(n)|<3^|f(x)|, hence strict H and J descent. This contradicts the original minimum and proves the disjunction. U counts all unused physical labels.

This is a necessary obstruction for Circle C3.1. It does not prove that both favorable supplies exist. Eliminating the deficient branch still requires transporting actual resources that may lie across LARGE gates inside arbitrary signed A, or a different exact legal exchange. Source localization, relay closure and full arbitrary-A C3.1 are not conclusions of this theorem.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/TailGateDeficiency.actualSource_threeNegative_twoGate_tail_deficiency`
- Truth anchor: `D5/S3/Combinatorics/Circle/TailGateDeficiency.signPool`
- Dependency: [D5/S3/Combinatorics/Circle/FirstNegativeShiftExchange](FirstNegativeShiftExchange.md)
- Dependency: [D5/S3/Combinatorics/Circle/PositiveSmallReturnExchange](PositiveSmallReturnExchange.md)

# Output-extinction curvature and same-strength short-alphabet loss

## 1. Inherited experiment and exact scope

**Definition 1.1 (the retained original problem).** The original object is the normalized twelve-history stopped classical–quantum experiment of [OE, Theorem 1.4][OE]. The histories are
$$
(y,e,n)\in\{5,16,27\}\times\{\pm1\}^2,
$$
with the original five failure Borel components in label order $(0,1,2,3,13)$, the original live coherences, singular-time, wrong-support, abort and zero-target components, and the HALF stopped-output trace norm. The first-event clock is $6+a$, $a\in[0,1]$. The contrast, sharp JOINT cost, whole-fibre activity and report alphabet are those of [OE, Definitions 1.1–1.3]. No source prior, survival conditioning, postselection, copies, retries, history oracle or uncounted accessible share is admitted.

Put $t=1000$ and $A=\log 1001$. Let $\mathcal T_A(s)$ denote the original actual-label total-variation optimum at fixed contrast $s$ under the original minimax error, sharp JOINT cost and activity bound.

**Assumption 1.2 (separate retained interfaces).** The following are hypotheses, each retained with its scope from [CG], [JR], [FA], [RC] and [OE].

1. The isolated consistent source root, its stipulated ranks, source dictionary and TP identity are the ones in [OE, Assumption 1.2(1) and Definition 2.1]. The surrounding source box is not asserted to consist of roots or TP points.
2. [CG, §§13–17] supplies the original full HALF stopped-output minimax identification and its averaged-live consequences.
3. [JR, §§34–42] supplies the sharp worst-history JOINT cost and the unaveraged supported real equality face.
4. [FA, §§67–70, 77–78] and [RC, §75] supply full-complex multi-Kraus actual-label rigidity, the rank-two capacity, the same-law reduction for every admissible error/cost optimizer, and the coherent one-high completion. A hidden Kraus index is not an actual label.
5. [OE, §§4–7 and 9] supplies the unique event and its two analytic signed contact sections, the full-circle dual certificate with seven separated event zeros, positive old weights, seven-column moment independence, positive restricted Hessian, nonzero contrast tangent and the transverse signs. It also supplies the original common constructor, all five Borel/passive-reference maps, whole-fibre activity and the compulsory positive high acquisition.

These assumptions remain conditional interfaces. They do not discharge source isolation, minimax, sharp JOINT, the unaveraged equality-face bridge, full-complex rigidity, physical realization, native permissions, all-budget or all-contrast coverage, or any strong-budget claim.

**Definition 1.3 (the selected event).** Let
$$
I=[190.449003333,190.449005333],
\qquad
190.44900433290<\lambda_e<190.44900433292
$$
be the inherited event interval. On the seven section the seventh indexed weight $p_4$ is positive for $\lambda<\lambda_e$ and vanishes at the event. On the six section contact $4$ is retained only as an unused stationary direction; its normalized unused gap is negative below the event and positive above it. The event strength and value satisfy the inherited enclosures
$$
0.12520584446759<s_e<0.12520584446760,\qquad
0.08594665979087<V_e<0.08594665979089.
$$
No midpoint calculation is used as a certificate in this volume.

Let $O=\{0,1,2,3,5,6\}$ be the six old contacts. For a physical branch $b\in\{6,7\}$ write
$$
k_b(\lambda)=\sum_{i\in b}p_i(\lambda)|u_i(\lambda)|,\qquad
s_b(\lambda)=\frac{s_0}{\sqrt\alpha}k_b(\lambda),
$$
and let $V_b$ be the HALF value. The branch identities, signs and all denominators are those of [OE, §§2–5].

## 2. Response equations at the disappearing contact

**Definition 2.1 (contact gap and response coordinates).** In the fixed local sign charts of [OE, Definition 4.1], set
$$
g_i=Y\cdot\Gamma_i-\lvert H_i\rvert-\lambda\lvert u_i\rvert .
$$
At every occupied contact $g_i=g_{i,x}=0$. At the event the unused contact $4$ also satisfies these two equalities. Let $v=\Gamma_4$ and $k_4=|u_4|$ at the event, and let $d_4>0$ be its normalized clearing denominator. Let $A$ be the differential of the eight-moment map in the six occupied contact variables at the event, let $H$ be the corresponding Lagrangian Hessian on those variables, and let $q=Dk$ be the differential of the contrast functional. The inherited geometry gives
$$
\operatorname{rank}A=8,\qquad
H\succ0\ \text{on }\ker A,\qquad
q|_{\ker A}\ne0.
$$

Write $z_6'$, $z_7'$ for the survivor-variable derivatives with respect to $\lambda$ at the event, and put
$$
h=z_7'-z_6',\qquad \Delta Y=Y_7'-Y_6'.
$$
The seven derivative $p_4'$ is the derivative of the signed seventh weight. The six unused-gap derivative is
$$
d_6'=\frac{d}{d\lambda}
\left(Y_6\cdot\Gamma_4-\lvert H_4\rvert-\lambda\lvert u_4\rvert\right).
$$

**Proposition 2.2 (differentiated event systems).** At the event,
$$
\begin{aligned}
H z_6'+A^T Y_6'&=q,& A z_6'&=0,\\
Ah&=-v\,p_4',& Hh+A^T\Delta Y&=0,\\
v^T\Delta Y&=-d_6'.
\end{aligned}
$$
Moreover,
$$
d_6'=\frac{P_4'}{d_4}>0,\qquad p_4'<0,
$$
where $P_4'$ is the cleared unused-stationarity derivative from [OE, Definition 4.1].

**Proof.** The six unused normalized gap is $P_4/d_4$. At the event $P_4=0$ and $P_{4,x}=0$, so the quotient rule removes both the denominator derivative and the motion of the unused angle:
$$
d_6'=P_4'/d_4.
$$
The strict sign is inherited from the cleared derivative certificate and $d_4>0$. Along the seven section, differentiating $g_4=0$ gives
$$
v^TY_7'-k_4=0.
$$
Along the six section the stationary unused equation gives
$$
d_6'=v^TY_6'-k_4.
$$
Subtracting yields $v^T\Delta Y=-d_6'$.

Differentiate the eight moments and the occupied stationarity equations. The disappearing atom contributes $v\,p_4'$ to the moment derivative; its angular motion is multiplied by $p_4=0$. Subtracting the six equations from the seven equations gives $Ah=-vp_4'$ and $Hh+A^T\Delta Y=0$. The first displayed six equations are the same differentiated stationarity and moment equations with $q=Dk$. This calculation keeps the moving unused angle in the cleared stationarity equation; it does not set an off-event normalized gap to zero. $\square$

**Theorem 2.3 (response identity and positive susceptibilities).** At the event,
$$
k_7'-k_6'=-p_4'd_6'=h^THh>0,
\qquad
k_7'>k_6'>0.
$$

**Proof.** From the six response equation and the equation for $h$,
$$
\begin{aligned}
q^Th
&=z_6'^THh+Y_6'^TAh\\
&=-z_6'^TA^T\Delta Y-p_4'v^TY_6'\\
&=-p_4'v^TY_6',
\end{aligned}
$$
because $Az_6'=0$. The disappearing contact contributes $k_4p_4'$ to the seven contrast derivative, hence
$$
k_7'-k_6'
=q^Th+k_4p_4'
=p_4'(k_4-v^TY_6')
=-p_4'd_6'.
$$
Also,
$$
h^THh=-(Ah)^T\Delta Y
=p_4'v^T\Delta Y
=-p_4'd_6'.
$$
The two strict transverse signs therefore give $h^THh>0$.

The vector $z_6'$ lies in $\ker A$. Since $q|_{\ker A}\ne0$, it is nonzero, and
$$
k_6'=q^Tz_6'=z_6'^THz_6'>0.
$$
Consequently $k_7'=k_6'-p_4'd_6'>k_6'>0$. The positive definiteness of $H$ is used only on $\ker A$; $h$ is generally not tangent because $Ah=-vp_4'\ne0$. No positive seven-ray Hessian at the zero weight is assumed. $\square$

## 3. HALF curvature and the event regularity

**Proposition 3.1 (branch value derivative).** On either analytic branch,
$$
2V_b-H_{\rm high}=J_b=Y_b\cdot B(1000)-\lambda k_b,
\qquad
J_b'=-\lambda k_b',
$$
and therefore
$$
\frac{dV_b}{ds}=-\frac{\lambda\sqrt\alpha}{2s_0},
\qquad
\frac{d^2V_b}{ds^2}
=-\frac{\alpha}{2s_0^2k_b'}.
$$

**Proof.** At occupied contacts the dual gap vanishes, so the endpoint height contribution equals the contact dual value. Summing against the eight moments gives the first identity. Differentiating the occupied moment and stationarity equations, multiplying the survivor stationarity by the survivor velocity, and using the vanishing gap of the disappearing atom on the seven branch gives $Y_b'\cdot B(1000)=k_b$. Hence $J_b'=-\lambda k_b'$.

Since $s=s_0k/\sqrt\alpha$, inversion is legitimate on both sides by Theorem 2.3. Differentiating $2V_b'=-\lambda k_b'$ with respect to $s$ gives the stated first and second derivatives. The event value, dual vector and first derivative agree because the two sections are the exact embeddings of the same event law. $\square$

**Theorem 3.2 (one-sided curvature jump).** The selected original value is continuous and $C^1$ at $s_e$, analytic on each side, and not twice differentiable there. Its left-minus-right second derivative is
$$
\left.\frac{d^2\mathcal T_A}{ds^2}\right|_{s_e^-}
-
\left.\frac{d^2\mathcal T_A}{ds^2}\right|_{s_e^+}
=
\frac{\alpha}{2s_0^2}
\left(\frac1{k_6'}-\frac1{k_7'}\right)>0.
$$

**Proof.** The seven section is physical on the lower-strength side and the six section on the higher-strength side. Proposition 3.1 gives the common value and first derivative. Theorem 2.3 gives $k_7'>k_6'>0$, so
$$
-\frac{\alpha}{2s_0^2k_7'}
+
\frac{\alpha}{2s_0^2k_6'}>0.
$$
Thus the two analytic extensions have different second derivatives. The original full optimum equals the physical selected branch by the inherited dual and constructor interfaces in [OE]. $\square$

## 4. Compact six-atom relaxation and event localization

**Definition 4.1 (the lifted six-atom class).** Let
$$
X=S^1\times[0,1],
$$
where $(u,v)\in S^1$ is a direction and $\xi$ is the endpoint interpolation parameter. Let $\mathcal Q_6$ be the laws on $X$ represented by at most six atoms. For $(u,v,\xi)$ use the eight lifted columns $\Gamma_\xi$ and the lifted height
$$
H_\xi=\ell+t\,c\,\xi f
$$
from [OE, Definition 3.1]. Impose the eight moment equations
$$
\int_X\Gamma_\xi\,d\mu=B(1000)
$$
and the contrast constraint
$$
K(\mu)=\int_X|u|\,d\mu\ge\kappa.
$$
The objective is
$$
J(\mu)=\int_X|H_\xi|\,d\mu.
$$
The corresponding HALF objective is $(H_{\rm high}+J(\mu))/2$; the high term is fixed by the retained source interface.
A zero coefficient is allowed as padding; the class therefore includes all original competitors with at most six supported nonzero low actual labels under Assumption 1.2.

**Lemma 4.2 (compactness).** The feasible part of $\mathcal Q_6$ is compact, and $J$ attains its maximum.

**Proof.** The space of padded six-atom laws is the continuous image of the compact product $\Delta_5\times X^6$. The capacity denominator is strictly positive on the circle, so the columns $\Gamma_\xi$, the height $H_\xi$ and $|u|$ are continuous. The eight moment equalities and the closed inequality $K\ge\kappa$ define a closed subset. The objective is continuous and hence attains its maximum. $\square$

**Theorem 4.3 (unique event law and forced localization).** At $\kappa_e=k(\lambda_e)$ the event law is the unique merged equality law in $\mathcal Q_6$. For every sequence $\kappa_n\to\kappa_e$ from below, every sequence of global maximizers in $\mathcal Q_6$ converges weakly to that law. Consequently, after shrinking the neighborhood, every maximizer has exactly one positive atom near each of the six old contacts and no atom near contact $4$.

**Proof.** The event dual inequality of [OE, Theorem 6.3] gives, for each endpoint sheet,
$$
Y_e\cdot\Gamma_\eta\ge |H_\eta|+\lambda_e|u|.
$$
Convexity in $\xi$ and $\Gamma_\xi=(1-\xi)\Gamma_0+\xi\Gamma_1$ give
$$
|H_\xi|
\le (1-\xi)|H_0|+\xi|H_1|
\le Y_e\cdot\Gamma_\xi-\lambda_e|u|.
$$
After integration,
$$
J(\mu)\le Y_e\cdot B(1000)-\lambda_eK(\mu)
\le Y_e\cdot B(1000)-\lambda_e\kappa_e=J_e
$$
at the event, where $J_e$ denotes the event low-label objective. Equality forces $K=\kappa_e$, equality in both endpoint inequalities wherever the law has mass, and zero endpoint gaps.

A strictly fractional atom would require both endpoint sheets to vanish at the same direction. The event zero sets are disjoint, so no such atom occurs. Equality laws therefore use only the seven event rays. Seven-column independence from [OE, Proposition 7.1] makes the merged moment weights unique; they are the six positive old weights together with $p_4=0$. Thus the merged event law is unique.

For $\kappa_n<\kappa_e$ close to the event, the analytic six section, including its continuation below the event, has positive old weights and supplies a feasible six-atom comparator with $K=\kappa_n$ and value tending to $J_e$. Let $\mu_n$ be global maximizers. By Lemma 4.2, a subsequence converges to $\mu_*$. The dual upper bound tends to $J_e$, while the comparator gives the matching lower limit, so $\mu_*$ is an event equality law and hence equals the unique event law. Every maximizer sequence therefore localizes.

Choose six disjoint neighborhoods of the old rays, excluding contact $4$. Weak convergence gives positive mass in each neighborhood. At most six atoms then forces exactly one atom in each neighborhood and none elsewhere. In particular, a seventh small atom cannot appear and mass cannot move to contact $4$. $\square$

## 5. Strict complementarity and same-strength local uniqueness

**Definition 5.1 (inward coordinates and Lagrangian).** In the localized six-atom coordinates let $r_i=\xi_i$ when $\eta_i=0$ and $r_i=1-\xi_i$ when $\eta_i=1$. For the minimization of $F=-J$ use
$$
\mathscr L
=Y\cdot(\mathcal M-B)-J+\lambda(\kappa-K)-\nu\cdot r.
$$
At the event, write
$$
H_i^{\rm occ}=H_{\eta_i}(u_i,v_i),\qquad
H_i^{\rm opp}=H_{1-\eta_i}(u_i,v_i),\qquad
\epsilon_i=\operatorname{sgn}H_i^{\rm occ}.
$$
The occupied height is nonzero by [OE, Proposition 7.1]. Let
$$
R_i=Y_e\cdot\Gamma_{1-\eta_i}(u_i,v_i)
-|H_i^{\rm opp}|-\lambda_e|u_i|
$$
be the dual gap on the endpoint opposite to the occupied endpoint of ray $i$.

**Proposition 5.2 (strict complementarity, LICQ and tangent SOSC).** At the event,
$$
\nu_i=p_i\left(R_i+|H_i^{\rm opp}|-\epsilon_iH_i^{\rm opp}\right)
\ge p_iR_i>0\quad(i\in O),\qquad \lambda_e>0.
$$
The gradients of the eight moment equations, the active contrast equation and the six inward endpoint constraints have rank $15$. On the critical tangent, the Lagrangian Hessian is positive definite.

**Proof.** At fixed weight and direction, inward interpolation gives
$$
\Gamma_i(r_i)=(1-r_i)\Gamma_{\eta_i}+r_i\Gamma_{1-\eta_i},\qquad
H_i(r_i)=(1-r_i)H_i^{\rm occ}+r_iH_i^{\rm opp}.
$$
The nonzero occupied height fixes the sign of $H_i(r_i)$ near $r_i=0$, even when the opposite height has the other sign or is zero. Thus
$$
\left.\frac{d}{dr_i}|H_i(r_i)|\right|_{r_i=0^+}
=\epsilon_i(H_i^{\rm opp}-H_i^{\rm occ}).
$$
The contrast is independent of $r_i$. Using stationarity of $\mathscr L$ in $r_i$ and the occupied equality
$Y_e\cdot\Gamma_{\eta_i}=|H_i^{\rm occ}|+\lambda_e|u_i|$ yields
$$
\begin{aligned}
\nu_i
&=p_i\left(Y_e\cdot(\Gamma_{1-\eta_i}-\Gamma_{\eta_i})
-\epsilon_i(H_i^{\rm opp}-H_i^{\rm occ})\right)\\
&=p_i\left(R_i+|H_i^{\rm opp}|-\epsilon_iH_i^{\rm opp}\right).
\end{aligned}
$$
The added term is zero when $\epsilon_iH_i^{\rm opp}\ge0$, including $H_i^{\rm opp}=0$, and is $2|H_i^{\rm opp}|$ when the heights have opposite signs. The opposite endpoint of each old ray is not in the event zero set by [OE, Theorem 6.3 and Proposition 7.1], so the full-circle dual inequality gives $R_i>0$. All old weights are positive; hence $\nu_i\ge p_iR_i>0$ without a restriction on the opposite height. The multiplier $\lambda_e$ is positive by the event interval.

With $dr=0$, the first nine rows have rank nine: the moment rows have rank eight and $DK$ is nonzero on $\ker A$. The six $r$ rows are independent coordinate rows, so the complete active family has rank $15$. A critical tangent has $dr=0$, $A\,dz=0$ and $DK\,dz=0$. The last condition only restricts the tangent subspace of $\ker A$, on which $H$ is positive definite. This is the required tangent second-order condition; no non-tangent Hessian positivity is invoked. $\square$

**Theorem 5.3 (active-face identification).** There is $\varepsilon>0$ such that, for
$$
s_e-\varepsilon<s<s_e,
$$
every global maximizer in $\mathcal Q_6$ has all six old endpoint constraints active and has $K=\kappa$ active. It is the unique six-contact stationary law at that same strength.

**Proof.** By Theorem 4.3 all global maximizers lie in the localized coordinate neighborhood. LICQ persists there. At any such maximizer the KKT theorem applies to its active subset; extend omitted multipliers by zero in the full independent gradient family. The coefficients expressing the objective gradient in that family are unique and continuous, since a continuous left inverse exists for a full-rank matrix. At the event the six inward multipliers and the contrast multiplier are strictly positive. Hence, after shrinking the neighborhood, none can become zero: every endpoint constraint and the contrast constraint remains active.

On this active face, the bordered stationarity Jacobian is nonsingular. A homogeneous kernel vector would have a tangent $dz$ with $A\,dz=0$ and $DK\,dz=0$; its quadratic equation with $H$ forces $dz=0$, and row independence then forces the multiplier variation to vanish. The implicit-function theorem gives one stationary solution for each nearby $\kappa$. Since $dk_6/d\lambda>0$, the solution is precisely the analytic six section reparametrized by its same strength. The localization theorem makes this local solution global within $\mathcal Q_6$. $\square$

## 6. Original-class transfer and the seven-total sandwich

**Theorem 6.1 (same-strength optimum with six supported low labels).** Under Assumption 1.2, for some $\varepsilon>0$ and every $s_e-\varepsilon<s<s_e$, the original maximum among instruments with at most six supported nonzero low actual labels equals the positive extended six branch at that same strength:
$$
\mathcal T_A^{(\le6\ {\rm supported\ low})}(s)=V_6(s).
$$
The contrast constraint is active.

**Proof.** Every original competitor in this class has the same-law representation of [OE, Proposition 3.2]. Its eight moments, capacity-attached failure effect, complex coherences, arbitrary admissible time law and actual-label height are represented by a law in $\mathcal Q_6$; the endpoint convexity inequality used in Theorem 4.3 is valid for each existing fractional actual label. Hence Theorem 5.3 is an upper bound for the entire original class.

Conversely, the continued six law has nonnegative old weights, exactly the eight moments, active contrast and capacities $b_{\rm label}=0$ or $1000c_h$. The common constructor of [OE, Theorem 9.2] realizes it as one original complex CP/TP chronological instrument. It uses six low qubit fibres and one compulsory high fibre, the same source minimax error $E_*$, sharp JOINT cost $\mathsf C(s)$, deterministic reports, all five Borel/passive-reference maps, whole-fibre activity at most $\log1001$, and the absolute FIRST clock $6+a$. Thus the compact upper bound is attained at the same strength. $\square$

**Theorem 6.2 (at most seven total labels).** Under the same hypotheses and strength interval,
$$
\mathcal T_A^{(\le7\ {\rm total})}(s)=V_6(s).
$$

**Proof.** A positive high acquisition is compulsory under Assumption 1.2, and a generated label cannot simultaneously be a low fibre of dimension at most two and the required high fibre. An instrument with at most seven total generated actual labels therefore has at most six supported nonzero low labels; supported-zero labels consume the count and contribute no supported moment, contrast or height. The same-law reduction and Theorem 5.3 give the upper bound $V_6(s)$. The constructor in Theorem 6.1 has six low labels and one high label. Its supported-zero complement is included in that one high acquired label, so it supplies the reverse inequality. This is a sandwich for the two optima; it does not assert equality of their full feasible classes. Hidden Kraus multiplicity, failure-label count, quantum fibre dimension and actual acquisition alphabet remain distinct. $\square$

## 7. Positive quadratic loss of the shorter alphabet

**Theorem 7.1 (quadratic deficit at the output-extinction event).** Let $\mathcal T_A^{\rm full}$ be the original unconstrained optimum. For the interval in Theorems 6.1–6.2,
$$
\mathcal T_A^{\rm full}(s)=V_7(s),\qquad
\mathcal T_A^{(\le7\ {\rm total})}(s)=V_6(s),
$$
and
$$
\mathcal T_A^{\rm full}(s)
-\mathcal T_A^{(\le7\ {\rm total})}(s)
=
\frac{\alpha}{4s_0^2}
\left(\frac1{k_6'}-\frac1{k_7'}\right)
(s-s_e)^2+o\!\left((s-s_e)^2\right).
$$
The coefficient is strictly positive.

**Proof.** The first equality is the inherited full original optimum on the seven physical side of [OE, Theorem 1.4]. The second is Theorem 6.2. Both branches have the same event value and first strength derivative by Proposition 3.1. Their second derivative difference is the positive quantity in Theorem 3.2. Taylor expansion of the two analytic extensions gives half that second-derivative difference as the quadratic coefficient, yielding the formula. The neighborhood is existential; no explicit interval length or certified midpoint enclosure is asserted here. $\square$

## 8. Boundaries and source attribution

**Definition 8.1 (what remains conditional).** The results above concern only the selected event at $t=1000$, $A=\log1001$, and strengths immediately below $s_e$. They do not establish a complete $(s,A)$ frontier, any all-budget or all-contrast count law, a strong-budget branch, a next event, a connection across the gaps between previously selected multiplier ranges, universal affine absence, a maximal continuation interval, or exact global counts away from this neighborhood. They do not add source isolation, TP, minimax, sharp JOINT, unaveraged equality-face, full-complex rigidity, native permission, physical access, calibration or empirical claims. The original twelve histories, five Borel/passive-reference components, full-complex/multi-Kraus class, whole-fibre activity, FIRST clock, common constructor and compulsory high label remain exactly those inherited interfaces.

**Definition 8.2 (literature and mathematical suppliers).** The local response, compactness, strict-complementarity and quadratic-transfer deductions are \`repo-derived\` from the displayed hypotheses. The following primary sources are cited only for the standard tools they supply.

| Source | Precise use and excluded transfer |
| --- | --- |
| S. Banach, “Sur les opérations dans les ensembles abstraits et leur application aux équations intégrales”, *Fundamenta Mathematicae* 3 (1922), 133–181 | Contraction mapping in the inherited box argument; it supplies no source-root or physical-optimum claim. |
| S. Bernstein, “Démonstration du théorème de Weierstrass fondée sur le calcul des probabilités”, *Communications de la Société Mathématique de Kharkov* 13 (1912), 1–2 | Positivity of the Bernstein basis used by [OE, Proposition 6.2]; it supplies no new positivity certificate here. |
| H. W. Kuhn and A. W. Tucker, “Nonlinear programming”, *Proceedings of the Second Berkeley Symposium on Mathematical Statistics and Probability* (1951), 481–492 | KKT multiplier and second-order reasoning in §5; the constraint qualification and signs are checked from the inherited event geometry. |
| W. F. Stinespring, “Positive functions on $C^*$-algebras”, *Proceedings of the American Mathematical Society* 6 (1955), 211–216, DOI:10.1090/S0002-9939-1955-0069403-4 | Finite-dimensional CP/TP completion language used by [OE, §9]; no physical/native realization is inferred. |
| K. Kraus, “General state changes in quantum theory”, *Annals of Physics* 64 (1971), 311–335, DOI:10.1016/0003-4916(71)90108-4 | Kraus-index and effect bookkeeping in the common constructor; hidden Kraus indices are explicitly excluded from actual-label counting. |
| [CG], [JR], [FA], [RC], and [OE] | \`repo-derived\` supplier documents for the original source interfaces, event certificate, same-law reduction, capacity, response geometry and common constructor. Their exact scopes are those cited in Assumption 1.2. |

The standard references do not certify the numerical event or any original-AURIC bridge. No worldwide priority or novelty claim is made.

**Open question 8.3 (outside this source).** Extending the positive quadratic loss to every weak feasible strength, proving any universal minimum total alphabet, or closing the unchanged all-budget/all-contrast programme requires new source certificates and new global comparisons. These are not consequences of the local event argument.

[OE]: FIB_NATIVE_COMPLETE_CONTINUATION_LOCAL_OUTPUT_EXTINCTION.md
[CG]: FIB_NATIVE_COMPLETE_CONTINUATION_DISTINGUISHABILITY_GAP.md
[JR]: FIB_NATIVE_COMPLETE_CONTINUATION_JOINT_RECORD_PAYLOAD.md
[FA]: FIB_NATIVE_COMPLETE_CONTINUATION_FINITE_ACTIVITY_FRONTIER.md
[RC]: FIB_NATIVE_COMPLETE_CONTINUATION_RESIDUAL_CONTACT_CURVE.md

## 追加锚（本行以下为增补区）

## 9. Quantitative appendix: fixed original law and finite inputs

**Definition 9.1 (scope and fixed suppliers).** Retain Assumption 1.2, the selected $t=1000$ event, the original comparison class and every boundary in §8. In this appendix OE means [the fixed OE source][OEpin] at revision `321589a8be98de4fe179f99f6e593d8784952db1`; QS means [the fixed quantitative-stability source][QSpin] at revision `4751be04555dc6a71e83e0c8f5dcdc5e26d104de`. The CG, JR, FA and RC interfaces mean their respective files at the same fixed revision as OE. These source identities fix mathematical inputs, not an independently established source root or an evaluated numerical window. The qualitative event localization, strict complementarity and quadratic loss of §§4–7 are reused; the additional result is the finite quantitative recipe and its estimates below.

All conclusions are ordinary conditional mathematics. The source/root, ranks and root TP, full stopped-cq minimax, sharp worst-history JOINT cost, unaveraged equality face before height optimization, full-complex multi-Kraus rigidity, same-law reduction, physical capacity and common constructor remain separate antecedents. Comparison expressions on a rectangular source box are not asserted to be TP away from the exact root. No kernel, native, empirical, source-final or programme-completion conclusion is attached to this appendix.

**Definition 9.2 (the complete common-law dictionary).** Use OE Definitions 2.1–3.1 at that same original source. To distinguish source amplitudes from response derivatives, write $a_{\rm src},b_{\rm src},c_{\rm src},d_{\rm src}$ for OE's $a,b,c,d$, and write $\Delta_\rho=\rho_{27}-\rho_5$. With $D,T,S,M$ unchanged, put
$$
\begin{gathered}
\theta=\frac{a_{\rm src}b_{\rm src}}{h_0h_1},\quad
\omega=\frac{c_{\rm src}d_{\rm src}}{h_0h_2},\quad
\delta=\theta+\omega,\quad s_0=\sqrt\delta,\quad
\alpha=\theta/\delta,\quad\beta=\omega/\delta,\quad
a_s=\sqrt\alpha/s_0>0,\quad \kappa=a_s s,\quad s_e=k_e/a_s,\\
u=\cos\phi,\quad v=\sin\phi,\quad
z=u/\sqrt\alpha,\quad w=v/\sqrt\beta,\quad h=(1,z,w)^T,\quad
L_h=s_0D+zT+wS,\quad
n_h=(0,d_{\rm src}w/h_2,-b_{\rm src}z/h_1)^T,\\
N_{ij}=\operatorname{tr}(K_i\Delta_\rho K_j^T),\quad
(K_0,K_1,K_2)=(D,T,S),\quad
G=\operatorname{diag}(s_0,1,1)N\operatorname{diag}(s_0,1,1),\\
\ell_h=h^TGh,\quad f_h=n_h^T\Delta_\rho n_h,\quad
c_h=\frac{h_1^2h_2^2\delta+a_{\rm src}^2h_2^2z^2+c_{\rm src}^2h_1^2w^2}
{h_0^2\delta+b_{\rm src}^2z^2+d_{\rm src}^2w^2}>0,\\
H_\xi=\ell_h+1000c_h\xi f_h,\quad b_{\rm label}=1000c_h\xi,\quad
\Gamma_\xi=(1,u,v,u^2,uv,\xi c_h,\xi c_hu^2,\xi c_huv),\\
V_f=m_2h_1^2/b_{\rm src}^2,\quad W_f=m_1h_2^2/d_{\rm src}^2,\quad
\mu=\alpha V_f+\beta W_f,\quad
B=(1,0,0,\alpha,0,\mu/1000,\alpha V_f/1000,0),\\
H_{\rm high}=(1-\delta)N_{00}>0.
\end{gathered}
$$
The coefficient law $\pi$ on $X=\mathbb T\times[0,1]$ obeys
$$
\int\Gamma_\xi\,d\pi=B,\qquad
K(\pi)=\int|\cos\phi|\,d\pi\ge\kappa,\qquad
J(\pi)=\int|H_\xi|\,d\pi,\qquad
T_{\rm actual}=(H_{\rm high}+J)/2.
$$
These eight moments are the complete joint live and attached-failure covariances
$\int hh^T\,d\pi=I_3$ and $\int b_{\rm label}n_hn_h^T\,d\pi=M$, including both cross-covariances, by OE Proposition 3.2 and QS Proposition 2.3. No marginal, even-moment or feasibility-only symmetrization is substituted. In a finite law the $p_j$ are coefficient weights. The actual acquisition probability on input $\rho$ is
$\operatorname{tr}(E[p_jL_{h_j}^*L_{h_j}+p_jb_{{\rm label},j}n_{h_j}n_{h_j}^T]E^*\rho)$.
The source amplitudes, coefficient weights, physical probabilities, response derivatives and clock are distinct.

**Definition 9.3 (event geometry and norms).** Let $z_i^e=(\phi_i^e,\eta_i)$, $i=0,\ldots,6$, be OE's exact event contacts; $O=(0,1,2,3,5,6)$. Their endpoint, occupied-height and report signs, and their local half-angle bases, are

| $i$ | $\eta_i$ | $\epsilon_i$ | $\sigma_i$ | local base |
| --- | --- | --- | --- | --- |
| $0$ | $0$ | $+1$ | $+1$ | $0$ |
| $1$ | $0$ | $+1$ | $-1$ | $\pi$ |
| $2$ | $0$ | $-1$ | $-1$ | $\pi$ |
| $3$ | $0$ | $+1$ | $+1$ | $0$ |
| $4$ | $1$ | $+1$ | $+1$ | $0$ |
| $5$ | $1$ | $-1$ | $-1$ | $\pi$ |
| $6$ | $1$ | $-1$ | $+1$ | $3\pi/2$ |

At the event $p_i^e>0$ for $i\in O$, $p_4^e=0$, and
$\pi_e=\sum_{i=0}^6p_i^e\delta_{z_i^e}$.
The exact moments are $A_7p^e=B$ for
$A_7=[\Gamma(z_0^e)\ \cdots\ \Gamma(z_6^e)]$, and
$k_e=K(\pi_e)$, $J_e=J(\pi_e)$. The selected multiplier is $\lambda_e$.
Use the exact weaker margins
$$
p_*=11/250,\qquad h_*=3/1000,\qquad
u_*=79/100,\qquad \Delta=29/100,\qquad q_B=1/8000.
$$
The retained supplier inequalities give $p_i^e>p_*$ on $O$,
$\epsilon_iH_{\eta_i}(\phi_i^e)>h_*$ and
$\sigma_i\cos\phi_i^e>u_*$ at all seven contacts, and every pairwise chord distance is greater than $\Delta$, since $\Delta^2<0.08907$. Here $\Delta$ is a separation bound, not the density difference $\Delta_\rho$.

All unspecified vector norms are Euclidean; matrix norms are the induced $2\to2$ norm. A multilinear derivative norm is its supremum on tuples of Euclidean unit vectors. A Lipschitz bound for a matrix-valued function uses this matrix norm. $d_{\mathbb T}$ is shortest angular distance in radians. Local angular coordinates are the lifts about the displayed $\phi_i^e$. The only scaled norm below is expressly denoted $\|\cdot\|_{r_b}$. Every finite bound chosen below may be enlarged to a rational bound at least one, except a positive lower singular-value bound. A lower singular-value bound means the smallest singular value on the column domain.

## 10. Recipe I: explicit event coercivity on the full cylinder

**Definition 10.1 (signed endpoint charts and finite derivative inputs).** In a report chart let $r_c=1+x^2$, $(u,v)=(U/r_c,V/r_c)$, $x\in[-1,1]$. For report sign $+$ use $(U,V)=(1-x^2,2x)$; for sign $-$ use $(U,V)=(-1+x^2,-2x)$. These closed half-circles cover the circle, including their report axes. The local base-$3\pi/2$ chart for contact $6$ uses $(U,V)=(2x,-1+x^2)$. Put $Z=U/\sqrt\alpha$, $W=V/\sqrt\beta$ and
$$
\begin{aligned}
D_c&=h_0^2\delta r_c^2+b_{\rm src}^2Z^2+d_{\rm src}^2W^2,\\
N_c&=h_1^2h_2^2\delta r_c^2+a_{\rm src}^2h_2^2Z^2+c_{\rm src}^2h_1^2W^2,\\
L_c&=G_{00}r_c^2+G_{11}Z^2+G_{22}W^2
       +2G_{01}r_cZ+2G_{02}r_cW+2G_{12}ZW,\\
F_c&=-\frac{11}{64}(d_{\rm src}/h_2)^2W^2
       -\frac{2(\Delta_\rho)_{12}d_{\rm src}b_{\rm src}}{h_1h_2}ZW .
\end{aligned}
$$
Here $(\Delta_\rho)_{11}=-11/64$ and
$(\Delta_\rho)_{12}=(\sqrt{37}-\sqrt{59})/16<0$. OE's clearing dictionary is
$$
\begin{array}{c|c|c|c|c}
\eta&\Gamma_{\rm num}&d_\eta&H_{\rm num}&W_{\rm num}\\\hline
0&(r_c^2,r_cU,r_cV,U^2,UV,0,0,0)&r_c^2&L_c&r_cU\\
1&(D_cr_c^2,D_cr_cU,D_cr_cV,D_cU^2,D_cUV,N_cr_c^2,N_cU^2,N_cUV)
&D_cr_c^2&D_cL_c+1000N_cF_c&D_cr_cU
\end{array}
$$
Thus $\Gamma_\eta=\Gamma_{\rm num}/d_\eta$,
$H_\eta=H_{\rm num}/d_\eta$, and $W_{\rm num}/d_\eta=u$.
Every denominator is positive on every chart. At the event set
$$
P_{\eta,\epsilon,\sigma}
 =Y_e\cdot\Gamma_{\rm num}-\epsilon H_{\rm num}
                          -\lambda_e\sigma W_{\rm num},\qquad
D_\eta^e=Y_e\cdot\Gamma_\eta-|H_\eta|-\lambda_e|u|.
$$
The eight event signed cases and their exact removed double factors are

| $(\eta,\epsilon,\sigma)$ | contact indices removed | quotient degree |
| --- | --- | --- |
| $(0,+,+)$ | $0,3$ | $0$ |
| $(0,+,-)$ | $1$ | $2$ |
| $(0,-,+)$ | none | $4$ |
| $(0,-,-)$ | $2$ | $2$ |
| $(1,+,+)$ | $4$ | $6$ |
| $(1,+,-)$ | none | $8$ |
| $(1,-,+)$ | $6$ | $6$ |
| $(1,-,-)$ | $5$ | $6$ |

Contact $6$ in the base-zero report chart has root
$\widehat x_6=(x_6-1)/(x_6+1)$, with positive denominator. OE §§6 and 16 give positive quotients $Q_{\eta,\epsilon,\sigma}>q_B$ on all their closed leaves. The polynomial identity at the event is exactly
$P=Q\prod_{j\in S}(x-c_j)^2$ with $|S|\le2$.
No unused constant has been dropped: it is zero at the event; off the event the six-system unused value is retained as in OE Definition 6.1.

Choose finite rational $d_{\max},M_H,M_3\ge1$ with
$$
\begin{gathered}
0<d_\eta(x)\le d_{\max}
\quad\hbox{on all eight closed report charts},\\
|\partial_\phi H_\eta|\le M_H,\qquad
\left|\partial_\phi^3
 (Y_e\cdot\Gamma_\eta-\epsilon H_\eta-\lambda_e\sigma\cos\phi)\right|\le M_3
\quad\hbox{on }\mathbb T
\quad(\eta=0,1,\ \epsilon,\sigma=\pm1).
\end{gathered}
$$
The bounds refer to normalized functions; derivatives of cleared polynomials alone are not substitutes for them. Set
$$
\begin{gathered}
\gamma_*=\frac{q_B\Delta^2}{8d_{\max}},\qquad
\rho=\min\left\{\frac12,\frac\Delta4,\frac{u_*}2,
                     \frac{h_*}{2M_H},\frac{\gamma_*}{2M_3}\right\},\\
d_{\rm off}=\frac{q_B(\rho/2)^4}{d_{\max}},\qquad
c_{\rm sh}=\min\{\gamma_*/4,d_{\rm off}/10\},\qquad
c_e=\frac{c_{\rm sh}\Delta^2}{88}.
\end{gathered}
$$
All are strictly positive. They contain no unspecified off-support minimum.

**Theorem 10.2 (quantitative event gap, including both axes).** Define
$$
\mathfrak d(\phi,\xi)^2
 =\min_{0\le i\le6}
       \{d_{\mathbb T}(\phi,\phi_i^e)^2+|\xi-\eta_i|\},\qquad
D_e(\phi,\xi)
 =Y_e\cdot\Gamma_\xi-|H_\xi|-\lambda_e|\cos\phi|.
$$
Under the retained event factors and the finite bounds in Definition 10.1,
$$
D_e(\phi,\xi)\ge c_e\mathfrak d(\phi,\xi)^2
                       \qquad((\phi,\xi)\in X).
$$

Proof. At a contact in its report chart, differentiate $P/d_\eta$ twice in angle. Since $P=P_x=0$, its normalized angular curvature is
$$
\frac{2Q(c_i)\prod_{j\ne i}(c_i-c_j)^2}{d_\eta(c_i)}
                    \left(\frac{dx}{d\phi}\right)^2.
$$
Within a report half-circle $d\phi/dx=2/(1+x^2)\le2$, so
$|dx/d\phi|\ge1/2$. Chord separation gives
$|c_i-c_j|\ge\Delta/2$, because the chord distance in a common chart is at most $2|c_i-c_j|$. There is at most one other factor. With no other factor the empty product is one and also exceeds $\Delta^2/4$. Thus the curvature is at least $\gamma_*$. The $\rho$ gates keep report and occupied-height signs fixed along the entire angular $\rho$-arc: $|u-u_i|\le\rho$ and $|H_\eta-H_\eta(\phi_i^e)|\le M_H\rho$. The third-derivative gate then gives $D_\eta^{e\prime\prime}\ge\gamma_*/2$ there, and Taylor's integral formula gives
$D_\eta^e\ge(\gamma_*/4)d_{\mathbb T}(\phi,\phi_i^e)^2$.

Outside all same-sheet $\rho$-arcs every removed factor obeys
$|x-c_j|\ge\rho/2$ in its report chart, since shortest angular distance is at most $2|x-c_j|$. The product of at most two squared factors is at least $(\rho/2)^4$; this also holds for the rootless cases because $\rho/2\le1$. Each signed normalized polynomial is therefore at least $d_{\rm off}$ there. For the actual report sign,
$D_\eta^e=\min_{\epsilon=\pm1}P_{\eta,\epsilon,\sigma}/d_\eta$.
This remains true at a height zero, and the two report charts agree at a report axis. Hence the off-arc estimate covers these points as well. If
$d_\eta(\phi)=\min_{i:\eta_i=\eta}d_{\mathbb T}(\phi,\phi_i^e)$, the local and off-arc estimates, with $d_\eta^2\le\pi^2<10$, give
$$
D_\eta^e(\phi)\ge c_{\rm sh}d_\eta(\phi)^2
                                    \quad(\eta=0,1).
$$

The disjoint sheet inventories and angular/chord separation imply
$d_0+d_1\ge\Delta$. Put $S=(1-\xi)d_0^2+\xi d_1^2$.
For $\xi\le1/2$ and $d_0\le\Delta/2$,
$S\ge d_0^2/2+\xi\Delta^2/4$.
For $\xi\le1/2$ and $d_0>\Delta/2$, $S\ge\Delta^2/8$.
Since
$\mathfrak d^2=\min(d_0^2+\xi,d_1^2+1-\xi)\le\pi^2+1<11$
and $0<\Delta<1$, both cases yield
$S\ge\Delta^2\mathfrak d^2/88$. Exchange sheets for $\xi\ge1/2$.
Finally the exact affine/chord identity of QS Theorem 5.2 is
$$
D_e=(1-\xi)D_0^e+\xi D_1^e+
 (1-\xi)|H_0|+\xi|H_1|-|(1-\xi)H_0+\xi H_1|.
$$
Its last three terms are nonnegative everywhere, including all height zeros. Combining the inequalities proves the claim on the entire cylinder. No sign is imposed on the opposite endpoint height. $\square$

**Definition 10.3 (global rounding inputs).** Choose $M_\phi,M_\xi\ge1$
bounding $\|\partial_\phi\Gamma_\xi\|_2$ and
$\|\partial_\xi\Gamma_\xi\|_2$ on all $X$, and choose rational
$L\ge\max(1,\sqrt{M_\phi^2+M_\xi^2})$. Then
$\|\Gamma(x)-\Gamma(z_i^e)\|_2\le L\mathfrak d(x)$ when $i$ is a nearest contact; this is the derivative bound used in QS Theorem 7.1. Use the row-selector $S_7$ for moment rows $(0,1,2,3,4,5,7)$ and define the exact left inverse
$$
J_{\rm left}=(S_7A_7)^{-1}S_7,\qquad J_{\rm left}A_7=I_7.
$$
The inverse exists by OE Proposition 7.1. Choose rational
$K_G\ge\max(1,\max_i\|\operatorname{row}_iJ_{\rm left}\|_2)$.
Bounds for these derivatives and this left inverse are finite original-source inputs, not numerical values supplied here.

## 11. Recipe II: inverse branches and a comparator at the same contrast

**Definition 11.1 (original branch boxes and derivative norms).** Let
$F_b(X,\lambda)=0$, $b=6,7$, be exactly OE Definition 4.2 in its stated variable and equation order. $F_7$ has dimension $n_7=22$ and signed $p_4$. $F_6$ has dimension $n_6=21$, omits $p_4$ before any inverse, and retains $P_4'(x_4)=0$ but does not impose $P_4(x_4)=0$. Its last coordinate is the unused $x_4$. Both have all value rows before all derivative rows. The branch centers are the exact event-center embeddings of OE Definition 13.1, with radii $10^{-8}$ on every half-angle coordinate and weight and $10^{-4}$ on $Y$. The fixed multiplier interval is
$$
I=[190.449003333,190.449005333].
$$
Denote these full rectangular branch boxes by $\mathcal B_b$. The event root is the common exact embedding supplied by OE §§4–5; these boxes and $I$ are not adjustable localization neighborhoods.

Let $r_b$ be the corresponding radius vector, $D_{r_b}=\operatorname{diag}(r_b)$ and
$\|v\|_{r_b}=\|D_{r_b}^{-1}v\|_\infty$. Let $R_{{\rm pre},b}$ be the exact rational OE Appendix 14 preconditioner and choose its supplied uniform defect bound
$$
q_b\ge\sup_{\mathcal B_b\times I}
\|D_{r_b}^{-1}(I-R_{{\rm pre},b}F_{b,X})D_{r_b}\|_\infty,
\qquad q_b<1.
$$
The supplier bounds $q_6<0.000172$ and $q_7<0.010$ permit rational such choices below one. Choose finite rational bounds on these full boxes:
$$
\begin{gathered}
N_b\ge\|F_{b,X}^{-1}\|_2,\quad P_b\ge\|F_{b,\lambda}\|_2,\quad
Q_b\ge\|F_{b,XX}\|,\quad R_b\ge\|F_{b,X\lambda}\|,\\
K_{1b}\ge\|D_Xk_b\|_2,\qquad K_{2b}\ge\|D_X^2k_b\|.
\end{gathered}
$$
Here the index sets are $I_6=O$ and $I_7=\{0,\ldots,6\}$, and
$k_b(X)=\sum_{i\in I_b}p_i\sigma_i u_i$ uses the fixed report signs on the supplied contact boxes, and the derivatives include every variable dependence of the cleared systems. A sufficient Euclidean inverse bound is
$$
N_b\ge
\sqrt{n_b}\frac{\max_jr_{b,j}}{\min_jr_{b,j}}
       \frac{\|R_{{\rm pre},b}\|_2}{1-q_b}.
$$
Indeed $F_X^{-1}=(R_{\rm pre}F_X)^{-1}R_{\rm pre}$, the geometric-series inverse has scaled infinity norm at most $(1-q_b)^{-1}$, and conversion to Euclidean norm costs at most
$\sqrt{n_b}\max r_b/\min r_b$. A scaled defect bound by itself is not an unscaled contraction bound.

At the event let $v_b$ be the exact solution of
$F_{b,X}v_b=-F_{b,\lambda}$ in its original coordinates, and set
$$
a=D_Xk_6\,v_6=k_{6,\lambda}(\lambda_e)>0,\qquad
b=D_Xk_7\,v_7=k_{7,\lambda}(\lambda_e)>a .
$$
These are response derivatives, not $a_{\rm src},b_{\rm src}$. Their strict order is reused from Theorem 2.3:
$b-a=-p_4'd_6'$, with the normalized unused-gap derivative
$d_6'=\dot P_4/d_4$ at the event, where
$$
\dot P_4=\left.\frac d{d\lambda}
 P_4(x_4^{(6)}(\lambda);Y_6(\lambda),\lambda)\right|_{\lambda_e}
 =\Gamma_{{\rm num},4}\cdot Y_6'-W_{{\rm num},4}.
$$
The last equality uses the unused stationarity equation; $\dot P_4$ is a total multiplier derivative, whereas $P_4'(x_4)=0$ in the six system is an $x$ derivative. The supplier's cleared derivative is not substituted for $d_6'$ without its denominator. Enclosing these exact event linear solves, especially the small positive $a$, is a separate finite evaluation obligation.

**Definition 11.2 (explicit inverse intervals).** Put
$$
\begin{gathered}
\tau=\min\{a/4,(b-a)/4\},\quad
l_6=a-\tau,\quad u_6=a+\tau,\quad
l_7=b-\tau,\quad u_7=b+\tau,\\
U_b=N_bP_b,\qquad
W_b=N_b(Q_bU_b^2+2R_bU_b),\qquad
T_b=\max\{1,K_{2b}U_b^2+K_{1b}W_b\},\\
h_{\lambda,0}=9/10^7,\quad h_b=\min\{h_{\lambda,0},\tau/T_b\},\quad
d_{\rm branch}=\min\{l_6h_6,l_7h_7\},\quad C=1/(2l_6),\\
A_w=K_GL\sqrt{C/c_e},\quad
A_q=\sqrt{2C/(c_ep_*)},\quad
D_{\rm loc}=\sqrt{6(A_w^2+A_q^2+A_q^4)},\quad
C_{\rm br}=(2U_6+1)/l_6 .
\end{gathered}
$$
All denominators are positive; in particular
$0<l_6\le u_6<l_7\le u_7$.
OE's exact event-multiplier margin is greater than $9.999\cdot10^{-7}$, so $[\lambda_e-h_{\lambda,0},\lambda_e]\subset I$.

**Theorem 11.3 (controlled inversion and quadratic comparator slack).** On
$[\lambda_e-h_b,\lambda_e]$,
$$
l_b\le k_{b,\lambda}\le u_b .
$$
Both inverse multipliers $\lambda_b(\kappa)$ exist whenever
$k_e-d_{\rm branch}<\kappa\le k_e$. The extended six law there has its six positive old weights and is feasible for all eight moments and $K=\kappa$, even though its unused dual gap is negative on the left. In the notation $J_b(\kappa)=J_b(\lambda_b(\kappa))$,
$$
E_6(\kappa):=J_e-\lambda_e(\kappa-k_e)-J_6(\kappa)
\quad\hbox{satisfies}\quad
0\le E_6(\kappa)\le C(\kappa-k_e)^2.
$$
For $w_6=(p,\phi,Y,\lambda_6)$ in the twelve occupied endpoint variables and nine multipliers,
$$
\|w_6(\kappa)-w_e\|_2\le C_{\rm br}|\kappa-k_e|.
$$

Proof. The stated cleared systems are affine in $\lambda$, hence
$F_{b,\lambda\lambda}=0$. Implicit differentiation gives
$$
X_b'=-F_{b,X}^{-1}F_{b,\lambda},\qquad
X_b''=-F_{b,X}^{-1}
       (F_{b,XX}[X_b',X_b']+2F_{b,X\lambda}X_b').
$$
The box bounds give $\|X_b'\|\le U_b$, $\|X_b''\|\le W_b$ and
$|k_b''|\le T_b$. Integration from the exact event then proves the derivative windows. Each increasing branch image contains
$[k_e-l_bh_b,k_e]$, so both inverse sections exist on the displayed common interval. Their inverse multipliers are evaluated separately at the same $\kappa$; they are not equated. The six old-weight margins hold on its full supplied box, so this continued six law is a feasible primal comparator.

Proposition 3.1 gives $J_{b,\kappa}=-\lambda_b$ and
$J_{b,\kappa\kappa}=-1/k_{b,\lambda}$. Thus
$E_6(k_e)=E_6'(k_e)=0$ and $0<E_6''\le1/l_6$. Twice integration yields the asserted $C=1/(2l_6)$ bound. Matching the target contrast is essential to the first-order cancellation.

Finally every local half-angle chart obeys $|d\phi/dx|\le2$.
The endpoint weights, angles and $Y$ therefore have $\lambda$-derivative norm at most $2U_6$ after dropping unused $x_4$. The multiplier coordinate adds at most one to the norm bound. Since $d\lambda_6/d\kappa\le1/l_6$, integration gives $C_{\rm br}$. This is the Euclidean conversion, separate from the scaled inverse bound above. $\square$

## 12. Recipe III: global no-split localization and positive active multipliers

**Definition 12.1 (a prescribed smooth coordinate box).** Use block coordinates
$x=(p,\phi,r)\in\mathbb R^{18}$ indexed by $O$, with
$x_e=(p^e,\phi^e,0)$ and $\xi_i=\eta_i+(1-2\eta_i)r_i$. On the full closed box
$$
\mathcal X=\{\|p-p^e\|_\infty\le1,              \|\phi-\phi^e\|_\infty\le1,              \|r\|_\infty\le1\}
$$
define the signed smooth extensions
$$
\begin{aligned}
\mathcal M(x)&=\sum_{i\in O}p_i\Gamma_{\eta_i+(1-2\eta_i)r_i}(\phi_i),\\
\mathcal J(x)&=\sum_{i\in O}p_i\epsilon_i
                   H_{\eta_i+(1-2\eta_i)r_i}(\phi_i),\\
\mathcal K(x)&=\sum_{i\in O}p_i\sigma_i\cos\phi_i,\qquad
E_rx=r,\\
Q(x)&=[D\mathcal M(x)^T,                      -\nabla\mathcal K(x),                      -E_r^T]\in\mathbb R^{18\times15}.
\end{aligned}
$$
The affine fractional extensions for $r\in[-1,1]$ may leave the physical interval; they remain smooth because the capacity denominator depends only on $\phi$. The fixed signs in $\mathcal J,\mathcal K$ define smooth functions throughout this bounding box. Their equality to the actual absolute-value functions is used only in the smaller ball specified below.

Choose rational $M_{Hx},L_Q,L_J\ge1$ such that on $\mathcal X$ each individual
$H_{\eta_i+(1-2\eta_i)r_i}(\phi_i)$ has gradient norm at most $M_{Hx}$,
$Q$ has Lipschitz constant at most $L_Q$, and $\nabla\mathcal J$ has Lipschitz constant at most $L_J$. Put
$$
R_{\rm chart}=\min\{1/2,p_*/4,\Delta/4,u_*/2,h_*/(2M_{Hx})\}.
$$
On $\|x-x_e\|_2<R_{\rm chart}$ with physical $r\ge0$, all weights are positive, $r_i<1/2$, and the report and occupied fractional-height signs remain the stated ones. Thus $\mathcal J=J$ and $\mathcal K=K$ there, with the unique local angular lifts. There is no absolute-value differentiability assumption at other cylinder points.

At the event set
$$
\begin{gathered}
H_i^{\rm opp}=H_{1-\eta_i}(\phi_i^e),\qquad
R_i=D_{1-\eta_i}^e(\phi_i^e),\qquad
\chi_i=R_i+|H_i^{\rm opp}|-\epsilon_iH_i^{\rm opp},\\
\nu_i^e=p_i^e\chi_i,\qquad
y_e=(Y_e,\lambda_e,\nu^e),\qquad Q_e=Q(x_e).
\end{gathered}
$$
Choose a certified lower bound $\sigma>0$ with
$\sigma_{\min}(Q_e)\ge\sigma$; the exact rank argument below establishes that such a bound exists, but gives no decimal value. Define
$$
\begin{gathered}
m_\mu=\min\{190,p_*c_{\rm sh}\Delta^2\}>0,\qquad
C_\mu=\frac{2(L_J+L_Q\|y_e\|_2)}{\sigma}>0,\\
R_x=\min\left\{R_{\rm chart},\frac{\sigma}{2L_Q},
                                   \frac{m_\mu}{2C_\mu}\right\}.
\end{gathered}
$$

**Theorem 12.2 (every six-atom maximizer localizes quantitatively, with overshoot).** Let
$d=k_e-\kappa$ with
$$
0<d<\min\{1,d_{\rm branch},p_*/(2A_w)\}.
$$
Every global maximizer of $J$ in the complete fractional class $\mathcal Q_6$ at target $\kappa$ has precisely one positive atom in each old rounding cell and no atom in the seventh cell. After matching to those cells it satisfies
$$
\begin{gathered}
|p_i-p_i^e|\le A_wd,\quad p_i\ge p_*/2,\quad
d_{\mathbb T}(\phi_i,\phi_i^e)\le A_qd,\quad
0\le r_i\le A_q^2d^2,\\
0\le K-\kappa\le Cd^2/\lambda_e .
\end{gathered}
$$
If additionally $d<R_x/D_{\rm loc}$, the shortest angular lifts are unique and
$\|x-x_e\|_2\le D_{\rm loc}d<R_x$.

Proof. Compactness is Lemma 4.2, and Theorem 11.3 supplies a feasible six-atom comparator at this same target. For any law with the original eight moments the exact event identity is
$$
\begin{aligned}
\mathcal E_e(\pi;\kappa)
&:=J_e-\lambda_e(\kappa-k_e)-J(\pi)\\
&=\lambda_e(K(\pi)-\kappa)+\int_XD_e\,d\pi .
\end{aligned}
$$
For a feasible law both terms on the right are nonnegative, even though $\kappa<k_e$. Every maximizing six-law beats the comparator, so Theorems 10.2 and 11.3 give
$$
0\le\mathcal E_e\le Cd^2,\qquad
\int\mathfrak d^2\,d\pi\le Cd^2/c_e,\qquad
0\le K-\kappa\le Cd^2/\lambda_e .
$$
In particular overshoot has not been assumed absent.

Assign every original fractional atom to a single nearest event pair for $\mathfrak d$, resolving ties by the lowest index. This is the Borel no-split assignment of QS Theorem 7.1. Let $q_i$ be its seven cell masses. The proof uses only the complete contact set and the gap/derivative inequalities, not a positive mass at every zero. Its moment estimate and the exact left inverse give
$$
\left\|\sum_{i=0}^6q_i\Gamma(z_i^e)-B\right\|_2
 \le L\sqrt{C/c_e}\,d,\qquad
|q_i-p_i^e|\le K_GL\sqrt{C/c_e}\,d=A_wd.
$$
For all six old cells, $q_i\ge p_*/2>0$. At most six supported original atoms can occupy at most six cells because none is split. There must therefore be exactly one positive atom in each old cell, none in cell $4$, and no unassigned atom. Proportional subdivisions or a redundant spare positive atom would exceed this bound. Zero padding contributes no atom. Thus $p_i=q_i$ after matching. The fact that $p_4^e=0$ is fully retained; QS's theorem requiring seven positive masses is not invoked.

For the single atom in old cell $i$, its contribution to the gap estimate is
$p_i(d_{\mathbb T}(\phi_i,\phi_i^e)^2+r_i)\le Cd^2/c_e$.
Since $p_i\ge p_*/2$, the angular and inward bounds follow with $A_q$ as defined. If the additional coordinate-ball gate holds, $A_qd\le D_{\rm loc}d<R_x\le1/2$, so the shortest lifts are unambiguous. For $d\le1$ the squared coordinate norm is at most
$$
6(A_w^2d^2+A_q^2d^2+A_q^4d^4)
 \le D_{\rm loc}^2d^2.
$$
This proves the uniform estimate for every maximizing law, starting from the global fractional class, rather than assuming a preassigned local chart or active contrast. $\square$

**Theorem 12.3 (inward orientation, all active subsets and quantitative activity).** At the event the inward multipliers are exactly
$$
\nu_i^e=p_i^e(R_i+|H_i^{\rm opp}|-\epsilon_iH_i^{\rm opp})
                 \ge p_*c_{\rm sh}\Delta^2\ge m_\mu,
\qquad\lambda_e\ge m_\mu .
$$
The $15$ columns of $Q_e$ are independent. If a constrained local maximizer lies at $\|x-x_e\|_2<R_x$, every active constraint subset satisfies LICQ, its contrast and all six inward multipliers are positive, and
$$
K=\kappa,\qquad r=0.
$$

Proof. The inward computation refines the multiplier identity already used in §5. For an occupied endpoint let
$Q_h=Y_{e,5}+Y_{e,6}u^2+Y_{e,7}uv$.
Differentiate the raw fractional gap in the actual inward coordinate
$\xi=\eta+(1-2\eta)r$. The occupied nonzero height has sign $\epsilon$, so
$$
\partial_rD_e\big|_{r=0}
 =(1-2\eta)c_h(Q_h-\epsilon\,1000f_h).
$$
For $\eta=0$ the prefactor is $+1$; for $\eta=1$ it is $-1$, using that endpoint's own occupied sign. By the occupied equality and affineness, the same expression is
$$
Y_e\cdot\Gamma_{1-\eta}-\lambda_e|u|-\epsilon H_{1-\eta}
 =D_{1-\eta}^e+|H_{1-\eta}|-\epsilon H_{1-\eta}.
$$
If $\epsilon H_{1-\eta}\ge0$, including a zero opposite height, the last added term vanishes. If $\epsilon H_{1-\eta}<0$, it equals $2|H_{1-\eta}|$. No opposite-sign term is discarded and no same-sign premise is introduced. Opposite-sheet contact separation and Theorem 10.2's endpoint estimate give
$R_i\ge c_{\rm sh}\Delta^2$.

Use the minimization Lagrangian
$$
\mathscr L(x,Y,\lambda,\nu)
 =Y\cdot(\mathcal M(x)-B)-\mathcal J(x)
                        +\lambda(\kappa-\mathcal K(x))-\nu\cdot r.
$$
Differentiating in $r_i$ multiplies the raw inward gap by $p_i$. Its stationarity therefore derives $\nu_i^e=p_i^e\chi_i$; the coefficient weight is essential. This proves the lower bounds because $p_i^e>p_*$ and $\lambda_e>190$, and gives
$Q_ey_e=\nabla\mathcal J(x_e)$.

For rank, restrict a relation among the columns of $Q_e$ to variations with $dr=0$. In the twelve coordinates $z=(p,\phi)$ the eight moment rows $A=D_z\mathcal M(x_e)$ have rank eight, and $q=\nabla_z\mathcal K(x_e)$ is nonzero on $\ker A$, by the retained event geometry. Consequently $[A^T,-q]$ has nine independent columns; the relation's first nine coefficients vanish. The remaining six coordinate columns $-E_r^T$ are independent, so the other coefficients vanish too. In particular every subfamily consisting of all moment columns and any active subset of the seven inequality columns is independent.

For $\|x-x_e\|<R_x$, singular-value perturbation gives
$$
\sigma_{\min}(Q(x))
 \ge\sigma-\|Q(x)-Q_e\|_2\ge\sigma/2.
$$
The chart ball removes weight-boundary and upper-$r$ constraints and fixes the height/report signs. At a constrained local maximizer KKT thus applies to its active subset. Extend the inactive contrast or inward multipliers by zero into a full vector $y=(Y,\lambda,\nu)$. Stationarity reads $Q(x)y=\nabla\mathcal J(x)$. A left inverse of $Q(x)$ has norm at most $2/\sigma$, so
$$
\begin{aligned}
\|y-y_e\|_2
&\le\frac2\sigma
\left(\|\nabla\mathcal J(x)-\nabla\mathcal J(x_e)\|_2
            +\|Q(x)-Q_e\|_2\|y_e\|_2\right)\\
&\le C_\mu\|x-x_e\|_2<m_\mu/2 .
\end{aligned}
$$
Every inequality multiplier is strictly positive, since its event value is at least $m_\mu$. An extended inactive multiplier could not have that property. Complementarity forces all six endpoints and the contrast active. In particular the overshoot controlled globally in Theorem 12.2 is now zero. $\square$

## 13. Recipe IV: the exact bordered system and its contraction ball

**Definition 13.1 (face variables, boxes and constants).** On $r=0$ write
$z=(p,\phi)\in\mathbb R^{12}$, $w=(z,Y,\lambda)\in\mathbb R^{21}$, and
$w_e=(p^e,\phi^e,Y_e,\lambda_e)$. Define
$$
\Psi(w;\kappa)=
\begin{pmatrix}
\nabla_z\{Y\cdot(\mathcal M(z,0)-B)
                    -\mathcal J(z,0)-\lambda(\mathcal K(z,0)-\kappa)\}\\
\mathcal M(z,0)-B\\
\kappa-\mathcal K(z,0)
\end{pmatrix}.
$$
Its event $21\times21$ Jacobian, in this exact row and column order, is
$$
\mathcal B_e=D_w\Psi(w_e;k_e)
 =\begin{pmatrix}
 H&A^T&-q\\ A&0&0\\-q^T&0&0
 \end{pmatrix},
\qquad
H=\nabla_z^2\mathscr L_e,\quad
A=D_z\mathcal M_e,\quad q=\nabla_z\mathcal K_e.
$$
The block dimensions are $12,8,1$. This is the fixed-contrast face system, not the $22$-variable event system, not a seven-positive-weight Hessian and not a stationary system with an unremoved zero coefficient.

Choose rational $\beta_B\ge\max(1,\|\mathcal B_e^{-1}\|_2)$ and
$L_B\ge1$ bounding the Lipschitz constant of $D_w\Psi$ on the specified closed Euclidean ball
$\overline B(w_e,R_{\rm chart})$. In particular $\|Y-Y_e\|_2\le R_{\rm chart}\le1/2$ and $|\lambda-\lambda_e|\le R_{\rm chart}\le1/2$ there; bounding instead on the product of the $z$ chart ball with multiplier variations at most one is sufficient. The $w$ derivative is independent of $\kappa$, so this bound has no additional target-contrast input. All derivatives are of the signed extensions just defined, with $r=0$.

The exact inverse exists by the argument below; $\beta_B$ is an unevaluated bound for it, not an assumed uniqueness radius. The symbol $\beta_B$ is the bordered inverse bound, distinct from the source fraction $\beta=1-\alpha$. Put
$$
R_f=\min\{R_{\rm chart},1/(2\beta_BL_B)\},\qquad
C_{\rm joint}=1+C_\mu .
$$

**Theorem 13.2 (existence, self-mapping and uniqueness at fixed contrast).** If
$|\kappa-k_e|\le R_f/(2\beta_B)$, the system $\Psi(w;\kappa)=0$ has exactly one root in $\overline B(w_e,R_f)$. A globally maximizing law from Theorem 12.2 equals the same-strength six branch whenever, in addition to its localization and activity gates,
$$
d<\min\{R_f/(2C_{\rm joint}D_{\rm loc}),R_f/(2C_{\rm br})\}.
$$
Equality means the original fractional coefficient law up to permutation, not uniqueness of its full instrument or time law.

Proof. A homogeneous kernel vector $(\dot z,\dot Y,\dot\lambda)$ of $\mathcal B_e$ obeys $A\dot z=0$, $q^T\dot z=0$. Pairing its first equation with $\dot z$ yields $\dot z^TH\dot z=0$. The retained positive Hessian on $\ker A$ (and hence on this proper constrained tangent) gives $\dot z=0$. The independent nine constraint columns then give $\dot Y=\dot\lambda=0$. This proves nonsingularity. Neither the non-tangent seven-minus-six response nor a variable carrying zero weight is put into a positive-tangent argument.

For the frozen-Jacobian map
$T_\kappa(w)=w-\mathcal B_e^{-1}\Psi(w;\kappa)$, the derivative bound on the closed ball is
$$
\|D_wT_\kappa(w)\|_2
\le\beta_BL_B\|w-w_e\|_2
\le\beta_BL_BR_f\le1/2.
$$
At the center, only the final constraint row changes with $\kappa$, so
$\|\Psi(w_e;\kappa)\|_2=|\kappa-k_e|=d$ and
$\|T_\kappa(w_e)-w_e\|_2\le\beta_Bd\le R_f/2$.
Consequently for every $w$ in the closed ball,
$$
\|T_\kappa(w)-w_e\|_2
 \le\tfrac12\|w-w_e\|_2+\beta_Bd\le R_f.
$$
This proves self-mapping as well as contraction; a derivative bound alone would not suffice. The contraction principle gives exactly one fixed point, and invertibility of $\mathcal B_e$ identifies it with exactly one root.

Theorems 12.2–12.3 place any global maximizer on $r=0$. Its KKT multipliers obey the displayed bound, and dropping the inward multipliers gives
$$
\|w-w_e\|_2
 \le(1+C_\mu)\|x-x_e\|_2
 \le C_{\rm joint}D_{\rm loc}d<R_f/2.
$$
The extended six branch satisfies this same fixed-contrast KKT system: its occupied value and derivative equations give stationarity, and its own inverse multiplier gives $K=\kappa$. Theorem 11.3 and its separate gate place it within $R_f/2$ as well. The unique-root conclusion identifies the two. This supplies an explicit replacement for the unnamed implicit-function neighborhood in Theorem 5.3. $\square$

## 14. Recipe V: an explicit symbolic loss window in the original class

**Definition 14.1 (all window gates and HALF-TV constants).** With every input defined in §§9–13, set
$$
\begin{gathered}
d_*=\min\left\{
1,\frac{k_e}{2},d_{\rm branch},\frac{p_*}{2A_w},
\frac{R_x}{D_{\rm loc}},
\frac{R_f}{2C_{\rm joint}D_{\rm loc}},
\frac{R_f}{2C_{\rm br}},\frac{R_f}{2\beta_B}
\right\},\qquad
\varepsilon=\frac{d_*}{a_s},\\
c_- =\frac{\alpha}{4s_0^2}
              \left(\frac1{u_6}-\frac1{l_7}\right),\qquad
c_+ =\frac{\alpha}{4s_0^2}
              \left(\frac1{l_6}-\frac1{u_7}\right).
\end{gathered}
$$
Every term in this finite minimum is required. All denominators are strictly positive:
$a_s,s_0,\alpha,\beta,d_\eta,c_h,l_b,u_b,1-q_b,c_e,p_*,
\sigma,C_\mu,D_{\rm loc},C_{\rm br},\beta_B,L_B$ have the respective positive bounds already specified. The original source supplies $k_e>0$ and $\lambda_e>190$. Thus $d_*>0$ and $\varepsilon>0$. The strict ordering $u_6<l_7$ gives $c_->0$, and $l_6<u_7$ gives $c_+>0$. These are exact symbolic constants conditional on the stated source and finite bounds. No numerical value of $d_*,\varepsilon,c_-,c_+$ is asserted.

**Theorem 14.2 (uniform same-strength optimum and two-sided local loss).** Under Assumption 1.2, the fixed OE/QS correspondences of Definition 9.1 and the finite inputs of §§10–13, for
$$
s_e-\varepsilon<s<s_e
$$
every maximizing fractional law in $\mathcal Q_6$, with all eight original moments and $K\ge a_s s$, consists of the six old endpoint atoms and equals the inverse six branch at its own target $\kappa=a_s s$, up to permutation. Its contrast is active. In the original full-complex multi-Kraus acquisition class,
$$
\begin{gathered}
\mathcal T_A^{(\le6\ {\rm supported\ nonzero\ low})}(s)
 =\mathcal T_A^{(\le7\ {\rm TOTAL})}(s)=V_6(s),\qquad
\mathcal T_A^{\rm full}(s)=V_7(s),\quad A=\log1001,\\
c_-(s-s_e)^2
\le\mathcal T_A^{\rm full}(s)-\mathcal T_A^{(\le7\ {\rm TOTAL})}(s)
\le c_+(s-s_e)^2 .
\end{gathered}
$$
The inverse multipliers used to evaluate $V_6$ and $V_7$ are generally different. Each is evaluated at the same requested strength.

Proof. Put $d=k_e-\kappa=a_s(s_e-s)$. Then $0<d<d_*$. The gate $d<k_e/2$ keeps $\kappa>0$; $d<d_{\rm branch}$ puts both inverse multipliers in their specified supplier intervals and boxes. The next gates give the old-cell occupancy, the $R_x$ coordinate ball, the positive active multipliers and both placements in the $R_f$ uniqueness ball. The last gate gives its self-mapping. Theorems 12.2, 12.3 and 13.2 consequently identify every global maximizing six-law with the same-strength endpoint six branch. This is the quantitative version of the qualitative conclusion of §5, using no additional localization premise.

For the original upper bound, every admitted instrument with at most six supported nonzero low actual labels has, before height optimization, the same fractional law in $\mathcal Q_6$ by the retained full-class reduction. Its actual height, original eight moments, capacities and contrast inequality are unchanged. This includes arbitrary complex multi-Kraus labels, arbitrary admitted competing time laws and redundant actual representations. It does not expose hidden Kraus indices or split an existing fractional acquisition into two endpoints. The law bound therefore gives actual HALF-TV at most $V_6(s)$ for every such instrument.

For the reverse inequality apply the finite common-law constructor, in the general finite-law form of QS Proposition 4.1, FA Theorem 87.3 and RC Proposition 75.1, using OE §9's identical formulas. The continued six law has six positive weights, all eight moments and $b_{{\rm label},i}\in\{0,1000c_{h_i}\}$. These are precisely the constructor's premises, regardless of the unused dual gap's sign. At each low label form
$$
\begin{gathered}
K_i=\sqrt{p_i}L_{h_i},\quad
N_i=p_i b_{{\rm label},i}n_{h_i}n_{h_i}^T,\quad
J_i:\mathbb C^2\longrightarrow\operatorname{ran}K_i^*,\\
Q_i=J_i^*(K_i^*K_i+N_i)J_i\succ0,\quad
C_i=Q_i^{1/2}J_i^*E^*,\quad
B_i=K_iJ_iQ_i^{-1/2},\quad
F_i=Q_i^{-1/2}J_i^*N_iJ_iQ_i^{-1/2}.
\end{gathered}
$$
Here $J_i$ is an isometry; it is unrelated to the low-height objective $J$ or the left inverse $J_{\rm left}$. Rank-two capacity gives
$B_i^*B_i+F_i=I_2$, $I_2-F_i\succeq I_2/1001$, and whole-fibre activity
$\log(1+b_{{\rm label},i}/c_{h_i})\in\{0,\log1001\}$. Use the common density
$g(a)=2/(1+a)^2$ and cumulative function $G_{\rm time}(a)=2a/(1+a)$ with
$$
Z_i(a)=\sqrt{I_2-G_{\rm time}(a)F_i},\qquad
R_i(a)=g(a)F_i[I_2-G_{\rm time}(a)F_i]^{-1}.
$$
The survivor and jump effects sum to the identity at every cut; only terminal survivors receive the isometry $EB_i(I_2-F_i)^{-1/2}$. Low deterministic reports $\sigma_i$ give exactly $K/a_s=s$. The sufficient choice $g$ is distinct from the ideal density $f_y(a)=6y/(y+6a)^2$, and puts no density restriction on competitors in the upper bound.

For the original five-mode isometry
$E=((e_0+e_{13})/\sqrt2,(e_1+e_3)/\sqrt2,e_2)$ put $P=EE^*$.
Choose isometries $W_\perp:\mathbb C^2\to P^\perp$ and
$J_0:\mathbb C^2\to\mathbb C^3$. The one high encoder and its two hidden terminal decoder matrices are
$$
C_H=\begin{pmatrix}\sqrt{1-\delta}DE^*\\ W_\perp^*\end{pmatrix},
\qquad E[I_3\ 0],\quad EJ_0[0\ I_2].
$$
This dimension-five acquired fibre has report $+$ and rate zero; its terminal Kraus indices are discarded. Their effects sum to the identity on that entire fibre. All six low encoders and this one high encoder have total effect $I_5$ by the root TP identity and the full same-law moments. The full complex live map is
$$
\Phi^L(X)=E[\Lambda_*(E^*XE)+
               J_0W_\perp^*XW_\perp J_0^*]E^*,\qquad
\Lambda_*(Y)=DYD^*+TYT^*+SYS^*.
$$
For every Borel set $\mathcal B\subseteq[0,1]$, every complex $X\in M_5$, and each separate original failure label $\ell\in\{0,1,2,3,13\}$, the forgotten-acquisition failure map is
$$
\Phi^f_\ell(\mathcal B)(X)
 =w_\ell\left(\int_{\mathcal B}g(a)\,da\right)
                          \operatorname{tr}(EME^*X)P_f .
$$
With any passive reference the conditional operator is
$$
w_\ell\left(\int_{\mathcal B}g(a)\,da\right)P_f\otimes
       \operatorname{Tr}_5[(EME^*\otimes I_R)X].
$$
The reference is not replaced by its unconditional marginal. These identities include the zero components $\ell=0,13$ and retain live coherences. The original minimax premise gives the eight $y=5,27$ errors equal to $E_*$ and the four $y=16$ errors strictly smaller. The one high acquisition is positive on the original histories, with probability
$(1-\delta)\sum_jh_j^2p_{yj}$, maximal at $y=27$; its worst-history value is the original sharp JOINT cost $\mathsf C(s)$. All later-accessible input-bearing shares are included in the counted entire fibres. FIRST is absolute $6+a$, survivor controls and terminal processing are TP, no failed carrier receives later positive-carrier action, and no terminal forced absorption is added. Thus the same original instrument attains $V_6(s)$ with six low labels and one counted high label, proving the first original optimum equality conditionally.

Every instrument with at most seven TOTAL generated actual labels has at least one compulsory positive high label and hence at most six supported nonzero low labels. Any supported-zero labels still consume total count and supply no supported moment, contrast or height. The constructor includes its supported-zero complementary input subspace in its single high label. It has seven TOTAL labels, so supplies the matching lower bound and the second equality. This is equality of optima by a sandwich, not equality of full feasible classes. The original unrestricted optimum $V_7(s)$ is supplied on this left interval by OE's full-circle dual and the common constructor.

For the quantitative loss, put $\mathcal D(\kappa)=V_7(\kappa)-V_6(\kappa)$, with $V_b=(H_{\rm high}+J_b)/2$. The common event embeddings give
$\mathcal D(k_e)=\mathcal D'(k_e)=0$, and Proposition 3.1 yields
$$
\mathcal D''(\kappa)=\frac12
 \left(\frac1{k_{6,\lambda}(\lambda_6(\kappa))}
           -\frac1{k_{7,\lambda}(\lambda_7(\kappa))}\right).
$$
The same-target inverse bounds, evaluated on the two respective multiplier intervals, imply
$$
\frac12\left(\frac1{u_6}-\frac1{l_7}\right)
\le\mathcal D''(\kappa)
\le\frac12\left(\frac1{l_6}-\frac1{u_7}\right).
$$
For $\kappa<k_e$ the positive integration kernel gives
$$
\mathcal D(\kappa)=\int_\kappa^{k_e}(t-\kappa)\mathcal D''(t)\,dt,
\qquad \int_\kappa^{k_e}(t-\kappa)\,dt=(\kappa-k_e)^2/2 .
$$
Thus the two coefficients in $\kappa$ are exactly
$(1/u_6-1/l_7)/4$ and $(1/l_6-1/u_7)/4$.
The first factor $1/2$ is the actual HALF-TV normalization, and the second is from twice integration. Substituting
$\kappa-k_e=a_s(s-s_e)$ gives exactly $c_-,c_+$, including their factor $\alpha/(4s_0^2)$. No little-$o$ remainder, common-multiplier replacement, or qualitative continuity radius is needed. $\square$

## 15. Source correspondence, finite obligations and unresolved scope

**Definition 15.1 (exact mathematical correspondence).** The references in this table identify which conditional inputs and established tools are used by the quantitative deduction. They do not turn any supplier hypothesis into a numerical certificate.

| Fixed source | Correspondence and retained boundary |
| --- | --- |
| This owner, §§2–3 | $a=k_{6,\lambda}(\lambda_e)>0$, $b=k_{7,\lambda}(\lambda_e)>a$, $b-a=-p_4'd_6'$ with $d_6'=P_4'/d_4$; $J_{b,\kappa}=-\lambda_b$ and the original HALF conversion. These response and value identities are reused. |
| This owner, §§4–7 | Compactness, qualitative event localization, inward multiplier formula, proper-tangent positivity and qualitative short-alphabet loss. §§10–14 give explicit bounds and gates for these conclusions, rather than counting them as new qualitative theorems. |
| OE Definitions 2.1–3.1 and Proposition 3.2 | The same original source amplitudes, signs of $\Delta_\rho$, positive physical capacity, full eight $\Gamma$ moments and actual-label absolute height; coefficient weights are not acquired probabilities. |
| OE Definitions 4.1–4.2, §§5 and 12–15 | Original clearing denominators, bases, variables, all value rows before derivative rows, exact event embedding, full branch boxes, rational preconditioners and defect norms. Event $p_4=0$ is removed before inverses. Six retains unused $x_4$ through stationarity only. |
| OE §§6–7, Appendices 16–17 | All eight signed event cases, complete circle/axis coverage, exact double factors, positive Bernstein quotients, all seven separated zeros, six old positive masses and the row-$(0,1,2,3,4,5,7)$ minor. The six off-event unused constant is retained. The cleared derivative comparison is not a normalized unused-gap derivative away from the event. |
| QS Theorems 5.2–5.3, 6.1 and 7.1 | Exact affine/chord slack, overshoot identity, geometric coercivity and no-split moment rounding. The gap and rounding arguments do not require positive mass at each event zero. The seven-positive-mass count theorem in QS §8 is not applied with $p_4=0$; Theorem 12.2 supplies the six-old-cell argument. |
| [CG §§13–17 and Convention 21.3][CGpin] | Isolated-root dictionary/ranks/TP and the full twelve-history stopped-cq HALF minimax, with its precise averaged-live and preaverage conclusions, in the stipulated finite/countable/measurable class. The additional unaveraged face remains separate. |
| [JR §§34, 37, 41–42][JRpin] | Original contrast and sharp worst-history acquired JOINT cost; the supported unaveraged live/effect equality face applies to every original error/cost optimizer before height optimization. |
| [FA §§67–70, 77–78 and 87][FApin]; [RC §§67 and 75][RCpin]; OE §9; QS §§3–4 | Whole-fibre survival, arbitrary complex multi-Kraus double rigidity, same-law capacity and all physical covariances, supported-zero labels counted, and finite common instrument with one coherent high acquisition. The endpoint construction realizes the extended six law without requiring its dual to be optimal. Its sufficient time density restricts no competing law. |

**Definition 15.2 (unevaluated original-source obligations).** A numerical strength window requires outward evaluation at the same exact original source of all the following inputs and their displayed consequences. None is supplied as an evaluated numerical quantity by the present symbolic recipe.

1. Retain the original isolated source/root equations, isolation, source dictionary, exact ranks and root TP; full stopped-cq minimax; sharp worst-history JOINT cost; unaveraged equality face before height optimization; arbitrary-complex multi-Kraus rigidity, whole-fibre capacity, same-law reduction and coherent completion. Source-box comparisons alone settle none of these original antecedents.
2. Retain the fixed OE event and branch root/embedding, full signed Bernstein and complete-zero data, old-weight/height/report/separation margins, moment independence and proper-tangent regularity. Authentication of their enclosure provenance, if required, is separate from reading their exact mathematical statements. The present appendix gives no new event isolation.
3. Evaluate $d_{\max},M_H,M_3$ from the original normalized rational functions on all eight charts and both entire sheets; evaluate $M_\phi,M_\xi,L$, the full event $A_7$, its stated left inverse $J_{\rm left}$ and $K_G$. Then evaluate every term of $\gamma_*,\rho,d_{\rm off},c_{\rm sh},c_e$. No unknown off-contact minimum or sampled sign test replaces these quantities.
4. Evaluate the event derivative matrices $F_{6,X},F_{6,\lambda},D_Xk_6$ and $F_{7,X},F_{7,\lambda},D_Xk_7$, solve both original event linear systems and outward-certify $0<a<b$. The original coarse derivative-center residual enclosures alone do not certify the small $a$. On the full supplied branch boxes bound $\|R_{{\rm pre},b}\|_2$, $q_b<1$, $N_b,P_b,Q_b,R_b,K_{1b},K_{2b}$ for each $b$. The omitted $F_{\lambda\lambda}$ term is zero for these exact cleared systems, not for an arbitrary reparameterized system. Evaluate $\tau,l_b,u_b,U_b,W_b,T_b,h_b,d_{\rm branch},C,A_w,A_q,D_{\rm loc},C_{\rm br}$ with the scaled-to-Euclidean conversion.
5. Evaluate the complete signed $18$-variable derivatives on $\mathcal X$, giving $M_{Hx},L_Q,L_J$. Form the full event $18\times15$ matrix $Q_e$ and certify $\sigma_{\min}(Q_e)\ge\sigma>0$ in Euclidean norm. Evaluate all opposite-height cases in $\chi_i$, the actual weighted $\nu_i^e$, $\|y_e\|_2$, and hence $R_{\rm chart},m_\mu,C_\mu,R_x$. A substituted same-sign premise or the unweighted gap $R_i$ alone does not supply these multipliers.
6. Form every block of the exact event $21\times21$ matrix $\mathcal B_e$, bound its inverse by $\beta_B$, and bound the full Jacobian Lipschitz constant $L_B$ on the specified face/multiplier ball. Evaluate $R_f,C_{\rm joint}$ and verify both contraction and self-mapping gates. A nonsingularity statement without inverse and derivative bounds is not a numerical radius.
7. Outward-enclose $k_e,\lambda_e,\alpha,\beta,s_0,a_s$ and all preceding constants at this same source. Evaluate separately every member
$$
1,\quad k_e/2,\quad d_{\rm branch},\quad p_*/(2A_w),\quad
R_x/D_{\rm loc},\quad R_f/(2C_{\rm joint}D_{\rm loc}),\quad
R_f/(2C_{\rm br}),\quad R_f/(2\beta_B)
$$
of the defining minimum $d_*$, then $\varepsilon=d_*/a_s$ and both $c_-,c_+$. All strict positivity, denominator exclusion, branch-box containment, norm conversion and ordering checks must use outward bounds. Source pivots, square roots, the capacity denominator, chart denominators including $x_6+1$, $1-q_b$, $l_b,u_b$, $\sigma$, and the bordered inverse cannot be inferred from displayed midpoint decimals.

The listed matrices, derivative intervals and each $d_*$ term remain unevaluated here. The symbolic theorem is conditional on their stated bounds; no decimal $\varepsilon$, newly certified event, or universally evaluated count follows.

**Definition 15.3 (literature tools and original deduction).** The quantitative combination of the original endpoint factors, zero-seventh-mass no-split localization, active constraints, same-strength inverse comparison and original acquired-label transfer is `repo-derived`. Banach contraction, Taylor's integral formula, KKT under LICQ, finite-dimensional singular-value perturbation and Bernstein basis positivity are standard tools within that deduction, with the attributions in §8.

For an explicit-radius comparison, O. P. Ferreira and B. F. Svaiter, *Kantorovich's Theorem on Newton's Method*, [arXiv:1209.5704v1, Theorem 1](https://arxiv.org/html/1209.5704v1), gives a standard Newton theorem under invertibility of $F'(x_0)$, a preconditioned derivative Lipschitz bound $L_{\rm NK}$, residual bound $b_{\rm NK}$, $2b_{\rm NK}L_{\rm NK}\le1$, and containment of the resulting ball in the differentiability domain. Its scalar radii are
$$
t_* =\frac{1-\sqrt{1-2b_{\rm NK}L_{\rm NK}}}{L_{\rm NK}},
\qquad
t_{**}=\frac{1+\sqrt{1-2b_{\rm NK}L_{\rm NK}}}{L_{\rm NK}}.
$$
Here the correspondence is $F=\Psi$, $x_0=w_e$,
$b_{\rm NK}\le\beta_Bd$, $L_{\rm NK}\le\beta_BL_B$.
The gates in §§13–14 imply $2b_{\rm NK}L_{\rm NK}\le1/2$ and the direct self-mapping argument supplies the needed containment. This reference is `literature-attested` only for that general method. The proof above directly establishes the stronger gates it uses; the literature supplies no quantum reduction, original event inventory, source derivative bound, positive seventh mass, evaluated constant or original count conclusion. No exhaustive search, worldwide novelty or historical-byte identity claim is needed.

**Definition 15.4 (the unchanged open programme).** This fixed-$t$ local increment does not complete the original through-2027 programme. The complete evaluated finite-$(s,A)$ roof for all budgets and feasible contrasts, the distinct strong branch, all original actual counts and oriented coefficient/failure allocations, live-height decompositions, selected roots and positive common weights, universal necessity, complete ordering, connected coverage, degeneracies, gluing and one common original attainer at every point remain required at their original scopes. Higher-count seeds, universal or dense seven-original-fractional-low and universal eight-low questions, actual affine coexistence, and exact strong optimal counts remain unresolved; the inherited maximum minimum TOTAL alphabet bound remains $\{8,9,10\}$ at its supplier scope.

The selected multiplier interval does not connect the ranges below $1/4$, the intervening gap $(23/5,190.449003333)$ or any later event; no chronologically next event, maximal range or transverse-budget atlas is identified. The original remaining $K(s)$, source-coefficient evaluations, physical orientations, coefficient gluing, transition-root isolation and multiplicities, height/report sign intervals and next terms, critical five-label/static-contact interpolation, floor/rising/strong/degenerate thresholds and uniform JOINT limits retain every outstanding obligation of OE Definition 10.2 and QS §10. Finite prescribed-product results are not an infinite-product or unbounded uniform-limit theorem.

All twelve histories, original five separate Borel failure components, actual-label HALF TV, the independent minimax and sharp worst-history JOINT objectives, unaveraged equality face, arbitrary complex multi-Kraus competitors and admitted time laws remain unchanged. Low coefficient atoms, actual generated labels, supported-zero labels, hidden Kraus multiplicity, failure labels and joint quantum dimension remain distinct. The whole-fibre activity and conditional passive-reference operators, absolute FIRST clock, no-copy/no-retry/no-postselection rules and counted coherent high completion remain as in §§1 and 14. No LOSR, PPT, diamond norm, product-input metric, free-class or count substitution is used.

Source-final approval, actual quantum access and calibration, coherent storage of all counted shares, acquisition duration, whole-fibre actuation, absolute FIRST alignment, archive/source/epoch/controller interfaces, permissions and the original quantum-native interpretation still require their own bridges. Ordinary conditional CP/TP instrument existence supplies no empirical operation or native authorization.

[OEpin]: https://github.com/the-omega-institute/trureturing/blob/321589a8be98de4fe179f99f6e593d8784952db1/docs/develop/theory/FIB_NATIVE_COMPLETE_CONTINUATION_LOCAL_OUTPUT_EXTINCTION.md
[QSpin]: https://github.com/the-omega-institute/trureturing/blob/4751be04555dc6a71e83e0c8f5dcdc5e26d104de/docs/develop/theory/FIB_NATIVE_COMPLETE_CONTINUATION_QUANTITATIVE_OUTPUT_STABILITY.md

[CGpin]: https://github.com/the-omega-institute/trureturing/blob/321589a8be98de4fe179f99f6e593d8784952db1/docs/develop/theory/FIB_NATIVE_COMPLETE_CONTINUATION_DISTINGUISHABILITY_GAP.md
[JRpin]: https://github.com/the-omega-institute/trureturing/blob/321589a8be98de4fe179f99f6e593d8784952db1/docs/develop/theory/FIB_NATIVE_COMPLETE_CONTINUATION_JOINT_RECORD_PAYLOAD.md
[FApin]: https://github.com/the-omega-institute/trureturing/blob/321589a8be98de4fe179f99f6e593d8784952db1/docs/develop/theory/FIB_NATIVE_COMPLETE_CONTINUATION_FINITE_ACTIVITY_FRONTIER.md
[RCpin]: https://github.com/the-omega-institute/trureturing/blob/321589a8be98de4fe179f99f6e593d8784952db1/docs/develop/theory/FIB_NATIVE_COMPLETE_CONTINUATION_RESIDUAL_CONTACT_CURVE.md

## 追加锚（本行以下为增补区）

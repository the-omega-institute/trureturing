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

## 16. Evaluated conditional certificate at the original extinction event

**Definition 16.1 (antecedents and exact centre).** Retain Assumption 1.2 and the fixed-source correspondences of Definitions 9.1 and 15.1. The following hypotheses are named separately throughout §§16–24.

- $\mathsf H_{\rm root}$ is OE Assumption 1.2(1): the same isolated CG root in its nine-coordinate radius-$10^{-24}$ box, its stipulated dictionary and ranks, and root TP. The exact reconstruction is OE Definition 2.1, including its positive-pivot adjugates; no off-root rank identity is used.
- $\mathsf H_{\rm original}$ comprises the original twelve-history HALF stopped-cq minimax, JR's sharp worst-history JOINT and supported unaveraged equality face before height optimization, and FA/RC's arbitrary-complex multi-Kraus actual-label rigidity, capacity, same-law reduction and coherent one-high constructor, at precisely their retained scopes. It includes the compulsory positive high acquisition, the whole-fibre convention, all five separate failure Borel maps and their conditional passive-reference operators, and absolute FIRST clock $6+a$. These interfaces are not consequences of interval arithmetic.
- $\mathsf H_{\rm sections}$ is the supplied OE event existence/isolation, its common exact embeddings into both branch sections, their isolation in the complete prescribed boxes, Appendix 12's comparison enclosures and Appendix 14's exact preconditioners with uniform scaled defects. In particular $q_6<0.000172$ and $q_7<0.01$ on those entire boxes and the entire multiplier interval. No new source or event isolation is asserted.
- $\mathsf H_{\rm contacts}$ is the supplied complete seven-contact inventory, exact event double-factor identities, Bernstein quotient enclosures and covering leaves, and the old-weight, height, report, separation and proper-tangent margins in OE §§6–7 and Appendices 16–17. The complete tables consist of $24$ signed cases, $147$ leaves, $831$ control intervals and $126$ power-coefficient intervals. Their ordering, coverage and lower-control comparisons are finite data checks; their originating coefficient enclosures and root certificates remain inherited. Counting or authenticating these tables does not regenerate their coefficients.

The full-cylinder and no-split deductions of §§10–14, using the exact slack identities and rounding argument of QS §§5–7, are reused. The positive-mass-at-every-zero count theorem of QS §8 is not an antecedent: here $p_4^e=0$ exactly. Every conclusion below is conditional on all four named hypotheses.

Set exactly

$$
t=1000,\qquad A=\log1001,\qquad
 a_s=\frac{\sqrt\alpha}{s_0},\qquad
 s_e=\frac{k_e}{a_s},\qquad
 \varepsilon_0=2\cdot10^{-153},\qquad
 c_{-,0}=394256130000,\quad c_{+,0}=657236410000.
$$

The decimal enclosure $s_e\in[0.125205844467,0.125205844468]$ is only a location bound. The centre in every window is the exact common event $k_e/a_s$, never a decimal endpoint, midpoint or independently chosen nearby source. The window has mathematical width $2\cdot10^{-153}$; no operational resolution or practical widening is implicit.

**Definition 16.2 (pinned mathematical suppliers).** OE, CG, GC, JR, FA and RC mean the respective original-source files at `321589a8be98de4fe179f99f6e593d8784952db1`; QS means its file at `4751be04555dc6a71e83e0c8f5dcdc5e26d104de`. GC denotes [Global actual counts][GCpin]. The finite numerical mathematical suppliers are the supplied C313 candidate tables and C316 independently reconstructed arithmetic tables. They are fallible mathematical data, with no additional logical authority. The rational witnesses, defining functions and outward comparisons used here are specified in this appendix and the pinned OE tables; no inaccessible numerical file is a required premise. The attributions in Definitions 8.2 and 15.3 apply to the standard analytic tools; this evaluated source-specific application is `repo-derived`, with no literature-wide novelty claim.

The fixed OE and QS source identities have SHA-256 digests `eef92ebbb4ff32147059580e8648fef47280d0fd33eaec2c1c51ccb81b348f29` and `70bfdb1e28b51dc604cb98ede4861b79d437aa485bb390480363047c6dead5c7`, respectively. These identify mathematical suppliers; neither digest certifies a root, TP or any original physical bridge.

**Definition 16.3 (original-source dictionary and comparison boxes).** All symbols retain Definition 9.2, with $a_{\rm src},b_{\rm src},c_{\rm src},d_{\rm src}$ reserved for source amplitudes, $a,b$ for the two response derivatives, $\beta$ for the source fraction and $\beta_B$ for a bordered inverse bound. In particular

$$
\begin{gathered}
D=\operatorname{diag}(h_0,h_1,h_2),\quad
T=a_{\rm src}e_0e_1^T+b_{\rm src}e_1e_0^T,\quad
S=c_{\rm src}e_0e_2^T+d_{\rm src}e_2e_0^T,\quad
M=\operatorname{diag}(0,m_1,m_2),\quad
\Delta_\rho=
\begin{pmatrix}
11/64&(\sqrt{999}-\sqrt{295})/128&(\sqrt{27}-\sqrt5)/16\\
(\sqrt{999}-\sqrt{295})/128&-11/64&(\sqrt{37}-\sqrt{59})/16\\
(\sqrt{27}-\sqrt5)/16&(\sqrt{37}-\sqrt{59})/16&0
\end{pmatrix},\\
(K_0,K_1,K_2)=(D,T,S),\quad
N_{ij}=\operatorname{tr}(K_i\Delta_\rho K_j^T),\quad
G=\operatorname{diag}(s_0,1,1)N\operatorname{diag}(s_0,1,1),\\
\theta=\frac{a_{\rm src}b_{\rm src}}{h_0h_1},\quad
\omega=\frac{c_{\rm src}d_{\rm src}}{h_0h_2},\quad
\delta=\theta+\omega=s_0^2,\quad \alpha=\theta/\delta,\quad\beta=\omega/\delta,\\
u=\cos\phi,\quad v=\sin\phi,\quad z=u/\sqrt\alpha,\quad w=v/\sqrt\beta,\quad
h=(1,z,w)^T,\quad L_h=s_0D+zT+wS,\quad
n_h=(0,d_{\rm src}w/h_2,-b_{\rm src}z/h_1)^T,\\
\ell_h=h^TGh,\quad f_h=n_h^T\Delta_\rho n_h,\quad
c_h=\frac{h_1^2h_2^2\delta+a_{\rm src}^2h_2^2z^2+c_{\rm src}^2h_1^2w^2}
{h_0^2\delta+b_{\rm src}^2z^2+d_{\rm src}^2w^2},\quad
b_{\rm label}=1000c_h\xi,\\
\Gamma_\xi=(1,u,v,u^2,uv,\xi c_h,\xi c_hu^2,\xi c_huv),\quad
H_\xi=\ell_h+1000c_h\xi f_h,\\
V_f=m_2h_1^2/b_{\rm src}^2,\quad W_f=m_1h_2^2/d_{\rm src}^2,\quad
\mu=\alpha V_f+\beta W_f,\quad
B=(1,0,0,\alpha,0,\mu/1000,\alpha V_f/1000,0),\\
\int\Gamma_\xi\,d\pi=B,\quad K(\pi)=\int|u|\,d\pi\ge\kappa=a_ss,\quad
J(\pi)=\int|H_\xi|\,d\pi,\quad
T_{\rm actual}=(H_{\rm high}+J)/2,\quad H_{\rm high}=(1-\delta)N_{00}.
\end{gathered}
$$

The matrix $\Delta_\rho$ is GC.28 with the height orientation $27-5$. Coefficient weights, physical acquired probabilities and endpoint/failure-line groups are distinct. The eight displayed moments give both full covariances $\int hh^T\,d\pi=I_3$ and $\int b_{\rm label}n_hn_h^T\,d\pi=M$, including the cross entries; they are never optimized separately.

For every interval comparison the source rectangle is exactly the nine integer endpoint pairs of OE Appendix 12 divided by $2^{224}$, varied independently. It is not the product of the coarser decimal bounds below. The event rectangle is exactly the $22$ rows of OE Appendix 15.1 divided by $2^{150}$. In that order it is

$$
(x_0,\ldots,x_6,p_0,p_1,p_2,p_3,p_5,p_6,Y_0,\ldots,Y_7,\lambda).
$$

The omitted event weight is $p_4=0$. Seven inserts this zero and removes $\lambda$; six takes the $O=(0,1,2,3,5,6)$ angle and weight sublists, then $Y$, then unused $x_4$. Full branch centres are OE Appendix 13's exact decimals under these same embeddings. Every angle and weight has radius $10^{-8}$, including the six unused $x_4$ and seven signed $p_4$; every $Y$ has radius $10^{-4}$; $\lambda\in[190.449003333,190.449005333]$. The event existence box, with radii $10^{-10},10^{-7},10^{-6}$, is distinct from its refined event rectangle and from these branch boxes.

The endpoint/height/report/base dictionary is precisely the seven-row table in Definition 9.3: indices $0,1,2,3$ are pure, $4,5,6$ saturated; the signs are $(+,+,-,+,+,-,-)$ for height and $(+,-,-,+,+,-,+)$ for report. Bases are $(0,\pi,\pi,0,0,\pi,3\pi/2)$. Thus the old occupied indices are $0,1,2,3,5,6$, not the first six indices. The original margin weakenings are

$$
p_*=11/250,\quad h_*=3/1000,\quad u_*=79/100,\quad
\Delta=29/100,\quad q_B=1/8000,\quad h_{\lambda,0}=9/10^7.
$$

**Proposition 16.4 (outward source and event scalars).** Under the named hypotheses the following are closed outward rational intervals. Every decimal in this appendix is exact; no floating-point rounding convention is implicit.

| Quantity | Lower | Upper |
| --- | --- | --- |
| $h_0$ | $0.984341295186$ | $0.984341295187$ |
| $h_1$ | $0.706284581667$ | $0.706284581668$ |
| $h_2$ | $0.809497327848$ | $0.809497327849$ |
| $a_{\rm src}$ | $0.0656644991486$ | $0.0656644991487$ |
| $b_{\rm src}$ | $0.145993080138$ | $0.145993080139$ |
| $c_{\rm src}$ | $0.0154967056182$ | $0.0154967056183$ |
| $d_{\rm src}$ | $0.0987837797518$ | $0.0987837797519$ |
| $m_1$ | $0.49685026325$ | $0.496850263251$ |
| $m_2$ | $0.344473928321$ | $0.344473928322$ |
| $\theta$ | $0.0137891493902$ | $0.0137891493903$ |
| $\omega$ | $0.00192116160276$ | $0.00192116160277$ |
| $\delta$ | $0.015710310993$ | $0.0157103109931$ |
| $\alpha$ | $0.877713330842$ | $0.877713330843$ |
| $\beta$ | $0.122286669157$ | $0.122286669158$ |
| $s_0$ | $0.125340779449$ | $0.125340779450$ |
| $a_s$ | $7.47453115047$ | $7.47453115048$ |
| $k_e$ | $0.935854984693$ | $0.935854984694$ |
| $\lambda_e$ | $190.449004332$ | $190.449004333$ |

Proof. The first nine comparisons follow by integer comparison with OE Appendix 12. The remaining source entries follow by positive multiplication, division and square roots in Definition 16.3; $k_e=\sum_{i\in O}p_i\sigma_i u_i$ is evaluated on the exact event rectangle and $\lambda_e$ is its last coordinate. The interval prescription in §17 specifies these operations. The source pivots are retained through $\mathsf H_{\rm root}$; the displayed positive amplitudes, $\theta,\omega,\alpha,\beta,s_0$ exclude every subsequent scalar source denominator. They do not establish TP throughout the rectangle. $\square$

## 17. Finite arithmetic, derivative tensors and residual witnesses

**Definition 17.1 (directed intervals and ordinary derivatives).** For $D_{300}=2^{300}$ enclose a rational $x$ by $[\lfloor D_{300}x\rfloor,\lceil D_{300}x\rceil]/D_{300}$. After addition, multiplication, reciprocal, or square-root operations round the lower endpoint down and upper endpoint up on that grid. Products use all four endpoint products; a square has lower endpoint zero if its interval crosses zero. A reciprocal is taken only after zero exclusion. For a nonnegative $[l,h]$, integer comparisons $m^2\le D_{300}^2l$ and $n^2\ge D_{300}^2h$ give the outward square-root endpoints. Exact rational arithmetic with no rounding is also admissible. The final tiny radii in §22 use exact fractions and relative square-root enclosures: for $x>0$, choose an integer $e$ with $1\le2^{-2e}x<4$, enclose that rescaled square root on a dyadic grid and rescale by $2^e$. Thus no fixed absolute grid can underflow a positive radius.

For ordinary, unnormalized derivative jets, products and quotients obey

$$
\begin{aligned}
(fg)^{(j)}&=\sum_{i=0}^j\binom ji f^{(i)}g^{(j-i)},\\
q^{(0)}&=1/d^{(0)},\qquad
q^{(j)}=-\frac1{d^{(0)}}\sum_{i=1}^j\binom ji d^{(i)}q^{(j-i)}
\quad(q=1/d).
\end{aligned}
$$

The corresponding multi-index identities give all partial derivatives. No Taylor factorial is omitted when a tensor is formed. Whole-circle bounds use $u,v\in[-1,1]$, $u'=-v$, $v'=u$, $u''=-u$, $v''=-v$, through the required order, allowing the two zeroth-order coordinates to vary independently for an upper enclosure. In the zeroth capacity denominator retain the nonnegative squares:

$$
d_{\rm cap}=h_0^2\delta+(b_{\rm src}^2/\alpha)u^2+
(d_{\rm src}^2/\beta)v^2\ge h_0^2\delta>0.0152221568385.
$$

Derivatives of $d_{\rm cap}$ use the product identities, not the derivative of this lower bound. Use the $\Gamma,H$ formulas of Definition 16.3 for normalized angular derivatives. On branch boxes use Definition 10.1's cleared polynomials, $r_c=1+x^2$ and the specified three bases. For a polynomial $\sum c_jx^j$, its $m$th jet is exactly $\sum_{j\ge m}j!c_jx^{j-m}/(j-m)!$. Moment derivatives still use the normalized rational columns. These prescriptions determine every matrix and tensor below from the pinned source/event/branch rectangles.

For a tensor enclosure $\mathbf T$ put $\operatorname{maj}(\mathbf T)=(\sum_{i_1,\ldots,i_d}\sup|\mathbf T_{i_1\cdots i_d}|^2)^{1/2}$. This full Frobenius bound dominates the Euclidean multilinear operator norm by Cauchy–Schwarz. It includes both orders of each symmetric mixed pair, and every order of a third derivative with multiplier indices. Norms in what follows are Euclidean unless explicitly marked $\infty$ or scaled.

**Proposition 17.2 (finite inverse verification).** Let $\mathbf C$ enclose an $n$-square matrix $C$ and let $R$ be a displayed rational candidate. Define

$$
q_R=\max_i\sum_j\sup|\delta_{ij}-(R\mathbf C)_{ij}|,\qquad
r_R=\max_i\sum_j|R_{ij}|.
$$

If $q_R<1$, then $C$ is invertible and

$$
\|C^{-1}\|_\infty\le\frac{r_R}{1-q_R},\qquad
\|C^{-1}\|_2\le\frac{n r_R}{1-q_R}.
$$

For a parameter response $Cv=-f$ and any rational trial $v_0$,

$$
\|v-v_0\|_\infty\le
\frac{\|R(\mathbf C v_0+\mathbf f)\|_\infty}{1-q_R}.
$$

Proof. The geometric series in $I-RC$ has infinity norm at most $(1-q_R)^{-1}$, and $(RC)^{-1}R=C^{-1}$. The stated Euclidean bound follows even from the coarser inequality $\|T\|_2\le n\|T\|_\infty$. Applying $(RC)^{-1}$ to $R(Cv_0+f)$ proves the response estimate. This is a finite residual proof, with no significance attached to a candidate's numerical origin. $\square$

**Definition 17.3 (witness ordering).** Section 24 gives rational candidates $R_A,R_Q,R_B,R_6,R_7$ and trial responses $v_6^0,v_7^0$, all with denominator $10^{30}$. The matrices they precondition are, respectively, $S_7A_7$, the specified $15$-row minor of $Q_e$, the full off-root enclosure of $\mathcal B_e$, and the separate full $F_{6,X}$ and $F_{7,X}$ event Jacobians. Their entries are computed by Definition 17.1 from the exact source/event rectangles. Thus the source specifies both the candidate and every expression it multiplies; neither a solver midpoint nor a box corner is substituted for the actual source.

## 18. Evaluated recipe I: full-cylinder coercivity

**Proposition 18.1 (global normalized-function bounds).** Under the four named hypotheses the following selected rational upper bounds hold on the complete domains in §§10–12:

| Input | Selected value | Domain or meaning |
| --- | --- | --- |
| $d_{\max}$ | $4$ | Both closed report half-circles, all eight signed endpoint cases |
| $M_H$ | $369.125719756$ | $|\partial_\phi H_\eta|$ on each entire endpoint circle |
| $M_3$ | $3991698.40169$ | Third angular derivative of each normalized signed event gap |
| $M_\phi$ | $17.2182040803$ | $\|\partial_\phi\Gamma_\xi\|_2$ on $X$ |
| $M_\xi$ | $3.7587270313$ | $\|\partial_\xi\Gamma_\xi\|_2$ on $X$ |
| $L$ | $17.6236937289$ | At least $\sqrt{M_\phi^2+M_\xi^2}$ |
| $K_G$ | $1059.0362612$ | Every row norm of $(S_7A_7)^{-1}S_7$ |

Proof. On pure charts $d_0=(1+x^2)^2\le4$. On saturated charts

$$
d_1=D_c(1+x^2)^2\le
16\left(h_0^2\delta+b_{\rm src}^2/\alpha+d_{\rm src}^2/\beta\right)<4.
$$

Here $|U|,|V|\le1+x^2$ and $1+x^2\le2$, and the positive denominator lower bound in Definition 17.1 excludes poles. Evaluating normalized angular jets, with the nonnegative denominator squares retained, gives

$$
\begin{gathered}
\max_\eta\sup|H_\eta'|\le M_H,\qquad
\max_{\eta,\epsilon,\sigma}\sup
|Y_e\cdot\Gamma_\eta'''-\epsilon H_\eta'''-
\lambda_e\sigma u'''|\le M_3,\\
\operatorname{maj}(\partial_\phi\Gamma_\xi)\le M_\phi,
\qquad \operatorname{maj}(\partial_\xi\Gamma_\xi)\le M_\xi.
\end{gathered}
$$

These are interval comparisons using the source rows and event $Y,\lambda$, with $\xi\in[0,1]$; no cleared-polynomial derivative replaces a normalized derivative. The $L$ comparison follows by squaring its positive endpoints. For the left inverse take precisely the minor rows $S_7=(0,1,2,3,4,5,7)$. The $R_A$ witness gives

$$
q_{R_A}\le4.62721429217\cdot10^{-17},\qquad
r_{R_A}\le151.290894457,\qquad
\frac{7r_{R_A}}{1-q_{R_A}}<1059.0362612.
$$

Proposition 17.2 and $\|S_7\|_2=1$ bound the whole left inverse and therefore each of its rows. This supplies a finite witness for $K_G$, not just the inherited nonzero determinant. $\square$

**Proposition 18.2 (evaluated gap constants).** With exactly the inputs above, the constants of Definition 10.1 have outward intervals

| Constant | Lower | Upper |
| --- | --- | --- |
| $\gamma_*$ | $3.28515625\cdot10^{-7}$ | $3.28515625\cdot10^{-7}$ |
| $\rho$ | $4.11498555177\cdot10^{-14}$ | $4.11498555178\cdot10^{-14}$ |
| $d_{\rm off}$ | $5.60019691210\cdot10^{-60}$ | $5.60019691211\cdot10^{-60}$ |
| $c_{\rm sh}$ | $5.60019691210\cdot10^{-61}$ | $5.60019691211\cdot10^{-61}$ |
| $c_e$ | $5.35200636714\cdot10^{-64}$ | $5.35200636715\cdot10^{-64}$ |

Consequently $D_e\ge c_e\mathfrak d^2$ on the entire fractional cylinder, including height zeros and both report axes.

Proof. Substitute $q_B=1/8000$, $\Delta=29/100$, $d_{\max}=4$ into $\gamma_*=q_B\Delta^2/(8d_{\max})$. In the minimum defining $\rho$, the smallest member is $\gamma_* /(2M_3)$; compare it with $1/2,\Delta/4,u_*/2,h_* /(2M_H)$ by positive cross multiplication. Then substitute successively into $d_{\rm off}=q_B(\rho/2)^4/d_{\max}$, $c_{\rm sh}=\min(\gamma_*/4,d_{\rm off}/10)$ and $c_e=c_{\rm sh}\Delta^2/88$. Here $d_{\rm off}/10$ is the smaller member. These exact rational operations give the table. Theorem 10.2 supplies the full-cylinder consequence using the inherited exact event factors and complete leaves, with the factor $\Delta^2/88$ retained. No uncomputed off-support minimum is introduced. The contact-$6$ chart change has $x_6+1>1.49$ on its refined event rectangle, so its denominator also excludes zero. $\square$

## 19. Evaluated recipe II: separate responses and complete branch boxes

**Definition 19.1 (both exact differentiated systems).** Use the full original row orders in OE Definition 4.2. In either branch the first eight rows are the moment equations. If $I_6=O$, $I_7=\{0,\ldots,6\}$, their derivatives in the half-angle and weight columns are $p_i\Gamma_i'$ and $\Gamma_i$. All value rows $P_i$ precede all derivative rows $P_i'$. A value row has $x_i$ entry $P_i'$, $Y$ entries $\Gamma_{{\rm num},i}$ and parameter derivative $-\sigma_iW_{{\rm num},i}$. A derivative row has $x_i$ entry $P_i''$, $Y$ entries $\Gamma_{{\rm num},i}'$ and parameter derivative $-\sigma_iW_{{\rm num},i}'$. Other entries vanish except the displayed moment derivatives. Six has the extra final row $P_4'(x_4)$ and final column $x_4$, with entries $P_4''$ and $\Gamma_{{\rm num},4}'$ in that row; its parameter derivative is $-\sigma_4W_{{\rm num},4}'$. It has no value row $P_4$ and no weight column $p_4$. These formulas specify every entry without deleting the unused stationary angle.

For $J_b=F_{b,X}$ and $f_b=F_{b,\lambda}$ at the exact event, solve separately

$$
J_6v_6=-f_6,\qquad J_7v_7=-f_7,\qquad
 a=D_Xk_6v_6,\quad b=D_Xk_7v_7.
$$

The half-angle entries of $D_Xk_b$ are $p_i\sigma_i u_i'$ and its weight entries are $\sigma_i u_i$; all $Y$ entries and the six unused $x_4$ entry are zero. This is ordinary differentiation in the original coordinates, not an adopted coarse derivative centre from OE Appendix 17.

**Proposition 19.2 (finite event solves, including the small six response).** The §24 witnesses and the exact event rectangle give the following outward bounds:

| System | $\|I-R_b\mathbf J_b\|_\infty$ upper | $\|R_b\|_\infty$ upper | Euclidean inverse upper | $\|v_b-v_b^0\|_\infty$ upper |
| --- | --- | --- | --- | --- |
| $F_6$ | $2.17417396081\cdot10^{-12}$ | $180427.008196$ | $3788967.17213$ | $1.4\cdot10^{-17}$ |
| $F_7$ | $3.05254308934\cdot10^{-11}$ | $20074.3549344$ | $441635.808571$ | $2.01\cdot10^{-15}$ |

In particular

$$
\begin{gathered}
2.83264015392\cdot10^{-11}\le a\le2.83266211059\cdot10^{-11},\\
6.84687781515\cdot10^{-8}\le b\le6.84688086610\cdot10^{-8},\qquad 0<a<b.
\end{gathered}
$$

For the finer finite radius arithmetic, valid enclosing numerator pairs over the common denominator $2^{300}$ are

| Response | Lower numerator | Upper numerator |
| --- | --- | --- |
| $a$ | $57701899015645180801507086161464628207517552637740592529000272967303177339112552$ | $57702346280673657739636734338700593324400679155032278880682627172333162791904725$ |
| $b$ | $139473364350334886308524521683639965870471236860830251914350418378478490115253344307$ | $139473426499093092021104729933967577407226047730929850475068499216778116583941517911$ |

Proof. Apply Proposition 17.2 separately to the two matrices specified in Definition 19.1. Direct row sums of the rational witnesses and interval matrix products give the table; the response residual divided by $1-q_R$ is at most $1.391471993503\cdot10^{-17}$ on six and $2.008571892572\cdot10^{-15}$ on seven. Multiplication by the complete $D_Xk_b$, enclosing each solution coordinate by $v_b^0$ plus its error interval, gives intervals contained in the displayed dyadic bounds for $a,b$. Positive cross multiplication proves $0<a<b$. This also permits the weaker supplied coordinate errors $1.81773432464\cdot10^{-17}$ and $2.22563824343\cdot10^{-15}$, but the tighter residual estimates just stated suffice for these particular rational trial vectors. At the event the independent response identity of Theorem 2.3 still reads $b-a=-p_4'd_6'>0$, with $d_6'=\dot P_4/d_4$; a cleared derivative is not used without $d_4$. $\square$

**Proposition 19.3 (uniform Euclidean bounds on the entire prescribed branch boxes).** The following rational selections are valid. The columns $P,Q,R,K_1,K_2$ bound respectively $F_\lambda,F_{XX},F_{X\lambda},D_Xk,D_X^2k$ in the norms of Definition 11.1.

| Input | Six branch | Seven branch |
| --- | --- | --- |
| Dimension $n_b$ | $21$ | $22$ |
| $\max r_b/\min r_b$ | $10000$ | $10000$ |
| $\|R_{{\rm pre},b}\|_\infty$ upper | $180427.008196$ | $20074.3549344$ |
| Selected inherited $q_b$ | $0.000172$ | $0.01$ |
| $N_b$ | $37896189865.9$ | $4460967763.2$ |
| $P_b$ | $2.05021657197$ | $2.05140973139$ |
| $Q_b$ | $3047.45994554$ | $3047.66871219$ |
| $R_b$ | $1.3729251606$ | $1.38551774339$ |
| $K_{1b}$ | $2.22683824561$ | $2.37112622335$ |
| $K_{2b}$ | $3.12608472396$ | $3.46246784408$ |
| $U_b$ upper | $77695396477.6$ | $9151272680.85$ |
| $W_b$ upper | $6.9714662338\cdot10^{35}$ | $1.13857025534\cdot10^{33}$ |
| $T_b$ upper | $1.55243276375\cdot10^{36}$ | $2.69969378957\cdot10^{33}$ |

Proof. Appendix 14's exact integer matrices divided by $2^{151}$ give the two preconditioner row sums. For a radius-scaled defect, Proposition 17.2 in the scaled infinity norm, followed by the two norm conversions, gives the sufficient bound

$$
\|F_{b,X}^{-1}\|_2\le
\frac{n_b\,10000\,\|R_{{\rm pre},b}\|_\infty}{1-q_b}\le N_b.
$$

Thus the scaled defect is never treated as an unscaled Euclidean contraction. The table's $N_b$ inequalities are exact rational comparisons with this expression. Differentiate the full row formulas of Definition 19.1 on the full boxes, not just their root tubes. In a moment row the only nonzero second partials are $p_i\Gamma_i''$ and both orders of $\Gamma_i'$ in the $(p_i,x_i)$ pair. In a value row they are $P_i''$ and both $(x_i,Y_j)$ orders of $\Gamma_{{\rm num},i,j}'$; in a derivative row they are $P_i'''$ and both orders of $\Gamma_{{\rm num},i,j}''$. The same derivative-row formula applies to six's unused $x_4$. Parameter mixed derivatives are $-\sigma_iW_{{\rm num},i}'$ in a value row and $-\sigma_iW_{{\rm num},i}''$ in a derivative row. This exhausts the entries; $F_{\lambda\lambda}=0$ exactly. For $k$ the nonzero second entries are $p_i\sigma_i u_i''$ and both orders of $\sigma_i u_i'$ in the mixed weight/angle pair.

The interval jets of Definition 17.1 and full Frobenius sums of these entries give exactly the selected $P,Q,R,K_1,K_2$ bounds. All weight intervals, signed seven $p_4$, all $Y$ intervals and the whole multiplier interval participate. In succession the displayed selections satisfy

$$
U_b\ge N_bP_b,\qquad
W_b\ge N_b(Q_bU_b^2+2R_bU_b),\qquad
T_b\ge\max(1,K_{2b}U_b^2+K_{1b}W_b).
$$

Using these upward rational majorants instead of equality in Definition 11.2 preserves every bound in Theorem 11.3 and conservatively reduces its allowed inverse intervals. Subsequent constants use these displayed selections. This harmless outward selection does not alter either original system. The chart conversion for $C_{\rm br}$ remains $|d\phi/dx|\le2$. $\square$

**Proposition 19.4 (evaluated same-target inversion constants).** With $a,b$ the exact responses enclosed in Proposition 19.2 and the selections in Proposition 19.3, the inverse-branch construction of §11 gives

| Constant | Lower | Upper |
| --- | --- | --- |
| $\tau$ | $7.08160038482\cdot10^{-12}$ | $7.08165527648\cdot10^{-12}$ |
| $l_6$ | $2.12447462628\cdot10^{-11}$ | $2.12450207211\cdot10^{-11}$ |
| $u_6$ | $3.54080019241\cdot10^{-11}$ | $3.54082763824\cdot10^{-11}$ |
| $l_7$ | $6.84616964962\cdot10^{-8}$ | $6.84617270606\cdot10^{-8}$ |
| $u_7$ | $6.84758597519\cdot10^{-8}$ | $6.84758903163\cdot10^{-8}$ |
| $h_6$ | $4.56161487323\cdot10^{-48}$ | $4.56165023171\cdot10^{-48}$ |
| $h_7$ | $2.62311244785\cdot10^{-45}$ | $2.62313278041\cdot10^{-45}$ |
| $d_{\rm branch}$ | $9.69103505306\cdot10^{-59}$ | $9.69123536949\cdot10^{-59}$ |
| $C$ | $23534926445.3$ | $23535230490.2$ |
| $A_w$ | $1.23767289311\cdot10^{41}$ | $1.23768088777\cdot10^{41}$ |
| $A_q$ | $4.47081574303\cdot10^{37}$ | $4.47084462190\cdot10^{37}$ |
| $D_{\rm loc}$ | $4.89608747299\cdot10^{75}$ | $4.89615072495\cdot10^{75}$ |
| $C_{\rm br}$ | $7.31422176501\cdot10^{21}$ | $7.31431625654\cdot10^{21}$ |

Proof. Evaluate Definition 11.2 with the exact dyadic response enclosures and positive denominators. Here $\tau=a/4<(b-a)/4$, $h_b=\tau/T_b<h_{\lambda,0}$, and $l_6h_6<l_7h_7$ throughout the enclosures. Compare these choices before taking each minimum. Outward square roots and reciprocal endpoints then give the last five rows from $C=1/(2l_6)$, $A_w=K_GL\sqrt{C/c_e}$, $A_q=\sqrt{2C/(c_ep_*)}$, $D_{\rm loc}=\sqrt{6(A_w^2+A_q^2+A_q^4)}$ and $C_{\rm br}=(2U_6+1)/l_6$. The table proves $0<l_6\le u_6<l_7\le u_7$. The inherited multiplier embedding margin is greater than $9.999\cdot10^{-7}>h_{\lambda,0}$, so both inverse intervals remain inside $I$. Theorem 11.3 supplies the six feasible comparator, its $Cd^2$ slack bound and its $C_{\rm br}d$ joint-coordinate bound. The targets are the same $\kappa$ but the two inverse multipliers are separate. $\square$

## 20. Evaluated recipe III: no-split localization and all active subsets

**Proposition 20.1 (full coordinate-box derivative and LICQ bounds).** On the entire prescribed box $\mathcal X$ of Definition 12.1, selected rational bounds are

$$
M_{Hx}=738.534183019,\qquad
L_Q=4896.33417097,\qquad L_J=106981.054612.
$$

For the complete $18\times15$ matrix $Q_e$, in row order $(p_O,\phi_O,r_O)$ and column order $(Y_0,\ldots,Y_7,\lambda,\nu_O)$,

$$
\sigma_{\min}(Q_e)\ge\sigma:=\frac{3125}{11338247023}
>2.75615797897\cdot10^{-7}.
$$

Proof. Since $0<p_i^e<1$, the bounding box gives $|p_i|\le2$. With $r_i\in[-1,1]$, either endpoint orientation gives $\xi_i\in[-1,2]$. Form $\mathcal M,\mathcal J,\mathcal K$ as in Definition 12.1 and differentiate their signed extensions on this whole box. For each height use the Frobenius majorant of its $(\phi_i,r_i)$ gradient. For the two Lipschitz constants use

$$
L_Q^2\ \ge\sum_{j=0}^7\operatorname{maj}(D_x^2\mathcal M_j)^2+
                    \operatorname{maj}(D_x^2\mathcal K)^2,
\qquad
L_J\ge\operatorname{maj}(D_x^2\mathcal J).
$$

The inward-coordinate columns $-E_r^T$ are constant. A summand $p_i f(\phi_i,r_i)$ contributes $p_i f_{\phi\phi}$, $p_i f_{\phi r}$ in both orders, $f_\phi$ in both weight/angle orders and $f_r$ in both weight/inward orders; $f_{rr}=0$. These entries, the jets in §17 and $|p_i|\le2$, $\xi_i\in[-1,2]$ give the three selected bounds. No differentiability of the actual absolute height outside the small chart ball is claimed.

Every entry of the full event matrix has the explicit block form

$$
Q_e=\begin{pmatrix}
 (\Gamma_i)_{{i\in O}}&(-\sigma_i u_i)_{{i\in O}}&0\\
 (p_i\partial_\phi\Gamma_i)_{{i\in O}}&(p_i\sigma_i v_i)_{{i\in O}}&0\\
 (p_i(1-2\eta_i)\partial_\xi\Gamma_i)_{{i\in O}}&0&-I_6
\end{pmatrix},
$$

where each left block is written as six rows with eight moment columns. Select the rows

$$
S_Q=(0,1,2,3,4,5,6,7,10,12,13,14,15,16,17)
$$

without discarding any of the $15$ columns. For $C_Q=S_QQ_e$, the rational $R_Q$ witness gives

$$
q_{R_Q}\le6.70862769012\cdot10^{-15},\qquad
r_{R_Q}\le241882.603157,\qquad
\|C_Q^{-1}\|_2\le3628239.04736=\frac{11338247023}{3125}.
$$

For every $v\in\mathbb R^{15}$, $\|Q_ev\|_2\ge\|C_Qv\|_2\ge\sigma\|v\|_2$. This proves the claimed full-matrix bound. The same lower bound holds for every column subfamily by extending its coefficient vector by zeros in all other columns. In particular it covers all moment columns plus any active subset of the contrast and six inward constraints, not merely the fully active face. $\square$

**Proposition 20.2 (both inward orientations and weighted multipliers).** The six event raw inward derivatives $\chi_i$ and actual inward multipliers $\nu_i^e=p_i^e\chi_i$ have the following outward intervals, in old-index order $O$:

| $i$ | $\chi_i$ lower | $\chi_i$ upper | $\nu_i^e$ lower | $\nu_i^e$ upper |
| --- | --- | --- | --- | --- |
| $0$ | $4.20961943005$ | $4.20961943006$ | $1.13857262586$ | $1.13857262587$ |
| $1$ | $7.50977258619$ | $7.50977258620$ | $2.03009156569$ | $2.03009156570$ |
| $2$ | $5.12142026146$ | $5.12142026147$ | $0.949641731466$ | $0.949641731467$ |
| $3$ | $7.51922807131$ | $7.51922807132$ | $1.39280806906$ | $1.39280806907$ |
| $5$ | $2.34997011081$ | $2.34997011082$ | $0.104038333905$ | $0.104038333906$ |
| $6$ | $2.36005407132$ | $2.36005407133$ | $0.104488083402$ | $0.104488083403$ |

Also $\|y_e\|_2\le301.183623108$ for $y_e=(Y_e,\lambda_e,\nu^e)$. The resulting constants of Definition 12.1 satisfy

| Constant | Lower | Upper |
| --- | --- | --- |
| $R_{\rm chart}$ | $2.03105019982\cdot10^{-6}$ | $2.03105019983\cdot10^{-6}$ |
| $m_\mu$ | $2.07229686535\cdot10^{-63}$ | $2.07229686536\cdot10^{-63}$ |
| $C_\mu$ | $11477402472800$ | $11477402472900$ |
| $R_x$ | $9.02772587376\cdot10^{-77}$ | $9.02772587377\cdot10^{-77}$ |

Proof. Use the original inward derivative, including the saturated endpoint's minus sign,

$$
\chi_i=(1-2\eta_i)c_i
(Y_{e,5}+Y_{e,6}u_i^2+Y_{e,7}u_iv_i-\epsilon_i1000f_i).
$$

Equivalently, by the occupied event equality,
$\chi_i=R_i+|H_i^{\rm opp}|-\epsilon_iH_i^{\rm opp}$.
The correction is zero for $\epsilon_iH_i^{\rm opp}\ge0$ and $2|H_i^{\rm opp}|$ for the opposite sign; it includes zero opposite height without a new sign assumption. Interval substitution on the event rectangle yields the table from the raw formula, and multiplication by each actual coefficient weight yields $\nu^e$. All $18$ event stationarity coordinates are those of $Q_ey_e=\nabla\mathcal J(x_e)$, by the contact equations and this inward identity. The norm bound follows by summing the squares of the eight $Y$ coordinates, the contrast multiplier and these six multipliers.

Evaluate $R_{\rm chart}$ from Definition 12.1: its smallest member is $h_* /(2M_{Hx})$. The smaller member in $m_\mu$ is $p_*c_{\rm sh}\Delta^2$, and $C_\mu=2(L_J+L_Q\cdot301.183623108)/\sigma$ is the conservative choice using the selected norm bound. In $R_x$, the smallest member is $m_\mu/(2C_\mu)$. Exact positive rational comparisons and relative square roots give the displayed intervals.

Theorems 12.2–12.3 now apply uniformly to every global maximizing fractional six-law whenever their displayed $d$ gates hold. Their no-split assignment uses one cell per original atom, forces one positive atom in each old cell and no atom in cell $4$, and first controls the overshoot $0\le K-\kappa\le Cd^2/\lambda_e$. Full-matrix LICQ and the positive multipliers then force that overshoot to zero and identify all endpoint constraints. This application does not assume locality, active contrast, or a positive seventh event mass. $\square$

## 21. Evaluated recipe IV: full bordered Jacobian and multiplier variation

**Definition 21.1 (all off-root entries).** For an old contact define the signed normalized gap

$$
g_i(\phi;Y,\lambda)=Y\cdot\Gamma_{\eta_i}(\phi)
 -\epsilon_iH_{\eta_i}(\phi)-\lambda\sigma_i\cos\phi.
$$

On the endpoint face use $z=(p_O,\phi_O)$ and $w=(z,Y_0,\ldots,Y_7,\lambda)$. At any point of the enclosing rectangle, not just an exact contact root, the full Hessian block is

$$
H_{p_ip_j}=0,\qquad
H_{p_i\phi_j}=H_{\phi_jp_i}=\delta_{ij}g_i',\qquad
H_{\phi_i\phi_j}=\delta_{ij}p_i g_i''.
$$

The moment block has $A_{j,p_i}=\Gamma_{i,j}$ and $A_{j,\phi_i}=p_i\Gamma_{i,j}'$, while $q_{p_i}=\sigma_i u_i$, $q_{\phi_i}=-p_i\sigma_i v_i$. These formulas form every entry of

$$
\mathbf B_e=\begin{pmatrix}H&A^T&-q\\A&0&0\\-q^T&0&0\end{pmatrix}
$$

by interval evaluation on the exact event rectangle. The block sizes are $12,8,1$, in precisely that order. The mixed $g_i'$ terms are enclosed as raw expressions; they are not set to zero on a rectangular box by imposing root equations at its other points. This is the full $21\times21$ fixed-contrast face system, distinct from $F_6,F_7$ and the $22$-variable event system.

**Proposition 21.2 (bordered inverse and full Jacobian Lipschitz constant).** Valid selected bounds are

$$
\beta_B=2674263171960,\qquad L_B=11399894.7864.
$$

Consequently the constants of Definition 13.1 have enclosures

$$
\begin{gathered}
1.64007994346\cdot10^{-20}\le R_f\le1.64007994347\cdot10^{-20},\\
11477402472800\le C_{\rm joint}\le11477402472900.
\end{gathered}
$$

Proof. For the §24 candidate $R_B$, multiplication against all $441$ off-root interval entries gives

$$
\|I-R_B\mathbf B_e\|_\infty\le9.29214770243\cdot10^{-9},\qquad
\|R_B\|_\infty\le127345864148.
$$

The tighter row-sum comparison specified by the witness, rather than rounding both inputs up before division, gives

$$
\frac{21\|R_B\|_\infty}{1-\|I-R_B\mathbf B_e\|_\infty}
<2674263171960.
$$

Proposition 17.2 supplies the Euclidean inverse bound. It uses neither positivity of an unrestricted Hessian nor an inverse involving a zero-weight seventh angle.

For the uniform Lipschitz bound use the scalar face Lagrangian
$\mathscr L_f=Y\cdot(\mathcal M-B)-\mathcal J+\lambda(\kappa-\mathcal K)$.
The system $\Psi$ is its complete $w$ gradient. On the product of the face coordinate box with $|Y_j-Y_{e,j}|\le1$, $|\lambda-\lambda_e|\le1$, the only third derivative families are

$$
\begin{aligned}
D^3_{zzz}\mathscr L_f&=\sum_jY_jD^3_z\mathcal M_j-D^3_z\mathcal J-
\lambda D^3_z\mathcal K,\\
D^3_{zzY_j}\mathscr L_f&=D^2_z\mathcal M_j,
\qquad D^3_{zz\lambda}\mathscr L_f=-D^2_z\mathcal K.
\end{aligned}
$$

Each mixed family occurs in all three index positions; entries with two multiplier indices vanish. Thus a sufficient, fully off-root bound is

$$
L_B^2\ge
\operatorname{maj}\!\left(\sum_jY_jD^3\mathcal M_j-D^3\mathcal J-
\lambda D^3\mathcal K\right)^2
+3\sum_j\operatorname{maj}(D^2\mathcal M_j)^2
+3\operatorname{maj}(D^2\mathcal K)^2.
$$

Use $|p_i|\le2$, the entire circle and the normalized jets through order three from §17. The resulting upper bound is at most the selected $11399894.7864$. This covers the required ball of radius $R_{\rm chart}$, since all its multiplier variations are at most $1/2<1$. In particular the multiplier/Hessian terms are not silently dropped. Finally $R_f=1/(2\beta_BL_B)<R_{\rm chart}$ and $C_{\rm joint}=1+C_\mu$ give the two enclosures by exact arithmetic. $\square$

## 22. Evaluated recipe V: every radius gate and HALF coefficient

**Proposition 22.1 (all eight finite gates).** Using the outward selections above in the conservative recipe, the eight members of the minimum in Definition 14.1 have the following enclosures:

| Member | Lower | Upper |
| --- | --- | --- |
| $1$ | $1$ | $1$ |
| $k_e/2$ | $0.467927492346$ | $0.467927492347$ |
| $d_{\rm branch}$ | $9.69103505306\cdot10^{-59}$ | $9.69123536949\cdot10^{-59}$ |
| $p_* /(2A_w)$ | $1.77751795454\cdot10^{-43}$ | $1.77752943628\cdot10^{-43}$ |
| $R_x/D_{\rm loc}$ | $1.84384149527\cdot10^{-152}$ | $1.84386531564\cdot10^{-152}$ |
| $R_f/(2C_{\rm joint}D_{\rm loc})$ | $1.45927328554\cdot10^{-109}$ | $1.45929213772\cdot10^{-109}$ |
| $R_f/(2C_{\rm br})$ | $1.12114371729\cdot10^{-42}$ | $1.12115820122\cdot10^{-42}$ |
| $R_f/(2\beta_B)$ | $3.06641463088\cdot10^{-33}$ | $3.06641463089\cdot10^{-33}$ |

The minimum is $R_x/D_{\rm loc}$. For the resulting recipe constants,

| Output | Lower | Upper |
| --- | --- | --- |
| $d_*$ | $1.84384149527\cdot10^{-152}$ | $1.84386531564\cdot10^{-152}$ |
| $\varepsilon_{\rm recipe}=d_* /a_s$ | $2.46683231115\cdot10^{-153}$ | $2.46686417986\cdot10^{-153}$ |
| $c_{-,\rm recipe}$ | $394256134925$ | $394259192598$ |
| $c_{+,\rm recipe}$ | $657227911192$ | $657236404565$ |

Proof. Substitute the exact fractional expressions from §§18–21, not a point selected from each displayed interval. Interval minima take the minimum of lower endpoints and the minimum of upper endpoints; positive ratios use lower numerator/upper denominator and upper numerator/lower denominator. Relative square roots as in Definition 17.1 retain positivity through $R_x$ and $d_*$. These operations applied to the displayed defining formulas yield the enclosures above. In particular compare the upper endpoint of $R_x/D_{\rm loc}$ with the lower endpoint of each of the other seven members; all seven comparisons are strict.

For the loss coefficients retain the exact conversion

$$
c_{-,\rm recipe}=\frac{\alpha}{4s_0^2}\left(\frac1{u_6}-\frac1{l_7}\right),\qquad
c_{+,\rm recipe}=\frac{\alpha}{4s_0^2}\left(\frac1{l_6}-\frac1{u_7}\right).
$$

The response numerator pairs in Proposition 19.2 and the original source rectangle suffice for these exact fractional calculations; $u_6<l_7$ proves positivity. Rounding the first interval down and the second up is essential. Explicitly

$$
394256130000<394256134925\le c_{-,\rm recipe},\qquad
c_{+,\rm recipe}\le657236404565<657236410000.
$$

The factor $\alpha/(4s_0^2)$ contains both the original HALF factor and the factor from twice integrating the curvature; it is not replaced by $\alpha/(2s_0^2)$. $\square$

**Proposition 22.2 (strict comparisons at the selected mathematical width).** Put $d_0=a_s\varepsilon_0$. Its outward interval is

$$
1.4949062300940\cdot10^{-152}\le d_0\le
1.4949062300941\cdot10^{-152}.
$$

For every $0<d<d_0$ all eight defining $d_*$ gates hold. In addition the frozen-Jacobian map satisfies its contraction and self-mapping bounds and both candidate solutions lie in its uniqueness ball.

Proof. The selected-width upper endpoint is strictly below $1.84384149527\cdot10^{-152}$, the lower bound on $d_*$. For transparency, conservative outward comparisons obtained directly from the preceding tables are

$$
\begin{gathered}
\beta_BL_BR_f\le\tfrac12,\qquad
\beta_Bd_0<4.00\cdot10^{-140}<R_f/2,\\
D_{\rm loc}d_0<7.320\cdot10^{-77}<9.02772587376\cdot10^{-77}\le R_x,\\
C_{\rm joint}D_{\rm loc}d_0<8.402\cdot10^{-64}<R_f/2,\\
C_{\rm br}d_0<1.094\cdot10^{-130}<R_f/2,\qquad
A_wd_0<1.851\cdot10^{-111}<p_*/2.
\end{gathered}
$$

The first inequality follows from the exact choice $R_f=1/(2\beta_BL_B)$; the others follow by multiplying the upper endpoints, and $R_f/2\ge8.2003997173\cdot10^{-21}$. The $k_e/2$ gate keeps $\kappa>0$. Branch derivative windows and the inherited boxes give positive old weights, occupied-height/report signs, and physical seven $p_4>0$ on the strict left side. The positive $c_e$, $\sigma$, $m_\mu$, $1-q_b$, $l_b,u_b$, source fractions and capacity/chart denominators have all been excluded from zero before use. The $R_x$ gate supplies full-column LICQ and positive active multipliers; the two joint-placement gates and $\beta_Bd\le R_f/2$ supply, separately, uniqueness-ball placement and self-mapping. None of these conclusions is inferred from a small residual alone. $\square$

**Theorem 22.3 (evaluated original HALF loss and same-strength short-alphabet optimum).** Under $\mathsf H_{\rm root}$, $\mathsf H_{\rm original}$, $\mathsf H_{\rm sections}$ and $\mathsf H_{\rm contacts}$, for exactly $t=1000$, $A=\log1001$ and

$$
s_e-2\cdot10^{-153}<s<s_e,\qquad
s_e=\frac{k_e}{\sqrt\alpha/s_0},
$$

every global maximizing fractional law represented by at most six supported atoms, with all eight original moments and $K\ge a_ss$, equals the endpoint six branch at its own target strength, up to permutation. Its contrast is active. In the original full-complex multi-Kraus comparison class,

$$
\begin{gathered}
\mathcal T_A^{\rm full}(s)=V_7(s),\\
\mathcal T_A^{(\le7\ {\rm TOTAL})}(s)
=\mathcal T_A^{(\le6\ {\rm supported\ nonzero\ low})}(s)=V_6(s),\\
394256130000\,(s-s_e)^2
\le\mathcal T_A^{\rm full}(s)-\mathcal T_A^{(\le7\ {\rm TOTAL})}(s)
\le657236410000\,(s-s_e)^2.
\end{gathered}
$$

Proof. Proposition 22.2 puts $d=a_s(s_e-s)$ strictly inside every gate of the already proved Theorem 14.2, with the conservative rational majorants justified in Proposition 19.3. Apply that theorem; Proposition 22.1 weakens its loss constants in the correct directions. This instantiates the five-part sufficiency result rather than adding another symbolic sufficiency proof.

The short-alphabet transfer is the original compulsory-high-label sandwich of Theorem 14.2: at most seven TOTAL permits at most six supported nonzero low labels, while the common six-law constructor has those six low fibres and one counted high fibre, including its supported-zero complementary subspace in that same high label. The full left-side branch has seven supported low labels plus one high label. Hidden terminal Kraus multiplicity and saturated failure-line groups supply no additional or free actual labels. Both $V_6,V_7$ are evaluated at this same $s$, using their separate inverse multipliers. Uniqueness here is of the fractional coefficient law, not of every full instrument, time law or physical implementation. $\square$

## 23. Exhaustion of finite inputs and retained mathematical boundaries

**Definition 23.1 (correspondence with every item of Definition 15.2).** Items 1 and 2 remain the explicit hypotheses $\mathsf H_{\rm root}$, $\mathsf H_{\rm original}$, $\mathsf H_{\rm sections}$ and $\mathsf H_{\rm contacts}$; none is recertified. Item 3 has the original normalized whole-circle bounds, denominator bounds, left-inverse witness and evaluated coercivity in §18. Item 4 has both separate event response solves, the full branch-box preconditioner-to-Euclidean conversion, complete derivative tensors and all inverse/localization constants in §19. Item 5 has the prescribed entire $18$-variable coordinate box, all $15$ columns of $Q_e$, its row-minor witness and all-subset implication, both inward orientations and weighted multipliers in §20. Item 6 has all $441$ off-root bordered entries specified by formulas, its rational inverse witness, the full multiplier-dependent third tensor and the contraction/self-mapping constants in §21. Item 7 has the exact event-centred conversion, all eight finite minimum members, every strict positivity/placement gate and outward HALF constants in §22. These provide a fully evaluated conditional finite certificate; no in-scope finite numerical input is replaced by an unknown neighbourhood or unspecified minimum.

**Definition 23.2 (unchanged original programme and physical scope).** Theorem 22.3 concerns only the exact selected event and its stated mathematical width at $t=1000$. The unchanged through-2027 programme of Definition 15.4 remains open at its full scope: all budgets and feasible contrasts, the separate strong branch, all actual counts and coefficient orientations/failure allocations/live decompositions, selected roots and positive common weights, universal necessity, complete ordering, connected coverage, degeneracies, gluing, and a common original attainer at every requested point. Universal or dense seven-original-fractional-low and universal eight-low questions, higher-count seeds with matching necessity, actual affine coexistence and sharp strong counts remain unresolved; the supplier-scope maximum minimum TOTAL bound remains $\{8,9,10\}$.

No connection to multiplier ranges below $1/4$, across $(23/5,190.449003333)$, or to a later event or transverse-budget atlas follows. All remaining original $K(s)$, source-coefficient evaluations, physical orientations, coefficient gluing, transition-root isolation/multiplicities, height/report sign intervals and next terms, critical five-label/static-contact interpolation, floor/rising/strong/degenerate thresholds and uniform JOINT limits retain their original obligations. Finite prescribed-product statements do not imply an unbounded uniform or infinite-product limit.

The original experiment still has one unknown specimen, all twelve histories, the original five separately labelled Borel failure components, HALF full stopped-cq error, actual-label TV, independent minimax and sharp worst-history JOINT requirements, the supported unaveraged face, arbitrary complex multi-Kraus competitors and admitted time laws. There is no LOSR, PPT, diamond, entropy, marginal-prior, postselection or endpoint-splitting replacement. Whole-fibre activity, live coherences, conditional passive references, FIRST at $6+a$, no copies/retries, and one common coherent high completion remain compulsory.

The source-root/rank/TP, minimax, JOINT, unaveraged face, full-class reduction, event existence/isolation and preconditioner-defect antecedents remain as named. Source-final approval, actual quantum access and calibration, coherent storage and accounting of all accessible shares, acquisition duration, whole-fibre actuation, absolute FIRST alignment, archive/source/epoch/controller interfaces, native permissions and the original quantum-native interpretation require their own bridges. The evaluated conditional finite theorem is distinct from actual physical realization and from completion of that programme. It supplies neither Lean/kernel evidence, empirical certification nor source-final approval.

## 24. Exact finite rational matrix and response witnesses

**Definition 24.1 (numerators, index order and verification expressions).** Every row below is an ordered integer tuple, divided entrywise by the single denominator $10^{30}$. No omitted entries or symmetry completions are intended. The candidates' signs and large entries are part of the witness. A candidate is not asserted to equal an inverse; its role is exclusively the finite residual comparison of Proposition 17.2.

$R_A$ has shape $7\times7$ and preconditions the moment minor with rows $(0,1,2,3,4,5,7)$ and columns $0,\ldots,6$. $R_Q$ has shape $15\times15$ and preconditions the row-selected $Q_e$ of Proposition 20.1 in its full column order. $R_B$ has shape $21\times21$ and preconditions the off-root expression matrix of Definition 21.1, in order $(p_O,\phi_O,Y_0,\ldots,Y_7,\lambda)$. $R_6,R_7$ have shapes $21\times21$, $22\times22$ and the exact distinct variable/equation orders in Definition 19.1. Their trial-vector orders agree with their columns as solution coordinates. This fixes every product $R\mathbf C$ and $R(\mathbf Cv^0+\mathbf f)$ without a hidden permutation.

**Definition 24.2 ($R_A$ numerator rows).**

| Row | Complete ordered numerator tuple |
| --- | --- |
| $0$ | `(31737910926053939448391921664429,266527118770831506733466896224,787376107689580961099874288897,-34933164258995628976654594075686,846410818370904913849263560264,-72258513359967424349667716127504,-3201502673099777140977057184798)` |
| $1$ | `(12667435304939248299981780811336,-261872145663266837273537843487,792242693678294748423085495267,-13776252225892100358750964769662,-835193634964695482558436225455,-27384385268640230905661505665463,3198919726327857923334436221955)` |
| $2$ | `(-32320877543483270686331715610720,-266829574367123818456246257038,-786438849907547734651584918493,36134782633671476764514594815536,830310823373975921036818163485,70840917110803255864900265584635,-10110737920594132551540296760882)` |
| $3$ | `(-11930404478798956880373005032933,262088209363097392047098008383,-792938713659840044155497083609,13513126548348493658907890206576,-841729809500782155989362900588,22855785500493348520675273043002,10113780379898176978551667568096)` |
| $4$ | `(-23062945391123617987340004690733,-2355322485288158529825713946,6576922594148671118772383676,25586345969529642830712368166797,-5501794784935423615815449607,54271434100572793600706696305976,-962098767964990364128852906)` |
| $5$ | `(23683309192102894617118796210412,2418677654574891657636269977,-6753833419286508111553198161,-26274586026020314908803683282133,5649786043948859434519719411,-51762908528429899493198000831034,8240297346822244292722621262160)` |
| $6$ | `(225571990309763188552226648205,23036727175023821408639883,-64326975350093723096967580,-250252640641569009925611061432,53811461583367843013132485,3437670445168156762244987690385,-8239794760586404511727242253629)` |

**Definition 24.3 ($R_Q$ numerator rows).**

| Row | Complete ordered numerator tuple |
| --- | --- |
| $0$ | `(10617417280624238269989441816204239,-10595129149144259376897614651683837,13567408186798587944027291109672339,-13588696318278566837119118274192742,-1,0,-33227631929810584178894481943378743,-33221296066878815504487613704783717,-1,0,0,0,0,0,0)` |
| $1$ | `(263181593231302675051490368810,-263243888681272844037763457790,-263403276441957458132880529885,263465571891927627119153618864,-1,0,326160692721109788519433653,-244788039570568978963547586,-1,0,0,0,0,0,0)` |
| $2$ | `(796700837009544257670890829019,796090266025145610643936889572,-796028306236249653754269955818,-796762796798440214560557762775,0,0,-856923559838360430732861789,737354986634136827649660933,-1,0,0,0,0,0,0)` |
| $3$ | `(11782424769356480990555279778890230,-11753180278351515810513678272072178,15050408209722845077333719201113199,-15079652700727810257375320707931253,-1,0,-36872698549742145646670560757856234,-36853263923092319433208050852767719,-1,0,0,0,0,0,0)` |
| $4$ | `(838667517963498118101598471818,-838469234035542902893842580925,838405667909181510737093979716,-838603951837136725944849870612,-1,0,538089872703714690024311252,-795508224375646067697804850,-1,0,0,0,0,0,0)` |
| $5$ | `(-15260108761325032819074531274828648,15260954451673886261938452310906510,-19542829951313798383740025558979578,19527878573479285446476063553373682,8679765427246597952822488826128,5425922058412896447218480701904,47777103849637085839183670411785935,47814559487156959075258701126938016,118043887196259474007677680544424,0,0,0,0,0,0)` |
| $6$ | `(20617422218029986831369862895329822,-20612302728214788823176740208012914,26391622859468864946712171811153062,-26387016664663306540556301254661345,-7427915049651571289349052929451,-2297769571104843059644190879177,-64542574373399897341531980584003018,-64584758857031424171245347947167468,-186105735967664851377690178414896,0,0,0,0,0,0)` |
| $7$ | `(-3202345963753570238553901539149,3199954881251681681737504021237,-10111248281214620555106107281036,10113639370922785985791151160045,8239687264277741035829893390168,-8239687271484017909698539751269,-510831541898454103460080924,2580798573502793466306173758,9468136193901153018922175018,0,0,0,0,0,0)` |
| $8$ | `(22369262737844748173293771101347462,-22318548388285903951887748421708764,28579101987994138728456002097077649,-28629816337552982949862024776716349,-1,0,-70005499296629136359587860554548826,-69980374408617582283092302968804534,-1,0,0,0,0,0,0)` |
| $9$ | `(162610035973320589199944739214764,-162342973822020210283592650573497,207627715707536270972285991948661,-208155899958917464080953825762610,217164704993389189317744015228,43957395087425002998001157451,-508924283859283965110738355900520,-508952191399386043832166333531484,-2431857102566397349588408640942,-1000000000000000000000000000000,0,0,0,0,0)` |
| $10$ | `(162237836268356337374275800326474,-161971043205009021446888290762153,207327038323389381498928682539848,-207854840478636545719124062229702,-23120003524680368827681626624,284129095424528661635551752153,-507467006329608653803249696484754,-507494351553447194964046878375416,-2426981621616476435085742042049,0,-1000000000000000000000000000000,0,0,0,0)` |
| $11$ | `(111468955908830372839997561206529,-111285872255174838820867565327823,142328479949601884099628446285713,-142690581693457602393983292960890,148886805450401523991770948309,30131284749782751233079848159,-348866895289297423460725122028434,-348886008502894116397090337322221,-1667089643982155665909104097319,0,0,-1000000000000000000000000000000,0,0,0)` |
| $12$ | `(111457139865604513249802074361006,-111274177781497778092529176278620,142433757988882622662907562550091,-142795549605551599841495371849702,-15809066016012189317427862947,194638598578254210632339080168,-348629788230386976626106556690716,-348649010532916619193656957585340,-1665954757266869827843466621871,0,0,0,-1000000000000000000000000000000,0,0)` |
| $13$ | `(12181990110364060190269906034774,-12204815525997882668205104454034,15659593535866016050239964254691,-15592495925693648415206821071193,-44272194538545157097944764240,0,-38139477130422517307783856943329,-38199159448722345893071411821400,0,0,0,0,0,-1000000000000000000000000000000,0)` |
| $14$ | `(12170073828324115115165652344223,-12192910044589068008050708862382,15612034546801596376528371007470,-15544924733303475564747436298383,0,-44273597233167918895878190930,-38156041173437028966490655503170,-38215716718365856484799943262243,0,0,0,0,0,0,-1000000000000000000000000000000)` |

**Definition 24.4 ($R_B$ numerator rows).**

| Row | Complete ordered numerator tuple |
| --- | --- |
| $0$ | `(45547641937174628809218981056,2081174387758645567851094349,-1317898621474605896362395648,-46310924196114618558287524470,-117595090173993310647985839,117601582829943388227830549,-63602549764055151499609803384,-5377011934414854619808138716,4945222997005969802662910241,-80053546321711251209749222772,-4265172726708610677973810902,-4265293727403057174220913977,-1639688472817418709180259381048945,263285422943909710999807660425,796430765543607944300166872845,-1818925607202547311843994953780293,838827502999242742340826528865,2368355021244300019029967813018897,-3197473763153421117505505215767438,-3202207570841814883326784345800,-3454229909648427036613827247830292)` |
| $1$ | `(2081174387758645567851094349,20473584032223268455060361642,-16864387929716046568813776504,-5690370761034715854408484348,-4904169786412663487646227,4904440555261063798451085,-23815882955046475014658727703,3798157244477182754387692082,64369834737864379364947663614,24174658987923735120382338816,-177874188362853975057095342,-177879234559501823644959370,-14147928069380471648755087699393627,-263197369813268254616739197689,795966124861799459548887841839,-15695973755531748389568195882501513,-838384499579546274208855900304,20368600601760014906967679753168907,-27512473253284624508098313332585455,3199847108414001650379196382165,-29803988348802782852393903393168794)` |
| $2$ | `(-1317898621474605896362395648,-16864387929716046568813776504,13909783813109971330631051134,4272504605768701599927075550,33827595805517665715311904,-33829463493538131097266439,18956086999530394649938178882,-3305455492296830811731483388,-53070762379066534514771405072,-20668799185227138024147258386,1226926556426288973830137871,1226961363683784731443744292,16344861158563530955494808003224866,-263440673979214110769259850409,-795928378902667476901496332393,18132767574830280158811584690975048,838337017894780200218706322718,-23536479026565839104752242469764598,31787025559428573817647595244930176,-10111219037369131469665054168343,34430976374562282864445640414151794)` |
| $3$ | `(-46310924196114618558287524470,-5690370761034715854408484348,4272504605768701599927075550,47728795247312863530189604793,88675204197458806884040004,-88680100129689524304711533,68462340298699050889389711169,4884296492342107423334602135,-16244299915515421070409562300,76547694037874573166642694840,3216248755953266835208520437,3216339999229429144832679034,-556248021727227797025710131509090,263352620840027628747990288853,-796468511473362275271256938435,-617871990113338052965049893719750,-838780021357369363513335938736,785422526816845645339515877992313,-1067359336509362910288840696539000,10113579500026846597057406771603,-1172765289817296383172490383196885)` |
| $4$ | `(-117595090173993310647985839,-4904169786412663487646227,33827595805517665715311904,88675204197458806884040004,64117308617372171372611444,-64120848659942669836331288,-98182925114925104526885263,-247951553735555921263110578,-82585570781348903949060235,136181713151782167106621998,2325534132591312969823977106,2325600106764701189400315698,-61677964457209418455839452337699,-154767643348071770876622,532088505002880167759220,-68427511759601787959246099361219,-776873192456504737695697,95811984323439974566989666824547,-124760084694317702550385831610065,8239560908060639598412363701711,-129930283802161052271558840579005)` |
| $5$ | `(117601582829943388227830549,4904440555261063798451085,-33829463493538131097266439,-88680100129689524304711533,-64120848659942669836331288,64124388897965873212027623,98188345987106079467526296,247965243627951175080438462,82590130492955321519453749,-136189232011701220235174500,-2325662529899404125831729172,-2325728507715356067810865680,61681369818796617922088661064492,154776188373709971975438,-532117882654556469203080,68431289776955383524902138387724,776916085151667396683151,-81711107578761441151910641240070,115040878213152420795449831571779,-8239560908290541492857128341339,129937457508384460006139450623179)` |
| $6$ | `(-63602549764055151499609803384,-23815882955046475014658727703,18956086999530394649938178882,68462340298699050889389711169,-98182925114925104526885263,98188345987106079467526296,111344153021823414967531592912,4434203149970335969942273510,-72428925287936328476062025000,83520393124690139470927174214,-3561093697101179637734868021,-3561194723445937028258674659,-12658349675848480436530480406767194,137848531551862076481363004,-364413876073633937812436008,-14047264258435681860156333250297611,236745185613597482312592784,18202458971309009741724163802821346,-24590644947474897340594675407735053,-69884644351095662819723855,-26669472243180240768418612537349374)` |
| $7$ | `(-5377011934414854619808138716,3798157244477182754387692082,-3305455492296830811731483388,4884296492342107423334602135,-247951553735555921263110578,247965243627951175080438462,4434203149970335969942273510,2512312475310301848204893251,12437349346413509266602059849,15265516550052162957276702274,-8993200336622566048692116654,-8993455468959695929515919432,-31985416659865956585958429817647476,-249216861725808053582188912,747719589448895583440206084,-35481976069585012035597513489316441,-797530350674378832493771234,46043138856111144905030724847059313,-62193251568851927602300720756846215,3058979138510143029177213173,-67376725863521429269249035147012753)` |
| $8$ | `(4945222997005969802662910241,64369834737864379364947663614,-53070762379066534514771405072,-16244299915515421070409562300,-82585570781348903949060235,82590130492955321519453749,-72428925287936328476062025000,12437349346413509266602059849,202517531147805704986375533484,78994134172865848957052893746,-2995377813776894676939175669,-2995462791061244032069724858,-10646639469017839283196352639315697,142638556219473900210101616,-381048427635799928175214422,-11815402836030193829525615695461610,261481470861871724113807314,15307481600590987488044734135515007,-20680063658903927190976140181995999,-203340717950146835549522903,-22431615034947584618417656010267964)` |
| $9$ | `(-80053546321711251209749222772,24174658987923735120382338816,-20668799185227138024147258386,76547694037874573166642694840,136181713151782167106621998,-136189232011701220235174500,83520393124690139470927174214,15265516550052162957276702274,78994134172865848957052893746,178792671017760953506454515001,4939309353409481865324307640,4939449479003483266891296908,17559362942715520906609987942617768,-125559199336207097581919078,322157738447819125298213106,19484605739746622168160159738123904,-175034153716497996397380146,-25255375503618129500417121613933033,34117827187081795977868644894731472,-258602101669192033604897128,36993905958999463420984951839428478)` |
| $10$ | `(-4265172726708610677973810902,-177874188362853975057095342,1226926556426288973830137871,3216248755953266835208520437,2325534132591312969823977106,-2325662529899404125831729172,-3561093697101179637734868021,-8993200336622566048692116654,-2995377813776894676939175669,4939309353409481865324307640,84347099378746196268120858035,84349492261345174113072070845,-2237059144668024346782626653008345,-5613420852932408727716617,19298844674344590090237848,-2481865156799984973106718442129012,-28177182803073599990233298,3278328581938023260520425394215732,-4441742337746919592814925718508400,4885197482482824801192438137,-4712570074367315995954405732056266)` |
| $11$ | `(-4265293727403057174220913977,-177879234559501823644959370,1226961363683784731443744292,3216339999229429144832679034,2325600106764701189400315698,-2325728507715356067810865680,-3561194723445937028258674659,-8993455468959695929515919432,-2995462791061244032069724858,4939449479003483266891296908,84349492261345174113072070845,84351885211828965717650641363,-2237122608852798781743976777301557,-5613580102713120285853949,19299392172361021605367060,-2481935566001847966489977460741583,-28177982174847073000557770,3160374350347108397802856623728531,-4255757331938880559730527627083400,-4583068726965697451743930078,-4712703767487891269305253791023379)` |
| $12$ | `(-1639688472817418709180259381048945,-14147928069380471648755087699393627,16344861158563530955494808003224866,-556248021727227797025710131509090,-61677964457209418455839452337699,61681369818796617922088661064492,-12658349675848480436530480406767194,-31985416659865956585958429817647476,-10646639469017839283196352639315697,17559362942715520906609987942617768,-2237059144668024346782626653008345,-2237122608852798781743976777301557,-7955110456620175263455912389069398167009,-19977224352033607459782998090565,68671297062725550971309542076959,-8825654319716933921708619893973743834187,-100236064248596273742696254116770,11447988177119528919524817445901853740763,-15464108507823830104139246024214097936560,533346240607979351206104155681649,-16758168797922170749549415914850161026336)` |
| $13$ | `(263285422943909710999807660425,-263197369813268254616739197689,-263440673979214110769259850409,263352620840027628747990288853,-154767643348071770876622,154776188373709971975438,137848531551862076481363004,-249216861725808053582188912,142638556219473900210101616,-125559199336207097581919078,-5613420852932408727716617,-5613580102713120285853949,-19977224352033607459782998090565,-567979232660352872973120,1618361567371063510977033,-22152121955114627253739562681268,-1461238409145143135327955,28790926550624112392111465354010,-38883572207094091529863097486034,4143233301829832865705467,-42073171468252157278469454686421)` |
| $14$ | `(796430765543607944300166872845,795966124861799459548887841839,-795928378902667476901496332393,-796468511473362275271256938435,532088505002880167759220,-532117882654556469203080,-364413876073633937812436008,747719589448895583440206084,-381048427635799928175214422,322157738447819125298213106,19298844674344590090237848,19299392172361021605367060,68671297062725550971309542076959,1618361567371063510977033,-4630285038812231476427621,76154720818264690630830084275245,4242679504768166752033652,-98940970652028134921199609811742,133629595524736435106733552712399,-12433420281337608270703234,144632550835818272117627043889090)` |
| $15$ | `(-1818925607202547311843994953780293,-15695973755531748389568195882501513,18132767574830280158811584690975048,-617871990113338052965049893719750,-68427511759601787959246099361219,68431289776955383524902138387724,-14047264258435681860156333250297611,-35481976069585012035597513489316441,-11815402836030193829525615695461610,19484605739746622168160159738123904,-2481865156799984973106718442129012,-2481935566001847966489977460741583,-8825654319716933921708619893973743834187,-22152121955114627253739562681268,76154720818264690630830084275245,-9791463806876637404835150511657307882311,-111178820536123668662730649725706,12700763811979961176381694119031154472450,-17156376175408226201875681378801229165577,591650480830159122694784195290837,-18592049412089688134883309652620314311377)` |
| $16$ | `(838827502999242742340826528865,-838384499579546274208855900304,838337017894780200218706322718,-838780021357369363513335938736,-776873192456504737695697,776916085151667396683151,236745185613597482312592784,-797530350674378832493771234,261481470861871724113807314,-175034153716497996397380146,-28177182803073599990233298,-28177982174847073000557770,-100236064248596273742696254116770,-1461238409145143135327955,4242679504768166752033652,-111178820536123668662730649725706,-4088234710022616455677276,144345708417851115344475080478556,-194966456789738306992829402811680,13269647837976404310935425,-211131500213082471695391338770117)` |
| $17$ | `(2368355021244300019029967813018897,20368600601760014906967679753168907,-23536479026565839104752242469764598,785422526816845645339515877992313,95811984323439974566989666824547,-81711107578761441151910641240070,18202458971309009741724163802821346,46043138856111144905030724847059313,15307481600590987488044734135515007,-25255375503618129500417121613933033,3278328581938023260520425394215732,3160374350347108397802856623728531,11447988177119528919524817445901853740763,28790926550624112392111465354010,-98940970652028134921199609811742,12700763811979961176381694119031154472450,144345708417851115344475080478556,-16474540176346220708179009541281391437740,22254056502568283886044952617022468995877,-771041241424383159530779443112046,24116234763115798935610404959408732092851)` |
| $18$ | `(-3197473763153421117505505215767438,-27512473253284624508098313332585455,31787025559428573817647595244930176,-1067359336509362910288840696539000,-124760084694317702550385831610065,115040878213152420795449831571779,-24590644947474897340594675407735053,-62193251568851927602300720756846215,-20680063658903927190976140181995999,34117827187081795977868644894731472,-4441742337746919592814925718508400,-4255757331938880559730527627083400,-15464108507823830104139246024214097936560,-38883572207094091529863097486034,133629595524736435106733552712399,-17156376175408226201875681378801229165577,-194966456789738306992829402811680,22254056502568283886044952617022468995877,-30061116231107848097961041048552444345776,1042234736635659089180132318654501,-32576559934253758734209138101864831975907)` |
| $19$ | `(-3202207570841814883326784345800,3199847108414001650379196382165,-10111219037369131469665054168343,10113579500026846597057406771603,8239560908060639598412363701711,-8239560908290541492857128341339,-69884644351095662819723855,3058979138510143029177213173,-203340717950146835549522903,-258602101669192033604897128,4885197482482824801192438137,-4583068726965697451743930078,533346240607979351206104155681649,4143233301829832865705467,-12433420281337608270703234,591650480830159122694784195290837,13269647837976404310935425,-771041241424383159530779443112046,1042234736635659089180132318654501,-314677873750197844916334618,1123484867842316095845728650955639)` |
| $20$ | `(-3454229909648427036613827247830292,-29803988348802782852393903393168794,34430976374562282864445640414151794,-1172765289817296383172490383196885,-129930283802161052271558840579005,129937457508384460006139450623179,-26669472243180240768418612537349374,-67376725863521429269249035147012753,-22431615034947584618417656010267964,36993905958999463420984951839428478,-4712570074367315995954405732056266,-4712703767487891269305253791023379,-16758168797922170749549415914850161026336,-42073171468252157278469454686421,144632550835818272117627043889090,-18592049412089688134883309652620314311377,-211131500213082471695391338770117,24116234763115798935610404959408732092851,-32576559934253758734209138101864831975907,1123484867842316095845728650955639,-35302617700138686390346992005382113250832)` |

**Definition 24.5 ($R_6$ numerator rows).**

| Row | Complete ordered numerator tuple |
| --- | --- |
| $0$ | `(852046108493326468179215951693,87015917689723715146612120,-242980296192480025796496650,-945271566323537841948467817926,203260370986150035025184700,-8323144188802964238483938759518,9961027153314440121154473688013,-471223486587275057542190671,-35308039195988488795249418022,1717701231137023298073338648,-1823311049756509151699165228,35413842776654133491945555870,387083295001659246938520,261108567475575838620439,8891114729805665903443810853,3739268046377961468012716053,-2571975946674959146020901539,2573520160475516471984914016,-133184654794705456822566,-94942420972681885667974,-1)` |
| $1$ | `(-848526116399082662892753474249,-86656435568641301707629121,241976490514443475262906846,941366439115978542303518345446,-202420657158679493955623325,8288759427870666439259051450884,-9919875933350280951267285132343,469276757494946597504125413,-1756900487566239527791091151,35142446600682374083370048893,-35247807332999175932918743216,1862750769131701581569293106,-385484167765893748402450,-260029869874481694474250,3741853733064226224853742013,8860225852481132499096542046,2561350541654460783997418076,-2562888375964148307413168075,132634439345941834654934,94550192702520347761585,0)` |
| $2$ | `(850740249910233111147518022832,86882555795516130972247560,-242607900963932366309869640,-943822829012337081282168293447,202948851107813447422447752,-8310388013792093830732556658079,9945760734425932831657256404920,-470501282438483982826759957,5835301313080072917521022431,42942142334829554597967553036,-42836509060527068455260918921,-5940771613932639984814158859,386490045366326942918478,260708388587886144678152,-3751617679729014896518069117,3733537188359627316940273014,10048706118971158551362855277,2569575945066489615785691884,-132980534004919167745965,-94796910801235793724122,-1)` |
| $3$ | `(-852114737940298115224304905343,-87022926529091969677493590,242999867437728929494382245,945347704767441450359122283149,-203276742925077962830026544,8323814590060653098921789748415,-9961829480533574276785807558240,471261442053490052083392001,-43138060058614359737074934323,-5790343267995351085877777569,5895869544443748096416726720,43032265012713290977794752528,-387114473258567082874115,-261129598892076402463104,3757678934729835505472034936,-3739569231836757188245690959,2572183110682969005187449460,10074763571653805504970864786,133195382370493383734193,94950068265217528410351,0)` |
| $4$ | `(16106718478324909175023008,1644912024584934391770,-4593196527207577108380,-17869013017688943904155006,3842347897184769598218,32863009540863165225784658613751,-51811252372176849355820515623671,2635900050754679120536010092,-2011820932281277236396438239,2009790426552265829184004861,-1781880111512169707322296368,1783844775033307605120990708,-36874862469132283511343191699,-24874084310801202815053760483,-71027848761214359232429,70685538185845159145285,-48619543112954936743543,48648734276095042589341,12687620189170321567437270349,9044535791292925566818212077,0)` |
| $5$ | `(18030985303016791611985328,1841429374950564658315,-5141944908728597483033,-20003820861148700780145361,4301392524892586194192,-36771309747983284486550945611202,57972877115149303404084550842858,-2949371513127665773217127786,-2252172825338774025930510455,2249899735447324969471147526,-1994761015141009629932485042,1996960396667587029870246670,-41280295804911710873436470210,-27845786790004246107081367604,-79513533364466424201720,79130327004843556193810,-54428111380279973939230,54460790006547982919118,14203407942409209592717368129,10125084892051364978197304728,-1)` |
| $6$ | `(36048021509943837188540671647,263289539647337027453362964394,796416613786158981317905755318,237314550118109105357347710908,838848161431688167136518288127,8671098243584825326199805766815,-9978472176404786490979663527859,-3202317499659742826751973587751,48643164602348311224780740188,4847856601001433820573816955,-4858014265498196201475711044,-48632949731764029245353518204,2965463753633933496995606413,2000365302792984723100004180,-8039877402393800442514359866,160131736403969032023972949,645240621265089689268133078,-7553702059021311430510176641,-1020334050665384349197886375,-727358456725794505794873475,0)` |
| $7$ | `(38855989501233321118713725256,-263161849832203733080419955383,795844019841243110843040908883,234065796748832807058595688486,-838206253285578355735874203929,8637892986941072046386632516758,-9940127511338068487873588050756,3198898614163641936120247830451,4855560762670766251502406285,48377107349191188601437773111,-48366576503004060389284955328,-4865677762926705949291851432,-2962824901748349085690799654,-1998585254817465102051348941,-171409620337904917723543352,7993805253866343648527549465,7528414137520096368985644498,-637095905470622781715112505,1019426094724184636930455469,726711208472405951254074846,0)` |
| $8$ | `(460897278704854668154072282564,-263481708340607107613067192397,-795787317410199138669002933750,-233765176294833459805812881884,838131099349093035040766410201,-15687553672436877729723772752592,14799063703384964983871077995711,-10110123291969443869468513107970,-3869018668607102541708067452,-49350058694647550218691485306,49372615902491285642667286853,3845981142306389805390310030,2626532240009771729484501671,1771737709875666643320540205,-929951006267470289790420783,-9092236579127431092286067057,-6773016748962894119955832804,1391309916455581269496465661,-903717091928150550254215929,-644226534312879486882794945,-1)` |
| $9$ | `(464198710328013953825102113788,263354018525478311452079826114,-796473316217215514146388770020,-237615170620973441612801436593,-838773007495192339073848866611,-15727214868070523384667590222337,14845362220259848208332922722382,10113542177467147709214578978494,-49629712197980955490514172881,-3874899759528756476702134243,3851969993243126024253062384,49652651230524801618449303153,-2629271930690831045858243786,-1773585779059469877274145530,9141238028804941360469952002,938299589050416611398955765,-1400638009955247991168776277,6799488048169388822384962288,904659743709596175405450345,644898515949222001158425482,-1)` |
| $10$ | `(797757888973710507567604,81471688106193430941,-227498777613674172104,-885043475629047715922280,190309612183616146926,7052865845977372972664970941116,-4862979230122287782938373787299,8239556773106428381036502238262,-99644506861508610061700296,99543936905803167749916376,-88255650465185544744354136,88352959288536235563418915,-1826393903833243902890623713,-1232001230830637474659041780,-3517974611795864280853,3501020136410490216003,-2408102192190983502288,2409548016224890619815,628411622878590961995534286,447971434362550891566324020,0)` |
| $11$ | `(-797801934753996936360861,-81476186318149073672,227511338268119211670,885092340618050386841359,-190320119551177774716,7052911464004130769139953750237,-4862847005779670430412375352183,-8239556773108031330150842351488,99650008430489166000794153,-99549432922118894367886895,88260523233030468584671268,-88357837428992464757662464,1826494742628718807959559066,1232069252038921087563991863,3518168846085422652849,-3501213434610154627127,2408235148243854333790,-2409681052104546758621,-628446318718836874879337798,-447996167745504851301155930,0)` |
| $12$ | `(-49650299264036577447663589032028,-5070578118911032429307434092,14158910299530310647076096486,55082718747157859940568807944364,-11844356951323944080659708613,485004972938070554971756661390789,-580447436129719668677541040190090,27459062245672097614346970186,-103220858564784832339278869988,-100106849878781590241853422921,343782225733266107130624378215,346895711747395970942622435972,-22556057994239714407182003,-15215278124432356028910139,218949251011046572341220485823,-217894050193375554745443267876,149873785208791539390248119798,-149963769396925328677830044547,7760915638271849094637297,5532470094231666171317617,0)` |
| $13$ | `(-5070578118911032429307434092,-517837008861747894628146,1445990493846332411297083,5625368478126710224502167914,-1209614807567874293195336,49531536361234816478283855023,-59278677318048508118976402347,2804279576408766299459585,250133404443311927025965666697,-249999163912441223483449819771,-250337818565694087165053561974,250203578630710033461109032477,-2303556188176370787722,-1553872936809768364535,22360374414353783916218819,-22252611152974708454877854,15305985001958002812867885,-15315174712033520105029100,792589966253031933874,565008111112441362995,0)` |
| $14$ | `(14158910299530310647076096486,1445990493846332411297083,-4037734793984540466138308,-15708088075114209054677020391,3377687347614583653878464,-138310181578912944728713563560,165527767275835837931285217910,-7830575142722349044165011,756702685181592740867386822213,756034684059916477730442109499,-756033287293857235703537179977,-756704083996101810831240392699,6432372142473143360864,4338982067370702815280,-62438350849181112387199313,62137436374407404610829959,-42739913202485480581617229,42765574237102551680279050,-2213201329968768859465,-1577709479302172083978,-1)` |
| $15$ | `(55082718747157859940568807944364,5625368478126710224502167914,-15708088075114209054677020391,-61109518966710507060214051629181,13140291042783115101955415066,-538071127693514806526233568891636,643956297258435590921661278051872,-30463457927928890988139725804,377979580612102330313192457991,374354830777100277907666716968,-117692482665193862708255768988,-121317979563269397460622229545,25023998182448750179984314,16880036938567959854941990,-242905283394294712681542117908,241734629224569609044385820157,-166272020120682797596807002389,166371849805501134073022685359,-8610065591950919368891165,-6137797731228601546921646,-1)` |
| $16$ | `(-11844356951323944080659708613,-1209614807567874293195336,3377687347614583653878464,13140291042783115101955415066,-2825537683958973450012330,115700652519665854592899771883,-138468986630681295470933643519,6550513080631964077073896,796944265654034299658173332924,-796269426548209935781771710377,796267575276429492263123616943,-796942411391959469986545514378,-5380873957632997080613,-3629689808334822800462,52231570033622870515414916,-51979845969013308617915453,35753230815766508962211928,-35774697047793909608403947,1851409889796715008272,1319801725063704868397,0)` |
| $17$ | `(485004972938070554971756661390789,49531536361234816478283855023,-138310181578912944728713563560,-538071127693514806526233568891636,115700652519665854592899771883,-45732625970845948697784011455353428,70301820074305015189409273905098194,-3556375122613620237198908336283,9581140645942529802310158453766,9543830747178564557574451213572,-13985132751567844852672507773005,-14022855786567992902072691957600,13023980097465024550234931094658,68632633005014842348288491397553,-2138788227573516453984831251202,2128480582874394569885240120950,-1464030070649899821297600856353,1464909073986789971553118293421,15834823524703877857252508622138,-11282587617239622012902905301780,-1)` |
| $18$ | `(-580447436129719668677541040190090,-59278677318048508118976402347,165527767275835837931285217910,643956297258435590921661278051872,-138468986630681295470933643519,70301820074305015189409273905098195,-108683051200588886645605760399589835,5505040176107497449569322899321,-11087513868436604373590366905500,-11044249071840661934241256558843,12960098104838438230662874294087,13004040203527188546813801758448,47559641821743928043826447558931,-64844203616000931863439653323622,2559673018606335314767231911317,-2547336967901747264891116205283,1752131520997940846556241357584,-1753183500383134706105809095374,-24964908855568154071747801136709,17787891428344102097051197904201,0)` |
| $19$ | `(27459062245672097614346970186,2804279576408766299459585,-7830575142722349044165011,-30463457927928890988139725804,6550513080631964077073896,-3556375122613620237198908336283,5505040176107497449569322899321,-278923634248980691914112174,-3042397810760818620596950510261,3038803530926010003936757685408,-9605354953037223393786996314812,9608949216957638742525960408792,89671397095439236988417033582540,-57101380237323302618652630264415,-121089725566073541253722214,120506147513904578193119426,-82887588958071364554325369,82937354648504608994953735,1270090984228282587152964735,-904959402880081931229503980,-1)` |
| $20$ | `(-17944842609173035791144321597,-1832631980675348581794642,5117379363441399150641727,19908252982456072703159864088,-4280842702842004889557971,34150491904366278926714950024854,-53774437505107815162143958691192,2735027904123803915399373719,-18719959682485984621530968907,-9369161131883364100129919618,14970813835872028191237224411,13037101333753956809858140470,-40948759243408147301665572012,-23672532688931954824238286711,79133658951285881430303082,-78752283352853332283454868,54168082099775771781663961,-54200604604520162824361966,-13123433055385759156145220363,9350589114165146886826507028,28193169838546411847371568539)` |

**Definition 24.6 ($R_7$ numerator rows).**

| Row | Complete ordered numerator tuple |
| --- | --- |
| $0$ | `(852010611584610055331425307372,87012292538389394828875497,-242970173442891880738720947,-945232185569177797800114219523,203251902999778595492150128,-8164773925760047851760441838848,9711475317275934329063634064875,-458529008504601471591816698,-34491928120093955544097691150,2028836230488939771167357728,-2656977162998007936223244300,35120075946700412377947103702,-7483440262619015013267350130,7300121144174505253069753674,-114714566719533582505317526,8891271265046981067612988648,3739112265540298599314110879,-2571868796141097344320514043,2573412945608497379140482408,-1,-61172157740292623513617197,43395980618117690223384485)` |
| $1$ | `(-848490766135995877782286785948,-86652825393613908968384239,241966409584186663445322800,941327221052278816801980199367,-202412224155444277343210891,8131043427629161278997299992188,-9671355051483390211896418833775,456634723126346863540117334,-2569640026983417852707057362,34832596969254850724748460573,-34417585280001128187741105381,2155303982934042477487340863,7452524505479128919688932353,-7269962719109980046118155824,114240655315065822523259421,3741697844504829336519057426,8860380989753486469643772388,2561243833783300364142804465,-2562781604025605186316699796,0,60919441943005050381803914,-43216702164551549568100419)` |
| $2$ | `(850704807404608806280614961468,86878936200142852839824361,-242597793728621327169424257,-943783508613508946892637661737,202940396099604309711012932,-8152260471378072804831497701146,9696591365256026253796126924347,-457826260102391369193727824,6650161604958822147867838888,43252800484037618053888271461,-43668897484640527502446807621,-6234088212458156414931325710,-7471971030378417335717831107,7288932869550965626772317204,-114538753462406651106066016,-3751461384395946939134930158,3733381646274001357665926293,10048813105284512880884496401,2569468894518575952189126259,-1,-61078404378314646092386475,43329471290515537571648500)` |
| $3$ | `(-852079238172425149548326574411,-87019301085763907726606365,242989743872787367359994784,945308320841094155620237524293,-203268274256638715179197944,8165431570825951963553070240097,-9712257543934397693328993901271,458565941473322817400286160,-43954236869509907333416213129,-6101503328224520791604678941,6729602806685448217653210991,43326055504596662810533154629,7484043028550986783672222753,-7300709144368340593612682759,114723806591877433905595984,3757522386880133382022266192,-3739413438451472035950515483,2572075951518492253956091189,10074870795156621366690103512,0,61177084951759151234801203,-43399476018332451086462499)` |
| $4$ | `(-10312545339503600248619724926,-1053177272319902387835541,2940856481959497352440762,11440878361727086744383841423,-2460115445190619058291374,98824592266050364168838345760,-117545518989035092857733017654,5549932272424232021367877,-194194460463924323030468533491,-76267234567620200469011788671,194219876077932392794126603825,76200792349432033740771619160,1609037033067404882277591611143,-1610486568500669788328421568753,1048733593213149639139447510,45476545188465046678718309,-45257376191785993266148396,31129323046965072481656804,-31148013085770946943901434,28193169838546411847371568539,740414076579124044126444,-525255215829100362115115)` |
| $5$ | `(7397869709189242574633245401,755513598709374767600110,-2109670539204460420041701,-8207297489837127025110444022,1764803250209063995996319,-70893405418296366710056045625,84323162299111853411855068186,-3981332880927278249716125,-171726276477590126926975437383,-62692317626842719600185986269,171583234876388097287565363128,62874153527698860760574804733,1556219523652634044883710392873,-1554891745660914454898694355111,-964306942688792089473231381,-32623328679058741066551592,32466104286016371849635012,-22331118890168646686227235,22344526489106990427399035,0,25380985578061046223770867186,376800248905650201861044)` |
| $6$ | `(-8241545567501645028580367469,-841674697635741166483083,2350263868485299412268463,9143282986521742398086086330,-1966066851137746149173529,78978307831578420114679628113,-93939635571133811676807233154,4435376351221354379085568,187644135069943766239750797989,74646157278171156486465934991,-195975852067542912007391715169,-66357995243613551811142528842,-1741279732870457476185865989614,1657253871568150916435944180466,-54598831663017923413130386456,36343793611027500017078514,-36168638863712616242250431,24877828502171816288758622,-24892765145008860335026295,-1,591721650674481670836600,20244743791458864115330616934)` |
| $7$ | `(-14012789284820196919226473493,263284427145386515771546423982,796430889763143439005382544768,292852695952811319006094408986,838836219144912156470441880946,232018540609535994599875018942544,-361918055062767064716780266426965,-3184414648723848104101682664429,1199593589166422138577826969563,443637342711478876179100869426,-1180566070829090750598602201233,-462928341186262294938743520968,-10553794700090939441822429816581,10297681789426740795954982586918,-160148276217697262551540664552,-7819117866379108808345446301,-59563874331984725384986118,796353571552319007276951744,-7704905737491118873933040080,-1,-87102773148438074287782894029,60607302737105731283755786593)` |
| $8$ | `(19763918649866794443868684421,-263163799625823079086820882607,795849464378791197288224763535,255246800380131651742210052526,-838210807806003318179433450205,93817599955815008653986503982486,-144161993781422372763353872168402,3205726360120671170279035457705,443802247868385646427597927477,215721579495298613267001400907,-496755269376158661843592598483,-162868651375795343790383596801,-4024980677819693259758508761021,3923211169567952644024854255856,-63838441685704983821220770262,-87216882829384112520883751,7910018273605453118523352598,7586045228739748854020142563,-694761598384944152572767900,-1,-31810486170400704703267129828,24118375837277628620772463841)` |
| $9$ | `(512025013481088443539028276079,-263476486878157360823871924349,-795801897644784738147597749175,-290486982136968178257690806569,838143296156560033943930026179,-243795101571578650928298538929892,374239379699111729259478635155779,-10128407698471397899597714583677,-1179349142012122740813827491563,-497491271597313057872233869556,1250138019737136816424103744953,426971067552552961076236040217,10778723071850611309854535984310,-10511496542063654691002247459718,167376181712475247264652108927,-1155415492908667607727026642,-8867858692735199980793564735,-6927350302912199018223223907,1545736132237204498578384552,0,87013359064228505045754734662,-63286086310910164504159824896)` |
| $10$ | `(482211947320278719025861680361,263355858142292260757186242150,-796478453100790401234598265974,-257599301264260773806146739461,-838768710336626374148926100784,-96093680114671569346030586669407,141482766066581921841003560565887,10107100246311306533298265052777,-463772879974817108178231168161,-161763253494478584432592693142,426903605002121254551740260286,198727365614765856835047423088,3797541471708039760918444954480,-3706947320288838746307205395995,56571891677487604181230106457,9061802762427854048325423490,1017352026266655190275609922,-1455012546502084920260798890,6853895231176175380899578271,0,31879455231891356311293389937,-21424975510947468096065241449)` |
| $11$ | `(37453244485327032952388719070,3824943752294411930641534,-10680643157336137519896120,-41551139927330333215510530057,8934681225390722536681815,-167098499431003622488831323348102,263305348687752417395881129532336,-13394106935970002685494106019,-861089282361320432937388609484,-328282535579819217573737320461,879611827830214721483696735245,309957156884732610933927511209,7895873975572868110898607837834,-7702043201682424618014228946767,121312312314081785642631258624,-165162344427917023895848219,164366363441071778104435873,-113055905051354589680059877,113123783792227147234054597,0,64403004790313286453448336162,-45887831712017330856799625904)` |
| $12$ | `(-37767043646273048304147328435,-3856990752671266187588950,10770130113865335393506972,41899272993629966638987908668,-9009539772637440294420428,175554946563070605524176913444827,-270380020190419782785774472534836,8253063386844692997412363480360,868222550217467463888687125012,331139562229369829080188583874,-887088580114519189005063940631,-312472358513751959936575661198,-7962197138181591036844204893473,7764911845372264552008033877138,-123563303493452385725879769142,166546144571631184892465407,-165743494518614679241289203,114003135354967034468940499,-114071582812708439669026195,-1,-64315560636319405829283983021,46721248270480539490457488686)` |
| $13$ | `(325708994532255262226441994,33263302040236217088237,-92883316026109284904009,-361345998013652107944294097,77699704748631745382474,5596193988832233985122012577541,-2567425418836848230454714123802,-8239673539145454694604772636720,-7407082904014966964664752848,-2961423764536458647726971052,7756467750295808987717999860,2613761023758169820491804449,68833996960704556753554694448,-65317740332039936664188917436,2289635692809995010127729945,-1436320454407680728683988,1429398272619298516441661,-983181181396367601952135,983771483164439462816752,0,-66999131274962990162453888,-848033310988935937961046874)` |
| $14$ | `(-49648230793653167568630470015425,-5070366874652262558951615217,14158320428229431110632035534,55080423957920834724384178176423,-11843863506129705453329388746,475776445425035645631311831252906,-565905590075036765039458792102524,26719331579077035730540348554,-150777157158191074219192489371,-118237260516599171844621712712,392361488752165061930235010154,364014047099976056785430831585,436073875415727840101956037286,-425391532053249392639637487998,6684629518044143710500034511,218940129413636299142524058735,-217884972556458415640651797791,149867541349428168554631359673,-149957521788750150281852453753,0,3564614529844037000580626073,-2528763881517980221376617772)` |
| $15$ | `(-5070366874652262558951615217,-517815435366076340009040,1445930252748986602556503,5625134120866728895584332467,-1209564414066890896087088,48589065311291765208029978414,-57793579191623778441544818282,2728733966663745655317344,250128547716753608177949471535,-250001015495711207495734065163,-250332857368042759520546041269,250205326854949516462247755327,44534407318534228647765445,-43443464115464518843098563,682673350808435221370274,22359442863629545914030491,-22251684091752404708563875,15305347342625939162243221,-15314536669850931782955034,0,364039224441726736112898,-258252115205380664852489)` |
| $16$ | `(14158320428229431110632035534,1445930252748986602556503,-4037566578788233075388461,-15707433663852947987003331963,3377546630512239424831227,-135678457396165578494220422328,161380829655522800921478001174,-7619624145258417061840219,756716246940050246192295991360,756039854358217186078585859893,-756047140773850257596518356013,-756708965678152618166525057874,-124356367987737931921432875,121310055202113471963814956,-1906273902363680147555713,-62435749618545347914412709,62134847680104516979394702,-42738132624201778558051101,42763792589760034305034916,-1,-1016530778839072523496384,721134444259828239472438)` |
| $17$ | `(55080423957920834724384178176423,5625134120866728895584332467,-15707433663852947987003331963,-61106973096252509173132192750792,13139743607958868823561427094,-527832873483854629014728473587843,627823375037063188496467155746567,-29642790643729510541698259383,430739186473609613592495335618,394468955459864427127999973084,-171586979203555083516984602252,-140309294129799934352157258537,-483786301161457531966820296272,471935163832620193659230484747,-7416019100172481604961159656,-242895163769798535305248246905,241724558370443705057524637686,-166265093098000006169783736951,166364918623835426274272913933,-1,-3954631945827032253612656597,2805445117719955712121919533)` |
| $18$ | `(-11843863506129705453329388746,-1209564414066890896087088,3377546630512239424831227,13139743607958868823561427094,-2825419969844393861126238,113499135597920462783629169410,-134999947814078942591063100629,6374046187322842181266109,796932920832670210782888303906,-796273751659205267446361367304,796279164131686299646414529258,-796938327717191465329619050970,104027865171645514747026944,-101479532337054776152582452,1594655808175977305761130,52229394025475991035320024,-51977680447888262933349308,35751741308147222601841153,-35773206645874571682282990,0,850358759386781053209326,-603250786043285150566056)` |
| $19$ | `(475776445425035645631311831252906,48589065311291765208029978414,-135678457396165578494220422328,-527832873483854629014728473587843,113499135597920462783629169410,-4559341237396505515868947581681778,5423044200932079859125854598678370,-256049982035840904921051730715,221754645041914048896240868442609,90433068870036206683214282201702,-230722616125064212308593766183441,-90396697078033770349851523674998,-1945553482064219701504486913036072,1910817310690118906034484467550629,38741123544493083752354047924041,-2098092013917914082586929635556,2087980499955605449709641508526,-1436172950536147464773977587611,1437035228464163145529554551614,-1,-34159517936668053496563316088,24233014382088384586044501694)` |
| $20$ | `(-565905590075036765039458792102524,-57793579191623778441544818282,161380829655522800921478001174,627823375037063188496467155746567,-134999947814078942591063100629,5423044200932079859125854598678370,-6450363522704114684955593640029346,304555043794251649251993806066,-345419771474085336418139510847166,-138505411928183520866414057864212,354484042530972068107260593780916,133350069523652232553773489349123,3065704597766976052833987353128704,-2942886929215955353528336291365527,-17742677581317619393590995333164,2495545987164714339941744654342,-2483518989337446247337078577096,1708235682615401574524033619184,-1709261306948750963001681583632,0,40630557356322047408410009610,-28823617552023860328025566688)` |
| $21$ | `(26719331579077035730540348554,2728733966663745655317344,-7619624145258417061840219,-29642790643729510541698259383,6374046187322842181266109,-256049982035840904921051730715,304555043794251649251993806066,-14379619749188089027965743,-3025390628670397886837308665487,3045287365963882727830443719647,-9622727969786163775825411541838,9602827322381373666570264919867,-155949643337024195038166769783,89823518430453525962923231208835,-57103776249708543119361207059726,-117827640990518792602452657,117259784181037541313512958,-80654647028596858333324462,80703072061179940769953109,-1,-1918378883838782182233614,1360912152465063668367667)` |

**Definition 24.7 (trial-response numerator vectors).** The following ordered tuples, divided by $10^{30}$, are $v_6^0$ and $v_7^0$.

| System | Complete ordered numerator vector |
| --- | --- |
| $F_6$ | `(387521929964427174746934,979100650740504887500063,325944740798946740020256,-537536742816068237726973,74308661359821586294783,83186304067390603209892,97846282646480832747558,844243013420664775130455,-975309442121823751286479,33220349260748705692933,3680471655269082806369,-3680674861339645090840,474700458200195626187390846719,1191786167972662060036,-4096935588865697143737,526647898181687791353236142554,5980618831341026624709,-683128797075607746464702138300,922780293828629644825876716589,-31824406829692475856758,87267426747824557830166738)` |
| $F_7$ | `(591706237710313626481332,775759873810462533731531,529816112627228411526220,-741737496920879640211892,43365143679504542269901815,-42386858260074227003031222,47593687406626566548350407,288056216939313751688436471,110665109426478714278284663,-295070809850404798835219871,-103582008653132743802485101,-215437486660296051354374145,217250782572115272679275125,-1881803774074144653917146,474688560003744110081291483700,-23327043344114195472,-703894685178098369674,526661098203005930945739276559,3142237433088094327330,-630044723844981912900898006553,839133100949273643478036890437,4223233273933315161991599)` |

**Proposition 24.8 (verification of the displayed finite witnesses).** With the exact source/event rectangles of Definition 16.3 and the interval expressions specified in §§17–21, the rational rows in Definitions 24.2–24.7 satisfy the residual, row-norm and response inequalities in Propositions 18.1, 19.2, 20.1 and 21.2.

Proof. For each matrix form every entry of $E=I-R\mathbf C$, take its absolute interval upper endpoint, sum along each complete row and take the maximum. For responses form every row of $\mathbf Cv^0+\mathbf f$, then multiply by $R$ before taking absolute interval row endpoints. The source intervals are the nine OE Appendix 12 pairs, and the event intervals are the 22 OE Appendix 15.1 pairs; use the explicit derivatives of Definitions 19.1, 20.1 and 21.1. Directed multiplication and positive division by $1-q_R$ give the displayed residual inequalities. The actual inverse bounds follow from Proposition 17.2, without asserting that any candidate is an actual source or exact inverse. The interval products retain all off-root gap terms and every row and column, including six's unused stationary direction. These finite comparisons and the specified derivative majorants supply the arithmetic content of the conditional certificate; no proof-review conclusion is used as a mathematical premise. $\square$

[GCpin]: https://github.com/the-omega-institute/trureturing/blob/321589a8be98de4fe179f99f6e593d8784952db1/docs/develop/theory/FIB_NATIVE_COMPLETE_CONTINUATION_GLOBAL_ACTUAL_COUNTS.md

## 追加锚（本行以下为增补区）

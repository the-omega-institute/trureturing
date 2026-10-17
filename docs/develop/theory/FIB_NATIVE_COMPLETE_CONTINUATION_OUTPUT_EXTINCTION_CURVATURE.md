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

# A strict global K gain from the controlling faces

The whole-face neighborhood theorem of profile73 gives a strict global
improvement of the profile53 K comparison. The construction retains the
old globally defined separately concave source expressions, their exact
vertex bounds, the complete exponent tails, and all eight fallback
branches. It improves only the live identity cost, direction40. No
concavity of a patched table is assumed.

Put

\[
K_0=\frac{108508024932331114670819517565119344585698949}
{212986060315016386011231666281461556328000}
=509.4606885156834\ldots,
\]

and let gamma_K be the exact next positive signed gap of profile71. Set

\[
\delta=\frac1{25000},\qquad \epsilon_0=\frac1{100000},\qquad
h=\frac9{250000}\gamma_K
=\frac{15240056495574031935365456355486859072608164346131}
{9016538134941317921061120774070321426401000000000000000}.
\]

Then every actual family in the inherited source domain satisfies

\[
K\le K_1:=K_0-h.
\]

Here h=0.000001690233686975164...>0. The small size records a conservative
globalization, not a large numerical advance toward the terminal
threshold403. The unrestricted Erdős #7 problem remains open. The
ordinary proof below and its exact arithmetic certificate are not Lean
verification.

The program is `../frontier/source-budgets/global_k_face_gain.py` and the certificate is
`../certificates/source_norms/source-budgets/global_k_face_gain.json`.

## Retain the old true functions and actual mass residual

Write q=23/42, b=WHOLE_CONST, L=AC*H16+H41+A81, and

\[
a=q(K_0-b)-L>0.
\]

Let M_c(theta) be the true profile53 allocated survival margin and let
C_c(theta) be the true profile49 numerator correction used in its common
K comparison. Thus

\[
\Phi_{K_0}^{\rm old}
=aS+\sum_c\pi_c\bigl((K_0-b)M_c+C_c\bigr)
\]

is a sufficient signed comparison. Here S is the single actual
surviving mass and pi is the same actual forbidden-carrier mixture in
all terms. Put S_0=sum pi_c D_c(theta). The mass theorem gives S>=S_0.

The functions

\[
F_c(\theta)=aD_c(\theta)+(K_0-b)M_c(\theta)+C_c(\theta)
\]

are separately concave, as proved in profiles49 and53. Their vertex
lower bounds are the pinned profile53 signed table g_v,c. Therefore,
with the product source barycentric weights Lambda_v,

\[
\Phi_{K_0}^{\rm old}\ge
B+a(S-S_0),\qquad
B=\sum_{v,c}\Lambda_v\pi_cg_{v,c}.
\tag{G1}
\]

Both terms on the right are nonnegative. Profile71 gives

\[
B\ge\gamma_K(1-q(Z_K)).\tag{G2}
\]

## Translate face concentration into the neighborhood coordinates

If q(Z_K)>=1-delta, profile71 selects one of the two entire K beta
faces. Each required factor weight and the selected carrier weight is
at least 1-delta. Normalize the beta weights on the supported triangle
to obtain a face point beta*. The estimates of profile71 give

\[
\|\eta-\eta^*\|_1\le\delta/9,\qquad
\|n-n^*\|_1\le\delta/2,\qquad
\|d-d^*\|_1\le13\delta/4.
\]

The four extra source defects in profile73 satisfy

\[
\delta_P\le\delta/4,\quad
\delta_\alpha\le\delta/4,\quad
\delta_B\le\delta/4,\quad
\delta_L\le\delta/72.
\]

Consequently its infimum over face points obeys

\[
\tau\le\left(\frac19+\frac12+\frac{13}4+
\frac34+\frac1{72}\right)\delta
=\frac{37}8\delta=\frac{37}{200000}<\frac1{1000},
\qquad\kappa\le\delta.\tag{G3}
\]

The selected K root and cell remain mass maximizers on this
neighborhood; profile71 also proves

\[
0\le S_0-D\le\xi:=\frac4{45}\delta
=\frac1{281250}<\epsilon_0.\tag{G4}
\]

This explicitly controls the carrier mass substitution. It does not
replace the unknown actual epsilon=S-D by zero.

## A positive reserve in every case

Outside the two delta-neighborhoods, (G2) supplies

\[
R_{\rm outside}=\gamma_K\delta.\tag{G5}
\]

Inside a face neighborhood, if epsilon>epsilon_0 then (G1) and (G4)
supply

\[
R_{\rm mass}=a(\epsilon_0-\xi)>0.\tag{G6}
\]

In the remaining case epsilon<=epsilon_0, the general guard of
profile73 is satisfied: tau<=1/1000 and epsilon<=1/10000. Its
improvement of the actual identity deficit over the old carrier
average is at least

\[
\frac{677}{24300}-54\tau-608\epsilon-\frac72\kappa
-2\sqrt\epsilon.
\]

Since epsilon_0<=1/300^2, (G3) gives the uniform rational gain

\[
\Delta_*=
\frac{677}{24300}-54\frac{37}{200000}
-\frac{608}{100000}-\frac7{50000}-\frac2{300}
=\frac{121097}{24300000}>0.\tag{G7}
\]

Here the old carrier average is the true globally defined full49
direction40 function. At the 1272 source vertices where profile53 stores
the older47 lower bound, that bound is dominated by full49. The
interpolation in (G1) continues to use full49's separate concavity; the
new gain is relative to that true function, not relative to an
interpolated numerical table. The direction40 contribution is replaced
once, with no extra copy of its old margin.

Direction40 has the exact positive coefficient

\[
\beta_{40}=\frac{94212612766226}{1174116234095805}.
\]

All other costs keep their old bounds. Hence this last case supplies

\[
R_{\rm local}=\beta_{40}\Delta_*>0.\tag{G8}
\]

The exact arithmetic comparisons are

\[
R_{\rm outside}
<R_{\rm mass},\qquad
R_{\rm outside}<R_{\rm local}.
\]

Thus all cases give the same strict reserve

\[
R=\gamma_K/25000
=0.000001878037429972404\ldots.\tag{G9}
\]

This is a pointwise choice between already valid bounds for the actual
identity deficit. It does not replace the old separately concave
functions by a purportedly concave patched expression.

## Turn reserve into a lower global target

Let

\[
E=qS+\sum_c\pi_cM_c.
\]

The existing survival theorem gives E<=rho_actual*S. As rho_actual is
an actual surviving fraction, E<=S<=s<=5/9. Positivity uses the separate
lower-target calculation: with rho_53>0 the profile53 table and its
same separate-concavity argument give

\[
E-\rho_{53}S
\ge\sum_c\pi_c\bigl((q-\rho_{53})D_c+M_c\bigr)\ge0,
\]

because q-rho_53>0 and S>=S_0. Thus E>=rho_53 S>0 before any division.

Changing K_0 to K_0-h changes its sufficient signed expression by
exactly -hE; the improvement to direction40 is independent of that
target. With h=9R/10,

\[
\Phi_{K_1}^{\rm new}\ge R-hE
\ge R-\frac59h=\frac R2>0.\tag{G10}
\]

The exact checker also verifies K_1>b and a-qh>0, so the positive-offset
and lower-mass sign branch remain valid. No finite-height restriction
has been introduced in this argument.

For each of the eight inherited fallback branches, the stored complete
branch bound remains below K_1. Their smallest old reserve relative to
K_0 is 73.40956710560972..., far above h; the checker uses exact
fractions for every branch. Thus the target holds throughout the old
source-domain split, not only on the effective9 branch.

The separate J, Gamma13, T13(81), and survival bounds are unchanged.
The two complete-core error values therefore remain those of
profile53. Replacing K_0 by K_1 reduces each combined core gap by h;
both remain positive. A strict negative terminal comparison and the
unrestricted covering-system conclusion have not been obtained.

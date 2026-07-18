# Golden Phase

`D5/S1/Phase/Basic` maps an integer $n$ to $n \cdot \varphi \bmod 1$ in the additive circle. The map preserves zero, addition, and negation.

$$
\operatorname{goldenPhase}\left(n\right) = n \cdot \varphi \bmod 1
$$

## Additive laws

### Proposition: Zero

Provenance: `repo-derived`

Statement: `D5/S1/Phase/Basic.goldenPhase_zero` `✓ std3`

$$
\operatorname{goldenPhase}\left(0\right) = 0
$$

### Proposition: Addition

Provenance: `repo-derived`

Statement: `D5/S1/Phase/Basic.goldenPhase_add` `✓ std3`

$$
\operatorname{goldenPhase}\left(n + m\right) = \operatorname{goldenPhase}\left(n\right) + \operatorname{goldenPhase}\left(m\right)
$$

### Proposition: Negation

Provenance: `repo-derived`

Statement: `D5/S1/Phase/Basic.goldenPhase_neg` `✓ std3`

$$
\operatorname{goldenPhase}\left(-n\right) = -\operatorname{goldenPhase}\left(n\right)
$$

## Orbit notation

The same orbit has sequence and set presentations:

$$
p_{n} = n \cdot \varphi \bmod 1
$$

$$
\left(n \cdot \varphi \bmod 1\right)_{n \in \mathbb{Z}}
$$

$$
\left\{n \cdot \varphi \bmod 1 \mid n \in \mathbb{Z}\right\}
$$

## Theorem: Injectivity

Provenance: `repo-derived`

Statement: `D5/S1/Phase/Basic.goldenPhase_injective` `✓ std3`

Two phases could coincide only if a nonzero integer multiple of $\varphi$ were an integer. Irrationality excludes this. No three-distance theorem is asserted here.

## Remark: Visible phase and hidden prime fiber

Provenance: `repo-derived`

Statement:

$$
\mathit{visiblePhase} = T
$$

The source treats the all-prime hidden fiber K_infinity = product_p Z_p as derived rather than postulated: accepting a compatible family of congruence readings incurs its dual completion. Its phase interpretation is the exact sequence 0 -> K_infinity -> Sigma_infinity -> T -> 0, where T is visible phase, K_infinity is the hidden all-prime fiber, and Sigma_infinity is the complete phase object.

## Remark: Congruence readings close under dual completion

Provenance: `repo-derived`

Statement:

$$
\mathit{dualK} = \mathit{QmodZ}
$$

In the source's forward direction, a compatible family of congruence readings determines the completion, so hidden structure is the debt incurred by those readings. In the reverse direction, all continuous readings of the completion recover exactly Q/Z = union_m (1/m)Z/Z. Reading, completion, and reading again therefore form a closed loop on the pure congruence layer; the source points separately to the mixed-layer closure.

## Remark: The two phase-duality loops

Provenance: `repo-derived`

Statement:

$$
\mathit{dualSigma} = Q
$$

The source records both dual loops as closed: the pure congruence layer has K_infinity dual to Q/Z, and the mixed layer has Sigma_infinity dual to Q. Conversely, the dual of Q is the constructional origin assigned to Sigma_infinity. On this interpretation the complete phase object's measurable content is precisely the rational numbers, with readings and completion serving as each other's character groups.

## Remark: Dense phase leaves and discrete switching

Provenance: `repo-derived`

Statement:

$$
\operatorname{timeline}\left(a\right) \ne \operatorname{timeline}\left(b\right)
$$

The source's strict replacement for switchable parallel timelines is an uncountable family K_infinity/Z of leaves with one generator and different hidden offsets. Distinct leaves never intersect, while every leaf is dense, so they remain disjoint yet arbitrarily close everywhere. Continuous switching is ruled out; a genuine switch must be a discrete jump obeying a cocycle composition law, and every finite observation is said to be unable to distinguish such a jump from ordinary motion. The continuous phase leaf and discrete address leaf are then read as wave and particle. Finally, every switch must pass through an address reading and enter the ledger, giving the slogan that observation is bookkeeping.

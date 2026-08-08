# Observer Update Defects and Their Perturbation Seminorm

## Abstract

Permutation update defects characterize commutation, cyclic invariants, and a finite perturbation seminorm.

**Theorem 1.1 (Read-update commutation is equivalent to zero defect).**

$$\begin{gathered} \forall I,\ \forall \tau \in \operatorname{Perm}(I),\ \forall f: I\to \mathbb{C},\\ (\forall \psi: I\to \mathbb{C},\ U_{\tau}(R_{f}\psi)=R_{f}(U_{\tau}\psi)) \Leftrightarrow \delta_{\tau}f=0. \end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ObserverMetric.commute_iff_updateDefect_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a register on I be a complex-valued amplitude function. The read R_f multiplies amplitudes pointwise by f, while the permutation update U_tau acts by pullback. The update defect is delta_tau f(i) = f(tau^{-1} i) - f(i). The established read-update commutator formula identifies this defect as the coefficient of the represented commutator. If every register commutes, applying the identity to the constant-one register extracts each coefficient. Conversely, zero defect makes every coefficient times every predecessor amplitude vanish.

Provenance note: OBSERVER-QUANTUM.md, Section 3 motivates the observer metric through read-update noncommutativity. The theorem here is the repository-derived finite-register statement. It asserts no universal C*-algebra, operator norm, Connes metric, or Rieffel structure.

**Theorem 1.2 (Zero defect is equivalent to update invariance).**

$$\forall I,\ \forall \tau \in \operatorname{Perm}(I),\ \forall f: I\to \mathbb{C},\ \delta_{\tau}f=0 \Leftrightarrow \forall i\in I,\ f(\taui)=f(i).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ObserverMetric.updateDefect_eq_zero_iff_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The defect uses the inverse permutation because updates act by pullback, whereas invariance is stated in the forward coordinate. Evaluating a zero defect at tau(i) gives f(i) = f(tau(i)); in the reverse direction, applying forward invariance at tau^{-1}(i) cancels every defect coordinate. Thus the kernel is characterized without a finiteness or inhabitance assumption.

**Theorem 1.3 (Cyclic-window invariants are exactly constant).**

$$\begin{gathered} \forall M\in \mathbb{N},\ M\neq 0 \Rightarrow \forall f: \operatorname{ZMod}(M)\to \mathbb{C},\\ \delta_{+1}f=0 \Leftrightarrow \exists c\in \mathbb{C},\ f=(i\mapsto c). \end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ObserverMetric.invariant_iff_const_on_cyclic_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the nonempty cyclic window ZMod M, the update is addition by one. Zero defect first becomes invariance under this successor. Every residue has a natural-number representative, so induction along successive additions shows that its value equals f(0). Constant functions are invariant immediately. This is the precise finite-window form of the statement that the common observables are constants.

**Theorem 1.4 (The perturbation seminorm vanishes exactly on invariants).**

$$\begin{gathered} \forall I,\ 0<\VertI\Vert<\infty,\ \forall \tau \in \operatorname{Perm}(I),\ \forall f: I\to \mathbb{C},\\ L_{\tau}(f)=0 \Leftrightarrow \forall i\in I,\ f(\taui)=f(i). \end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ObserverMetric.perturbationSeminorm_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite nonempty index type, define L_tau(f) as the maximum of |delta_tau f(i)| over all indices. If this maximum is zero, every nonnegative coordinate norm is bounded above by zero and hence every defect coordinate vanishes. The converse is immediate from the same finite maximum. Combining this fact with the forward-invariance characterization identifies the seminorm kernel exactly.

**Theorem 1.5 (The perturbation seminorm is subadditive).**

$$\begin{gathered} \forall I,\ 0<\VertI\Vert<\infty,\ \forall \tau \in \operatorname{Perm}(I),\\ \forall f,g: I\to \mathbb{C},\ L_{\tau}(f+g)\leqL_{\tau}(f)+L_{\tau}(g). \end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ObserverMetric.perturbationSeminorm_add_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The update defect is additive in the observable. At each index, the complex triangle inequality bounds the defect of f + g by the sum of the two defect norms. Each summand is then bounded by its own finite maximum, yielding subadditivity of L_tau.

**Theorem 1.6 (The perturbation seminorm is absolutely homogeneous).**

$$\begin{gathered} \forall I,\ 0<\VertI\Vert<\infty,\ \forall \tau \in \operatorname{Perm}(I),\\ \forall c\in \mathbb{C},\ \forall f: I\to \mathbb{C},\ L_{\tau}(cf)=\Vertc\Vert L_{\tau}(f). \end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ObserverMetric.perturbationSeminorm_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Scalar multiplication factors c out of every defect coordinate, and the complex norm converts that factor to |c|. Since |c| is nonnegative, it also factors through the finite maximum. Together with subadditivity and the kernel theorem, this establishes the claimed perturbation seminorm laws on finite nonempty windows.

## References

- Truth anchor: `D5/S3/Observer/ObserverMetric.commute_iff_updateDefect_eq_zero`
- Truth anchor: `D5/S3/Observer/ObserverMetric.invariant_iff_const_on_cyclic_window`
- Truth anchor: `D5/S3/Observer/ObserverMetric.perturbationSeminorm_add_le`
- Truth anchor: `D5/S3/Observer/ObserverMetric.perturbationSeminorm_eq_zero_iff`
- Truth anchor: `D5/S3/Observer/ObserverMetric.perturbationSeminorm_smul`
- Truth anchor: `D5/S3/Observer/ObserverMetric.updateDefect_eq_zero_iff_invariant`
- Dependency: [D5/S3/Quantum/ObserverAlgebra](../Quantum/ObserverAlgebra.md)

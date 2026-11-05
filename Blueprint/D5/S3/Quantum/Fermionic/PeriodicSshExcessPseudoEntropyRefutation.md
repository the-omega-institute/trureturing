# Positive excess pseudo-entropy in a periodic SSH chain

## Abstract

Same-phase half-filled ground states of a periodic three-cell SSH chain have positive averaged excess pseudo-entropy.

The modes are ordered (1,A), (1,B), …, (N,A), (N,B), with zero-based indices in Fin(2N). An occupation configuration is a function Fin(2N) → Bool, where true means occupied. JordanWigner denotes D5.S3.Quantum.SpinChains.SupersymmetricFermion.JordanWigner, and FockMajoranaCarrier denotes D5.S3.Quantum.Fermionic.FockMajoranaCarrier. Their annihilation and number operators act on the full occupation space. All finite-type sums range over the displayed type. Nat.div and Nat.mod are natural quotient and remainder. Matrix.conjTranspose is conjugate transpose; star conjugates a vector pointwise, dotProduct is the bilinear coordinate sum, Matrix.mulVec is matrix action, and SMul.smul is scalar multiplication. Casts display their target type. Type* allows any universe; bracketed Fintype and DecidableEq assumptions are anonymous instances.

**Definition 1.1 (The periodic single-particle hopping matrix).**

$$\forall N \in \mathit{Nat},\; \forall v \in \mathit{Real},\; (\operatorname{\mathit{sshHopping}}\left(N, v\right):\operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(2 \cdot N\right), \operatorname{\mathit{Fin}}\left(2 \cdot N\right), \mathit{Real}\right)) = \lambda(i:\operatorname{\mathit{Fin}}\left(2 \cdot N\right))\mapsto(\lambda(j:\operatorname{\mathit{Fin}}\left(2 \cdot N\right))\mapsto((\operatorname{\mathit{if}} ((\operatorname{\mathit{Nat}}.\operatorname{\mathit{div}}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(i\right), 2\right) = \operatorname{\mathit{Nat}}.\operatorname{\mathit{div}}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right), 2\right)) \land (i \ne j)) \operatorname{\mathit{then}} v \operatorname{\mathit{else}} 0) + (\operatorname{\mathit{if}} (((\operatorname{\mathit{Nat}}.\operatorname{\mathit{mod}}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(i\right), 2\right) = 1) \land (\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right) = \operatorname{\mathit{Nat}}.\operatorname{\mathit{mod}}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(i\right) + 1, 2 \cdot N\right))) \lor ((\operatorname{\mathit{Nat}}.\operatorname{\mathit{mod}}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right), 2\right) = 1) \land (\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(i\right) = \operatorname{\mathit{Nat}}.\operatorname{\mathit{mod}}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right) + 1, 2 \cdot N\right)))) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0)))$$

*Formalization.* `D5/S3/Quantum/Fermionic/PeriodicSshExcessPseudoEntropyRefutation.sshHopping` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pramod Kamal Kharel; Manghang Limbu; Nabaraj Khatri; Ashish Khanal; Kiran Adhikari (2026). *Pseudo entropy and topological phases of matter*. URL: <https://arxiv.org/abs/2606.29311v1>.

*Commentary.*

The intracell bond joins the A and B modes of each cell with real amplitude v. The intercell bond has amplitude w = 1 and joins each B orbital to the A orbital of the next cell. The remainder modulo 2N includes the bond from (N,B) to (1,A), in both directions, as in equation (15).

**Definition 1.2 (The many-body SSH Hamiltonian).**

$$\forall N \in \mathit{Nat},\; \forall v \in \mathit{Real},\; (\operatorname{\mathit{hamiltonian}}\left(N, v\right):\operatorname{\mathit{Matrix}}\left((\operatorname{\mathit{Fin}}\left(2 \cdot N\right) \to \mathit{Bool}), (\operatorname{\mathit{Fin}}\left(2 \cdot N\right) \to \mathit{Bool}), \mathit{Complex}\right)) = \sum_{i:\operatorname{\mathit{Fin}}\left(2 \cdot N\right)}(\sum_{j:\operatorname{\mathit{Fin}}\left(2 \cdot N\right)}(\operatorname{\mathit{SMul}}.\operatorname{\mathit{smul}}\left(((\operatorname{\mathit{sshHopping}}\left(N, v, i, j\right):\mathit{Real}):\mathit{Complex}), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{conjTranspose}}\left(\operatorname{\mathit{JordanWigner}}.\operatorname{\mathit{fullC}}\left(i\right)\right) \cdot \operatorname{\mathit{JordanWigner}}.\operatorname{\mathit{fullC}}\left(j\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Fermionic/PeriodicSshExcessPseudoEntropyRefutation.hamiltonian` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pramod Kamal Kharel; Manghang Limbu; Nabaraj Khatri; Ashish Khanal; Kiran Adhikari (2026). *Pseudo entropy and topological phases of matter*. URL: <https://arxiv.org/abs/2606.29311v1>.

*Commentary.*

Equation (15) acts on the full fermionic Fock space by the sum of hopping coefficients times cᵢ†cⱼ. JordanWigner.fullC uses the stated ordering of the modes, so the annihilator at j has the parity string from all earlier modes. The periodic bond is included in the same operator sum, with these fermionic signs.

**Theorem 1.3 (The mixed canonical anticommutation relation).**

$$\forall M \in \mathit{Nat},\; \forall i \in \operatorname{\mathit{Fin}}\left(M\right),\; \forall j \in \operatorname{\mathit{Fin}}\left(M\right),\; \operatorname{\mathit{JordanWigner}}.\operatorname{\mathit{fullC}}\left(i\right) \cdot \operatorname{\mathit{Matrix}}.\operatorname{\mathit{conjTranspose}}\left(\operatorname{\mathit{JordanWigner}}.\operatorname{\mathit{fullC}}\left(j\right)\right) + \operatorname{\mathit{Matrix}}.\operatorname{\mathit{conjTranspose}}\left(\operatorname{\mathit{JordanWigner}}.\operatorname{\mathit{fullC}}\left(j\right)\right) \cdot \operatorname{\mathit{JordanWigner}}.\operatorname{\mathit{fullC}}\left(i\right) = \operatorname{\mathit{if}} (i = j) \operatorname{\mathit{then}} (1:\operatorname{\mathit{Matrix}}\left((\operatorname{\mathit{Fin}}\left(M\right) \to \mathit{Bool}), (\operatorname{\mathit{Fin}}\left(M\right) \to \mathit{Bool}), \mathit{Complex}\right)) \operatorname{\mathit{else}} 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/PeriodicSshExcessPseudoEntropyRefutation.fullC_mixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The anticommutator of an annihilator and a creator is the identity for equal modes and zero for distinct modes.

**Definition 1.4 (Half filling and ground-state minimality).**

$$\forall N \in \mathit{Nat},\; \forall v \in \mathit{Real},\; \forall psi \in (\operatorname{\mathit{Fin}}\left(2 \cdot N\right) \to \mathit{Bool}) \to \mathit{Complex},\; (\operatorname{\mathit{IsHalfFilledGroundState}}\left(N, v, \mathit{psi}\right)) \Leftrightarrow ((\mathit{psi} \ne 0) \land ((\operatorname{\mathit{Matrix}}.\operatorname{\mathit{mulVec}}\left(\operatorname{\mathit{FockMajoranaCarrier}}.\operatorname{\mathit{numberOperator}}\left(2 \cdot N\right), \mathit{psi}\right) = \operatorname{\mathit{SMul}}.\operatorname{\mathit{smul}}\left((N:\mathit{Complex}), \mathit{psi}\right)) \land (\forall phi \in (\operatorname{\mathit{Fin}}\left(2 \cdot N\right) \to \mathit{Bool}) \to \mathit{Complex},\; (\mathit{phi} \ne 0) \Rightarrow ((\operatorname{\mathit{Matrix}}.\operatorname{\mathit{mulVec}}\left(\operatorname{\mathit{FockMajoranaCarrier}}.\operatorname{\mathit{numberOperator}}\left(2 \cdot N\right), \mathit{phi}\right) = \operatorname{\mathit{SMul}}.\operatorname{\mathit{smul}}\left((N:\mathit{Complex}), \mathit{phi}\right)) \Rightarrow (\operatorname{\mathit{Complex}}.\operatorname{\mathit{re}}\left(\operatorname{\mathit{dotProduct}}\left(\operatorname{\mathit{star}}\left(\mathit{psi}\right), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{mulVec}}\left(\operatorname{\mathit{hamiltonian}}\left(N, v\right), \mathit{psi}\right)\right)\right) \cdot \operatorname{\mathit{Complex}}.\operatorname{\mathit{re}}\left(\operatorname{\mathit{dotProduct}}\left(\operatorname{\mathit{star}}\left(\mathit{phi}\right), \mathit{phi}\right)\right) \le \operatorname{\mathit{Complex}}.\operatorname{\mathit{re}}\left(\operatorname{\mathit{dotProduct}}\left(\operatorname{\mathit{star}}\left(\mathit{phi}\right), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{mulVec}}\left(\operatorname{\mathit{hamiltonian}}\left(N, v\right), \mathit{phi}\right)\right)\right) \cdot \operatorname{\mathit{Complex}}.\operatorname{\mathit{re}}\left(\operatorname{\mathit{dotProduct}}\left(\operatorname{\mathit{star}}\left(\mathit{psi}\right), \mathit{psi}\right)\right))))))$$

*Formalization.* `D5/S3/Quantum/Fermionic/PeriodicSshExcessPseudoEntropyRefutation.IsHalfFilledGroundState` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pramod Kamal Kharel; Manghang Limbu; Nabaraj Khatri; Ashish Khanal; Kiran Adhikari (2026). *Pseudo entropy and topological phases of matter*. URL: <https://arxiv.org/abs/2606.29311v1>.

*Commentary.*

Half filling means exactly N particles among the 2N modes. The vector is nonzero and is an eigenvector of FockMajoranaCarrier.numberOperator with eigenvalue N. Its energy is minimal among all nonzero vectors in that particle sector. The inequality is the comparison of Rayleigh quotients after multiplication by the two positive squared norms, so no normalization is required.

**Definition 1.5 (Partial trace over the later cells).**

$$\forall N \in \mathit{Nat},\; \forall L \in \mathit{Nat},\; \forall h \in 2 \cdot L \le 2 \cdot N,\; \forall X \in \operatorname{\mathit{Matrix}}\left((\operatorname{\mathit{Fin}}\left(2 \cdot N\right) \to \mathit{Bool}), (\operatorname{\mathit{Fin}}\left(2 \cdot N\right) \to \mathit{Bool}), \mathit{Complex}\right),\; (\operatorname{\mathit{reduce}}\left(h, X\right):\operatorname{\mathit{Matrix}}\left((\operatorname{\mathit{Fin}}\left(2 \cdot L\right) \to \mathit{Bool}), (\operatorname{\mathit{Fin}}\left(2 \cdot L\right) \to \mathit{Bool}), \mathit{Complex}\right)) = \lambda(a:\operatorname{\mathit{Fin}}\left(2 \cdot L\right) \to \mathit{Bool})\mapsto(\lambda(b:\operatorname{\mathit{Fin}}\left(2 \cdot L\right) \to \mathit{Bool})\mapsto(\sum_{x:\operatorname{\mathit{Fin}}\left(2 \cdot N\right) \to \mathit{Bool}}(\sum_{y:\operatorname{\mathit{Fin}}\left(2 \cdot N\right) \to \mathit{Bool}}(\operatorname{\mathit{if}} ((\forall i \in \operatorname{\mathit{Fin}}\left(2 \cdot L\right),\; x\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{castLE}}\left(h, i\right)\right) = a\left(i\right)) \land ((\forall i \in \operatorname{\mathit{Fin}}\left(2 \cdot L\right),\; y\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{castLE}}\left(h, i\right)\right) = b\left(i\right)) \land (\forall k \in \operatorname{\mathit{Fin}}\left(2 \cdot N\right),\; (2 \cdot L \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(k\right)) \Rightarrow (x\left(k\right) = y\left(k\right))))) \operatorname{\mathit{then}} X\left(x, y\right) \operatorname{\mathit{else}} 0))))$$

*Formalization.* `D5/S3/Quantum/Fermionic/PeriodicSshExcessPseudoEntropyRefutation.reduce` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pramod Kamal Kharel; Manghang Limbu; Nabaraj Khatri; Ashish Khanal; Kiran Adhikari (2026). *Pseudo entropy and topological phases of matter*. URL: <https://arxiv.org/abs/2606.29311v1>.

*Commentary.*

Subsystem A consists of the first L cells, hence the first 2L modes in the Jordan–Wigner order. Fin.castLE embeds these initial indices into Fin(2N). The two full configurations agree on every later orbital and restrict to a and b on the initial modes. Summing their matrix entries traces out the modes of the remaining cells. This initial partition crosses no modes.

**Definition 1.6 (Spectral entropy with algebraic multiplicity).**

$$\forall n \in \mathit{Type}*,\; [\operatorname{\mathit{Fintype}}\left(n\right)], [\operatorname{\mathit{DecidableEq}}\left(n\right)], \forall X \in \operatorname{\mathit{Matrix}}\left(n, n, \mathit{Complex}\right),\; (\operatorname{\mathit{matrixEntropy}}\left(X\right):\mathit{Complex}) = \operatorname{\mathit{Multiset}}.\operatorname{\mathit{sum}}\left(\operatorname{\mathit{Multiset}}.\operatorname{\mathit{map}}\left(\lambda(z:\mathit{Complex})\mapsto(-\left(z \cdot \operatorname{\mathit{Complex}}.\operatorname{\mathit{log}}\left(z\right)\right)), \operatorname{\mathit{Polynomial}}.\operatorname{\mathit{roots}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{charpoly}}\left(X\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/PeriodicSshExcessPseudoEntropyRefutation.matrixEntropy` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pramod Kamal Kharel; Manghang Limbu; Nabaraj Khatri; Ashish Khanal; Kiran Adhikari (2026). *Pseudo entropy and topological phases of matter*. URL: <https://arxiv.org/abs/2606.29311v1>.

*Commentary.*

The characteristic roots are taken with algebraic multiplicity. The multiset is mapped by z ↦ −z log z and then summed. Complex.log is the principal scalar logarithm, with Complex.log(0) = 0. This is the spectral form of equations (1)–(3), agreeing with −Tr(X log X) wherever that matrix function is defined.

**Definition 1.7 (The averaged excess pseudo-entropy).**

$$\forall N \in \mathit{Nat},\; \forall L \in \mathit{Nat},\; \forall h \in 2 \cdot L \le 2 \cdot N,\; \forall psi1 \in (\operatorname{\mathit{Fin}}\left(2 \cdot N\right) \to \mathit{Bool}) \to \mathit{Complex},\; \forall psi2 \in (\operatorname{\mathit{Fin}}\left(2 \cdot N\right) \to \mathit{Bool}) \to \mathit{Complex},\; (\operatorname{\mathit{averagedExcess}}\left(h, \mathit{psi1}, \mathit{psi2}\right):\mathit{Real}) = \operatorname{\mathit{Complex}}.\operatorname{\mathit{re}}\left(\operatorname{\mathit{matrixEntropy}}\left(\operatorname{\mathit{reduce}}\left(h, \operatorname{\mathit{SMul}}.\operatorname{\mathit{smul}}\left(\operatorname{\mathit{Inv}}.\operatorname{\mathit{inv}}\left(\operatorname{\mathit{dotProduct}}\left(\operatorname{\mathit{star}}\left(\mathit{psi2}\right), \mathit{psi1}\right)\right), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecMulVec}}\left(\mathit{psi1}, \operatorname{\mathit{star}}\left(\mathit{psi2}\right)\right)\right)\right)\right)\right) - \frac{\operatorname{\mathit{Complex}}.\operatorname{\mathit{re}}\left(\operatorname{\mathit{matrixEntropy}}\left(\operatorname{\mathit{reduce}}\left(h, \operatorname{\mathit{SMul}}.\operatorname{\mathit{smul}}\left(\operatorname{\mathit{Inv}}.\operatorname{\mathit{inv}}\left(\operatorname{\mathit{dotProduct}}\left(\operatorname{\mathit{star}}\left(\mathit{psi1}\right), \mathit{psi1}\right)\right), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecMulVec}}\left(\mathit{psi1}, \operatorname{\mathit{star}}\left(\mathit{psi1}\right)\right)\right)\right)\right)\right) + \operatorname{\mathit{Complex}}.\operatorname{\mathit{re}}\left(\operatorname{\mathit{matrixEntropy}}\left(\operatorname{\mathit{reduce}}\left(h, \operatorname{\mathit{SMul}}.\operatorname{\mathit{smul}}\left(\operatorname{\mathit{Inv}}.\operatorname{\mathit{inv}}\left(\operatorname{\mathit{dotProduct}}\left(\operatorname{\mathit{star}}\left(\mathit{psi2}\right), \mathit{psi2}\right)\right), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecMulVec}}\left(\mathit{psi2}, \operatorname{\mathit{star}}\left(\mathit{psi2}\right)\right)\right)\right)\right)\right)}{2}$$

*Formalization.* `D5/S3/Quantum/Fermionic/PeriodicSshExcessPseudoEntropyRefutation.averagedExcess` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pramod Kamal Kharel; Manghang Limbu; Nabaraj Khatri; Ashish Khanal; Kiran Adhikari (2026). *Pseudo entropy and topological phases of matter*. URL: <https://arxiv.org/abs/2606.29311v1>.

*Commentary.*

Matrix.vecMulVec forms the outer product. The first reduced matrix is the transition ψ₁ψ₂† divided by the overlap ψ₂†ψ₁. The other two are the normalized pure-state density matrices. Equation (21) subtracts the mean of the two input entropies from the real part of the transition entropy. The definition takes real parts of all three spectral entropies; for reduced density matrices their entropies are real.

**Definition 1.8 (Non-positivity for every same-phase periodic chain).**

$$(\mathit{claim}) \Leftrightarrow (\forall N \in \mathit{Nat},\; \forall L \in \mathit{Nat},\; \forall h \in 2 \cdot L \le 2 \cdot N,\; (1 \le L) \Rightarrow ((L < N) \Rightarrow (\forall v1 \in \mathit{Real},\; \forall v2 \in \mathit{Real},\; (((\left|\mathit{v1}\right| < 1) \land (\left|\mathit{v2}\right| < 1)) \lor ((1 < \left|\mathit{v1}\right|) \land (1 < \left|\mathit{v2}\right|))) \Rightarrow (\forall psi1 \in (\operatorname{\mathit{Fin}}\left(2 \cdot N\right) \to \mathit{Bool}) \to \mathit{Complex},\; \forall psi2 \in (\operatorname{\mathit{Fin}}\left(2 \cdot N\right) \to \mathit{Bool}) \to \mathit{Complex},\; (\operatorname{\mathit{IsHalfFilledGroundState}}\left(N, \mathit{v1}, \mathit{psi1}\right)) \Rightarrow ((\operatorname{\mathit{IsHalfFilledGroundState}}\left(N, \mathit{v2}, \mathit{psi2}\right)) \Rightarrow ((\operatorname{\mathit{dotProduct}}\left(\operatorname{\mathit{star}}\left(\mathit{psi2}\right), \mathit{psi1}\right) \ne 0) \Rightarrow (\operatorname{\mathit{averagedExcess}}\left(h, \mathit{psi1}, \mathit{psi2}\right) \le 0)))))))$$

*Formalization.* `D5/S3/Quantum/Fermionic/PeriodicSshExcessPseudoEntropyRefutation.claim` (`✓ std3`).

*Citation.* Pramod Kamal Kharel; Manghang Limbu; Nabaraj Khatri; Ashish Khanal; Kiran Adhikari (2026). *Pseudo entropy and topological phases of matter*. URL: <https://arxiv.org/abs/2606.29311v1>.

*Commentary.*

Section IV asserts non-positivity for same-phase half-filled SSH ground states at w = 1, and Section VI states that periodic boundary conditions give no exceptions at any system size. Here 1 ≤ L < N makes A a nonempty proper initial segment of cells. Both couplings have absolute value below one, or both have absolute value above one. The assertion includes every pair of half-filled ground states with nonzero overlap, and retains both the topological and the trivial phase.

**Theorem 1.9 (Positive excess for three unit cells).**

$$\neg (\mathit{claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/PeriodicSshExcessPseudoEntropyRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/kharel-limbu-khatri-khanal-adhikari-2026-periodic-ssh-excess-pseudo-entropy` (refuted) by `D5/S3/Quantum/Fermionic/PeriodicSshExcessPseudoEntropyRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kharel-limbu-khatri-khanal-adhikari-2026-periodic-ssh-excess-pseudo-entropy","declaration_gid":"D5/S3/Quantum/Fermionic/PeriodicSshExcessPseudoEntropyRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Pramod Kamal Kharel; Manghang Limbu; Nabaraj Khatri; Ashish Khanal; Kiran Adhikari (2026). *Pseudo entropy and topological phases of matter*. URL: <https://arxiv.org/abs/2606.29311v1>.

*Commentary.*

Take three unit cells, A the first cell, v₁ = 3/8 and v₂ = 5/8. Both couplings are in the topological phase. Write an occupation configuration as the integer k = ∑ⱼ₌₀⁵ 2ʲ xⱼ, with xⱼ = 1 for an occupied orbital. Two rational ground states have the following pairs of amplitudes at their nonzero coordinates: 7:(−4,−2), 11:(20,6), 13:(−20,−6), 14:(4,2), 19:(−20,−6), 21:(21,7), 22:(−5,−3), 25:(−5,−3), 26:(5,3), 28:(−4,−2), 35:(4,2), 37:(−5,−3), 38:(5,3), 41:(5,3), 42:(−21,−7), 44:(20,6), 49:(−4,−2), 50:(20,6), 52:(−20,−6), 56:(4,2); every other amplitude is zero. Each occupied configuration has three particles. The squared norms are 3528 and 392, the overlap is 1152, and the ground energies are −25/8 and −27/8, respectively.

In the occupation basis 00, 10, 01, 11 of the first cell, each reduced matrix has diagonal entries (a,p,p,a), entries q at positions (10,01) and (01,10), and zero elsewhere. For the normalized transition, (a,p,q) = (2/9,5/18,−1/6), with spectrum {2/9,2/9,4/9,1/9}. For the first reduced density matrix, (a,p,q) = (104/441,233/882,−5/42), with spectrum {104/441,104/441,169/441,64/441}. For the second, (a,p,q) = (10/49,29/98,−3/14), with spectrum {10/49,10/49,25/49,4/49}. All three spectra are strictly positive. Their entropies are, respectively, 2 log 3 − (4/3) log 2; 2 log 3 + 2 log 7 − (16/7) log 2 − (26/21) log 13; and 2 log 7 − (4/7) log 2 − (10/7) log 5.

Consequently ∆S = (1/21) log(2²·3²¹·5¹⁵·13¹³/7⁴²) > 0. The sign follows from the integer inequality 7⁴² < 2²·3²¹·5¹⁵·13¹³. Thus non-positivity fails for a one-cell subsystem even when both periodic-chain ground states are in the same phase.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/PeriodicSshExcessPseudoEntropyRefutation.IsHalfFilledGroundState`
- Truth anchor: `D5/S3/Quantum/Fermionic/PeriodicSshExcessPseudoEntropyRefutation.averagedExcess`
- Truth anchor: `D5/S3/Quantum/Fermionic/PeriodicSshExcessPseudoEntropyRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Fermionic/PeriodicSshExcessPseudoEntropyRefutation.fullC_mixed`
- Truth anchor: `D5/S3/Quantum/Fermionic/PeriodicSshExcessPseudoEntropyRefutation.hamiltonian`
- Truth anchor: `D5/S3/Quantum/Fermionic/PeriodicSshExcessPseudoEntropyRefutation.matrixEntropy`
- Truth anchor: `D5/S3/Quantum/Fermionic/PeriodicSshExcessPseudoEntropyRefutation.reduce`
- Truth anchor: `D5/S3/Quantum/Fermionic/PeriodicSshExcessPseudoEntropyRefutation.result`
- Truth anchor: `D5/S3/Quantum/Fermionic/PeriodicSshExcessPseudoEntropyRefutation.sshHopping`
- Dependency: [D5/S3/Quantum/Fermionic/FockMajoranaCarrier](FockMajoranaCarrier.md)
- Dependency: [D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreCompression](../SpinChains/SupersymmetricFermion/HardCoreCompression.md)

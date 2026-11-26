import GRH.Lib.General.Algebra.FaithfulChar
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Known result: Green's characters of GL_n(F_q) and the parabolic-induction ring. Its files treat
only cuspidal characters and their products over squarefree polynomials, named through a fixed
character of the algebraic closure. It gives orthonormality, a degree bound, twisting and vanishing,
and Hall polynomials do not appear. Source: J. A. Green, The characters of the finite general linear
groups, Trans. AMS 80 (1955), Thms 2, 9, 12-14; for the ring on all matrices, Z. Chen, arXiv
2408.06191, Prop. 3.2.

This file: Induction on squarefree labels; lower bound from the degree of Green's characters. -/


open Module Matrix Finset Complex Hall Fintype ComplexOrder LinearMap GeneralLinearGroup
variable {k n : Type _} {r : ℕ} (K : Type _) [Field k] [Finite k] [Field K] [Algebra k K]
  {T : MulChar K ℂ} [IsFaithfulMulChar K T] [Fintype n] {c : Polynomial k}

omit [Finite k] in
@[elab_as_elim] lemma IsLabel.induction_irreducible_mul [IsAlgClosed K] {p : ℕ → _ → Prop} (hc :
  IsLabel r c) (h1 : p 0 1) (h : ∀ P r c (ξ : K), P.Monic → Irreducible P → P.coeff 0 ≠ 0 →
  P.aeval ξ = 0 → p r c → p (P.natDegree + r) (P * c)) : p r c := by
  induction r using Nat.strongRec generalizing c
  obtain _ | ⟨P, n, i, c, rfl⟩ := not_or_of_imp c.exists_monic_irreducible_factor <;>
    simp_all [IsLabel, hc.1.isUnit_iff, squarefree_mul_iff]
  grind [i.natDegree_pos, n.of_mul_monic_left, n.natDegree_mul,
    IsAlgClosed.exists_aeval_eq_zero K P i.degree_pos.ne']

lemma IsLabel.map (hc : IsLabel r c) : IsLabel r (c.map (algebraMap k K)) := by
    simp_all [IsLabel, (PerfectField.separable_iff_squarefree.2 _).map.squarefree]

attribute [local simp] rankInner finMean NeZero.ne simClassOf_out_eq_one_iff prod_range_succ

/-- For a label c of degree r = |n| over a field with q elements, Re Ξ_c(1) ≥ 0, and the coefficient
at 1 of the group algebra element attached to Ξ_c by `labelIdem` has real part at least (1 − r/q)
q^{−r}. -/
lemma labelChar_degree_bounds (hc :
  IsLabel (card n) c) : let d := (labelChar T c).evalGL (n := n) 1; 0 ≤ d.re ∧ ((1 -
    card n / Nat.card k) / Nat.card k ^ card n : ℝ) ≤ d / Nat.card (GL n k) * star d := by
  have o := @Finite.one_lt_card k _ _
  let z : PowerBasis k k := ⟨1, 1, .singleton .., by simp⟩
  obtain ⟨B, b, e⟩ : ∃ B ≤ Nat.card k ^ card n, rankInner (card n) (labelChar T c) (mulMu fun c ↦
    ite (∀ x, c.out.2 x = x) 1 0) * B = (-1) ^ card n := hc.induction_irreducible_mul K ⟨1, by
    aesop⟩ fun P r c _ m i _ _ ⟨B, b, e⟩ ↦ ⟨_, Nat.pow_add .. ▸ mul_le_mul' (Nat.pred_le _) b, by
    have := NeZero.of_pos i.natDegree_pos
    have h := mulMu_greenCuspidal_lsmul (K := K) (V := Fin P.natDegree → k) z
    simp [minpoly.eq_X_sub_C'] at h
    rw [map_mul, labelChar_eq_greenTau T i m,
      rankInner_mul_eq_rankInner_skew greenTau_eq_zero_of_dim_ne, pow_add, ← e, ← star_inj]
    simp [z, skew, greenTau, field, Nat.card_fun, ite_div, ite_and, forall_and,
      ← Nat.card_congr (generalLinearEquiv ..).1, LinearMap.ext_iff] at *; grind⟩
  rw [← finrank_pi k, rankInner_eq_classInner_simClassOf, classInner,
    ← star_inj] at e; simp [prod_neg, field, Lagrange.eval_nodal, by simpa [z] using
    (moebius_and_greenCuspidal_lsmul (V := n → k) z T).1, ↓← Nat.card_congr toLin.1] at e
  by_cases B = 0 <;> simp_all [← eq_div_iff, evalGL, End.one_eq_id, ← ofReal_natCast, ← ofReal_pow,
    ← ofReal_prod, le_def, @eq_comm ℂ 0, prod_eq_zero_iff]
  rify at *; use by positivity
  grw [b, b]; simp [card_GL_eq_prod, field]; induction' card n with m h <;> simp [← mul_assoc]
  grw [← h] <;> simp [field, pow_succ] <;> nlinarith [one_le_pow₀ o.le (n := m)]

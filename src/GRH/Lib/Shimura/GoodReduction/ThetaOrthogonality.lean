import GRH.Lib.CM.Sigma.SigmaFunction
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Good reduction of unitary PEL abelian varieties, in analytic form (no toric
degeneration) (known result; see Lib.Shimura.GoodReduction.ArcReduction).

This file: Valuations of theta values at torsion points, sup norm, boundedness, peak-shifting
defects. Orthogonality of translates of theta functions; stable integral lattices are
proportional. -/

open Complex Filter Module NNReal QuotientAddGroup Set Submodule thetaSpace ZSpan

variable {V : Type} [FinComplexSpace V] {L : Submodule ℤ V} {v : Valuation ℂ ℝ≥0} {B B' :
  LatticeForm L} (B : LatticeForm L)

/-- The ℤ-submodule of the vectors a of V with na in L for some n ≠ 0: the preimage in V of the
torsion subgroup of V/L. -/
def torsionPoints (L : Submodule ℤ V) := ((torsion' ℤ _ (nonZeroDivisors ℕ)).comap L.mkQ).copy
    {a | ∃ n ≠ 0, n • a ∈ L} (by simp [← Quotient.mk_smul])

/-- (L, B, χ) is an Appell–Humbert datum with positive Riemann form, and χ has finite order on
L: χⁿ = 1 there for some n ≠ 0. -/
structure IsAmpleType (χ) extends isAppellHumbert : IsAppellHumbert B χ, isPosRiemann :
  IsPosRiemann B where finite_order : ∃ n ≠ 0, ∀ l ∈ L, χ l ^ n = 1

variable (v)

/-- The size of f at a vector x torsion modulo L: the valuation v of the value at 0 of the
translate `RealComplexForm.thetaShift` of f by x. -/
noncomputable def LatticeForm.sizeAt f (x : torsionPoints L) := v (B.thetaShift x f 0)

/-- The norm ‖f‖: the supremum of the size `LatticeForm.sizeAt` of f over all vectors torsion modulo
L. -/
noncomputable abbrev LatticeForm.thetaNorm (B : LatticeForm L) v f := iSup (B.sizeAt v f)

/-- The sizes of degree B: the functions `LatticeForm.sizeAt` of theta functions f for B and some
multiplier χ satisfying `IsAmpleType`. -/
inductive LatticeForm.sizes : Set (torsionPoints L → ℝ≥0) | of_mem_thetaSpace {χ f} :
  IsAmpleType B χ → f ∈ B.thetaSpace χ → sizes (B.sizeAt v f)

/-- Good reduction of V/L at v: for all polarisations B, C and twisted theta functions f, g of these
degrees, the sup norm of fg is the product of the norms. -/
def HasMultiplicativeNorm L := ∀ ⦃B C : @LatticeForm V _ L⦄ ⦃φ ψ⦄, φ ∈ B.sizes v → ψ ∈ C.sizes v →
  iSup (φ * ψ) = iSup φ * iSup ψ

/-- The conditions of `IsAmpleType`, with NL^∨ ⊆ L for some natural N with v(N) = 1, r > 1 with
v(r) = 1, and multiplicative sup norm (`HasMultiplicativeNorm`). -/
structure HasGoodReduction (χ) (v : Valuation ℂ ℝ≥0) (r : ℕ) extends IsAmpleType B χ where
  dual_torsion : ∃ N : ℕ, v N = 1 ∧ ∀ a ∈ B.dualLattice, N • a ∈ L
  val_eq_one : v r = 1
  one_lt : 1 < r
  hasMultiplicativeNorm : HasMultiplicativeNorm v L

/-- The torsion vector w has defect at most C in degree B: every size φ of degree B satisfies
φ(y)² ≤ C sup_x φ(x) φ(x + w) for all y. -/
def LatticeForm.HasShiftBound w C := ∀ φ ∈ B.sizes v, ∀ y, φ y ^ 2 ≤ C * ⨆ x, φ x * φ (x + w)

variable {v : Valuation ℂ ℝ≥0} {B B' : LatticeForm L} {χ : V → ℂ} {g : V → ℂ}
  {φ : SubmoduleElem (torsionPoints L) → NNReal} {ψ : SubmoduleElem (torsionPoints L) → NNReal}
  {C : NNReal} {n : ℕ} {f : V → ℂ} {x y w : torsionPoints L}

@[simp] lemma sizeAt_mul : (B + B').sizeAt v (f * g) =
  B.sizeAt v f * B'.sizeAt v g := by ext; simp [LatticeForm.sizeAt]

lemma sizeAt_pow : (n • B).sizeAt v (f ^ n) = B.sizeAt v f ^ n := by ext; simp [LatticeForm.sizeAt]

lemma valuation_eq_one_of_pow_eq_one {ζ} (hn : n ≠ 0) (h : ζ ^ n = 1) :
  v ζ = 1 := by simpa [hn] using congr(v $h)

lemma IsAppellHumbert.valuation_exp_riemannForm (hB : IsAppellHumbert B χ) : ∀ a b :
  torsionPoints L, v (exp (Real.pi * I * B.riemannForm a b)) = 1
  | ⟨_, _, _, h⟩, ⟨_, _, _, k⟩ =>
    valuation_eq_one_of_pow_eq_one (by aesop) (hB.exp_riemannForm_pow_eq_one h k)

lemma IsAppellHumbert.sizeAt_thetaShift (hB : IsAppellHumbert B χ) (w x : torsionPoints L) :
    B.sizeAt v (B.thetaShift w f) x = B.sizeAt v f (x + w) := by simp [LatticeForm.sizeAt,
  hB.thetaShift_thetaShift, hB.valuation_exp_riemannForm]

lemma factorsThrough_mkQ_of_mem_sizes : φ ∈ B.sizes v → Function.FactorsThrough φ (L.mkQ ·)
  | ⟨⟨A, _, n, o, c⟩, T⟩, x, y, h => add_sub_cancel y x ▸ A.sizeAt_thetaShift .. ▸ by
    simp [thetaShift_of_mem T, valuation_eq_one_of_pow_eq_one o, c, LatticeForm.sizeAt,
      SModEq.sub_mem.1 h]

lemma mul_shift_mem_sizes : φ ∈ B.sizes v → ψ ∈ B'.sizes v → ∀ w, (fun x ↦ φ x * ψ (x + w)) ∈ (B +
  B').sizes v | ⟨⟨a, p, n, _⟩, b⟩, ⟨⟨c, q, m, _⟩, d⟩,
  ⟨w, r, o⟩ => by simpa [← c.sizeAt_thetaShift] using! LatticeForm.sizes.of_mem_thetaSpace ⟨a.add
  (.shift w), by simp_all [pr_iff, add_pos], n * m * r, by aesop,
  fun l h ↦ by simpa [mul_pow, pow_mul, pow_right_comm _ n, ← exp_nsmul, *, mul_assoc] using
  (c.exp_riemannForm_pow_eq_one (nsmul_mem h (n * m)) o.2)⟩ (mul b (c.thetaShift_mem d w))

variable [IsFullRankLattice L]

lemma finite_range_nsmul_torsion {α} {p : torsionPoints L → α} (hn : n ≠ 0) (h : p.FactorsThrough
  (L.mkQ ·)) : (range fun x : L.comap (n • (torsionPoints L).subtype) ↦ p x).Finite := .subset
  (.image _ (finite_of_fg_torsion (L.map (L.mkQ ∘ₗ ((n⁻¹ : ℂ) • 1))) fun ⟨_, l, k, rfl⟩ ↦
  ⟨⟨n, by simpa⟩, by simpa [← Quotient.mk_smul, ← smul_assoc, *]⟩)) (range_subset_iff.2
  (⟨_, ⟨_, ·.2, by simp [← Nat.cast_smul_eq_nsmul ℂ, *]⟩, h.extend_apply (p ∘ 0) _⟩))

/-- A lattice L of full rank in V is cocompact. -/
lemma isCocompact_of_isFullRankLattice : L.toAddSubgroup.Cocpt :=
  ⟨_, isCompact_closedBall 0 _, fun x ↦ ⟨_, ((finBasis
  ..).ofZLatticeBasis_span ℝ).le (-floor ..).2, by simpa [neg_add_eq_sub] using! norm_fract_le ..⟩⟩

/-- A continuous f on V is zero if there are complex-linear d arbitrarily close to 0, each with
a left inverse c such that f vanishes on c⁻¹L: lattices of arbitrarily small mesh are dense. -/
lemma eq_zero_of_small_mesh (hf : Continuous f) (h : ∃ᶠ d : V →L[ℂ] V in nhds 0, ∃ c : V →L[ℂ] V,
  (∀ y, c (d y) = y) ∧ ∀ y, c y ∈ L → f y = 0) : f = 0 := isCocompact_of_isFullRankLattice (L :=
  L).elim fun _ ⟨K, o⟩ ↦ funext fun z ↦ by_contra fun _ ↦ h ((K.eventually_forall_mem (f <|
  z - · ·) {0}ᶜ (by aesop)).mono fun d k ⟨c, _⟩ ↦ (o (c z)).elim (by aesop))

/-- For a full lattice L in a finite-dimensional complex vector space V, an entire function on V
that vanishes at every vector of finite order modulo L is zero. -/
lemma eq_zero_of_torsionPoints (hf : Differentiable ℂ f) (h : ∀ x : torsionPoints L, f x = 0) :
    f = 0 := eq_zero_of_small_mesh hf.continuous
    ((tendsto_algebraMap_inv_atTop_nhds_zero_nat (𝕜 := ℝ) _).frequently ((eventually_ne_atTop
    0).frequently.mono fun n o ↦ ⟨n, by simp [← smul_assoc, o], (h ⟨·, n, o, ·⟩)⟩))

omit [IsFullRankLattice L] in
lemma LatticeForm.HasShiftBound.of_doubling {ι} (B : ι → LatticeForm L) (w : ι →
  _) : let P D := ∀ i, (B i).HasShiftBound v (w i) D
  Nonempty (Subtype P) → (∀ D, P D → ∀ i, (B i + B i).HasShiftBound v (w i) (D * C)) → P C := by
  intro P _ h; have m := (le_iInf_mul fun C : Subtype P ↦ C.2 · · · ·)
  exact (m · · · · |>.trans (mul_le_mul_left (by nlinarith [le_sqrt_iff_sq_le.1 (ciInf_le'
    (@Subtype.val _ P) ⟨sqrt (_ * C), fun i φ k ↦ by
    simpa [← sq, ← le_sqrt_iff_sq_le, sqrt_mul] using h _ m i _ (mul_shift_mem_sizes k k 0)⟩)]) _))

/-- For a full lattice L in a finite-dimensional complex space V and an ℝ≥0-valued valuation v
on ℂ, every size φ of degree B is bounded above on the torsion points of V/L. -/
lemma bddAbove_of_mem_sizes : φ ∈ B.sizes v → BddAbove (range φ) :=
  fun (.of_mem_thetaSpace (f := g) G@⟨A, s, n, _⟩ T@⟨_, _⟩) ↦ by
  obtain ⟨Q, _⟩ := A.nsmul (4 * n), s.nsmul (by lia : 4 * n ≠ 0)
  obtain ⟨⟨N, p, k⟩, t, ht, c, H⟩ := Q.exists_nsmul_mem_of_mem_dualLattice,
    (mem_span_image_iff_exists_fun ℂ).1 ((eq_or_ne g 0).elim (by simp_all) fun h ↦
    Q.thetaSpace_le_of_thetaShift_mem ⟨by fun_prop, by
    simp_all [mul_pow, pow_mul', ofNat_smul_eq_nsmul, nsmul_mem, ← exp_nsmul]; grind⟩
    (pow_ne_zero n ((MulAction.surjective₀
    (two_ne_zero' ℂ)).injective_comp_right.ne h)) _ (image_subset_iff.1 subset_span) (pow T _))
  use 1 ⊔ iSup (v ∘ c), fun _ ⟨⟨x, m, q, o⟩, j⟩ ↦ j ▸ (fun b ↦ (b ⟨_, by
    simp [*, mul_smul, nsmul_mem]⟩).trans (le_max_iff.2 ((le_or_gt ..).imp_right fun h ↦
    (mul_le_mul_iff_right₀ (pow_pos h.pos n)).1 ((pow_le_pow_right₀ h.le (by omega : n < 4 * n)
    ).trans ((iSup_pow ..).trans_le (ciSup_le' fun z ↦ (sizeAt_pow.ge _).trans ?_))))))
    (le_ciSup (finite_range_nsmul_torsion (mul_ne_zero p q) (factorsThrough_mkQ_of_mem_sizes ⟨G,
    T⟩)).bddAbove)
  grw [← H, LatticeForm.sizeAt, map_sum, Finset.sum_apply, v.map_sum_le fun i _ ↦
    (fun K ↦ ?_) (k _ (ht i.2))]
  grw [← map_smul, ← LatticeForm.sizeAt, Q.sizeAt_thetaShift ⟨_, N, p, K⟩, ← Finite.le_ciSup _ i,
    ← b (2 • (z + ⟨⟨_, N, p, K⟩, by simp [mul_nsmul, nsmul_mem K]⟩))]
  simp [LatticeForm.sizeAt, thetaShift, ↓two_smul, mul_pow, ← map_pow, ← exp_nsmul]; ring; rfl

lemma size_le_iSup (h : φ ∈ B.sizes v) x : φ x ≤ iSup φ := le_ciSup (bddAbove_of_mem_sizes h) x

/-- Let φ, ψ be sizes of degrees B, B' and x, y, w torsion modulo L. If `LatticeForm.HasShiftBound`
holds in degree B + B' for y − x − w with constant 1, then φ(x)ψ(y) ≤ sup_z φ(z)ψ(z + w). -/
lemma mul_le_iSup_of_hasShiftBound (hφ : φ ∈ B.sizes v) (hψ : ψ ∈ B'.sizes v) (h :
  (B + B').HasShiftBound v (y - x - w) 1) : φ x * ψ y ≤ ⨆ z, φ z * ψ (z + w) := let d := y - x - w
  match mul_shift_mem_sizes hφ hψ, d.2 with
    | m, ⟨n, o, k⟩ => not_lt.1 fun q ↦ (strictMono_nat_of_lt_succ (f := fun k ↦ ⨆ z,
      φ z * ψ (z + (w + k • d))) (Nat.rec (.trans_le (by simpa [d]) (size_le_iSup (m _) x))
      fun k i ↦ lt_of_mul_lt_mul_right' ((mul_lt_mul_of_pos_left i i.pos).trans_le (by
                 grw [← sq, iSup_pow, ciSup_le' (h _ (m _)), mul_iSup_le fun z ↦ ?_]
                 grw [← size_le_iSup (m _) z, ← size_le_iSup (m _) (z + d)]
                 grind [succ_nsmul, Eq.le]))) o.pos).ne congr(⨆ z,
      _ * $(factorsThrough_mkQ_of_mem_sizes hψ (by simpa [← Quotient.mk_smul])))

omit [IsFullRankLattice L] in
lemma IsAmpleType.nsmul (G : IsAmpleType B χ) (hn : n ≠ 0) : IsAmpleType (n • B) (χ ^ n) :=
  ⟨G.1.nsmul n, G.2.nsmul hn, G.3.imp (by simp_all [pow_right_comm _ n])⟩

lemma IsAmpleType.thetaNorm_pos (G : IsAmpleType B χ) (hf : f ∈ B.thetaSpace χ) (h :
  f ≠ 0) : 0 < B.thetaNorm v f := by simpa [LatticeForm.sizeAt, thetaShift,
  lt_ciSup_iff, bddAbove_of_mem_sizes ⟨G, hf⟩, v.pos_iff] using h ∘ eq_zero_of_torsionPoints hf.1

/-- Let (B, χ) satisfy `IsAmpleType` and B − B' have positive Riemann form. If φ(y)² ≤ C·sup_x
φ(x)φ(x + w) for the sizes φ of theta functions for (B, χ), then the same holds for all
sizes of degree B'. -/
lemma LatticeForm.HasShiftBound.of_isPosRiemann_sub (G : IsAmpleType B χ) (P : IsPosRiemann
  (B + -B')) (h : ∀ f ∈ B.thetaSpace χ, ∀ y, B.sizeAt v f y ^ 2 ≤ C * ⨆ x, B.sizeAt v f x * B.sizeAt
  v f (x + w)) : B'.HasShiftBound v w C := fun φ hφ@⟨⟨K, _, m, _⟩, T⟩ x ↦ IsAmpleType.mk
  (G.add K.neg) P (G.3.imp' (· * m) (by simp_all [mul_pow, pow_mul, pow_right_comm])) |> fun H ↦ by
  obtain ⟨⟨g, hg, g0⟩, N, _, n⟩ := H.exists_theta_ne_zero,
    G.exists_nsmul_mem_of_mem_dualLattice (hp := G.2)
  grw [← mul_le_mul_iff_left₀ (pow_pos (H.thetaNorm_pos hg g0) 2), iSup_pow, mul_iSup_le fun s ↦ ?_]
  let u : torsionPoints L :=
    ⟨(B.riemannForm.toDual G.nondegenerate).symm (B'.riemannForm (s - x)), (s - x).2.imp' (N * ·)
    fun r o ↦ ⟨by aesop, mul_smul N r (_ : V) ▸ n _ (by simpa using K.le_dualLattice o.2 ·)⟩⟩
  grw [← mul_pow, (by simpa [↓sizeAt_mul, ↓K.sizeAt_thetaShift,
    H.sizeAt_thetaShift, ↓Pi.mul_apply] using ((by simp : B' + (B + -B') = B) ▸ h :) _ ((mul
    (K.thetaShift_mem T ↑(u - (s - x))) (H.thetaShift_mem hg u)).imp id
    fun k l m ↦ by have := K.ne_zero m; simp [↓k, u, riemannForm_swap _ l, m,
    exp_sub, field, mul_sub,
    exp_add, mul_add]) (s - u) :), ← iSup_pow, sq, mul_assoc, ciSup_le' fun _ ↦ ?_]
  grw [mul_mul_mul_comm, add_right_comm, size_le_iSup (mul_shift_mem_sizes hφ hφ _)]
  gcongr <;> apply size_le_iSup ⟨H, hg⟩

omit [IsFullRankLattice L] in
/-- If (B, χ) satisfies `IsAmpleType`, then for any form A and all large m, m ≠ 0 and mB − A has
positive Riemann form. -/
lemma IsAmpleType.eventually_isPosRiemann_smul_sub (G : IsAmpleType B χ) A : ∀ᶠ m : ℕ in atTop,
  m ≠ 0 ∧ IsPosRiemann (m • B + -A) :=
  (eventually_ne_atTop 0).mp (.mono (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ).zero_smul_const A
  G.eventually_add_neg) fun m H n ↦ by simpa [← smul_assoc, n] using H.nsmul n)

variable {B : LatticeForm L} {χ : V → ℂ} [hB : IsAppellHumbert B χ] [hp : IsPosRiemann B]

/-- Let B be positive, a_s (s ∈ T finite) dual lattice points that each dual translation
permutes modulo L, and h = ⌊√[L^∨ : L]⌋. Theta functions f, g satisfy h·Σ_s
(U_{−a_s}g)(z)·(U_{a_s}f)(w) = |T|·f(z)g(w), with U = `RealComplexForm.thetaShift`.

Known result: Schur orthogonality for the theta group of a polarised complex torus. -/
lemma IsAppellHumbert.sum_shift_mul_shift T [Fintype T] (a : T → B.dualLattice) (ha : ∀ t, ∃ e :
  T ≃ T, ∀ s, (t + a s - a (e s)).1 ∈ L) (f g : B.thetaSpace χ) z w :
  (L.toAddSubgroup.relIndex B.dualLattice.toAddSubgroup).sqrt * ∑ s, B.thetaShift
  (-a s) g z * B.thetaShift (a s) f w = Fintype.card T * f.1 z * g.1 w := by
  have i s := by simpa using (hB.thetaShift_thetaShift (-s) s (f := ·))
  obtain ⟨⟨-, r, p⟩, c, E⟩ := hB.finrank_sq_eq_relIndex,
    schur_lemma (Q := ∑ s, (LinearMap.domRestrict (LinearMap.proj z ∘ₗ B.thetaShift (-a s))
    _).smulRight (thetaShiftEnd (a s) f)) fun t ↦ LinearMap.ext fun x ↦ (ha t).elim fun e j ↦ by
    simpa [Subtype.ext_iff] using Fintype.sum_equiv e _ _ fun s ↦
      i (-a s) x ▸ by simp [hB.thetaShift_thetaShift t, thetaShift_mem_of_dual, smul_smul, mul_comm,
      (by simpa using hB.thetaShift_add_mem (f := ·) · (a (e s)) (j s)), *]
  rcases finite_of_finrank_pos p, congr(($E g).1 w), congr(LinearMap.trace _ _ $E)
  simp_all [← r, -E, field]

/-- Let B be positive, N·L^∨ ⊂ L with N and all c(a)c(−a) units of the valuation ring O. For
finite non-zero theta families f_i, g_k and some γ ≠ 0, an O-module stable under the c(a)U_a
(a ∈ L^∨) contains all g_k iff all γf_i. -/
lemma IsAppellHumbert.exists_proportional_orbit_lattice {O} [CommRing O] [IsDomain O]
  [ValuationRing O] [Algebra O ℂ] [IsFractionRing O ℂ] {ι κ : Type} [Finite ι] [Finite κ] (f : ι →
  B.thetaSpace χ) (g : κ → B.thetaSpace χ) i k (c : V → ℂ) {N : ℕ} (n : IsUnit (N : O)) (t :
  ∀ a ∈ B.dualLattice, N • a ∈ L) (f0 : f i ≠ 0) (g0 : g k ≠ 0) (hc : ∀ a ∈ B.dualLattice, ∃ e : Oˣ,
  algebraMap O ℂ e = c a * c (-a)) : ∃ γ ≠ (0 : ℂ), ∀ M : Submodule O _, (∀ a ∈ B.dualLattice,
  ∀ x ∈ M, c a • B.thetaShift a x ∈ M) → ((∀ k, (g k).1 ∈ M) ↔ ∀ i, γ • (f i).1 ∈ M) := by
  let H := (L.submoduleOf B.dualLattice).toAddSubgroup
  obtain ⟨⟨z, j⟩⟩ := Function.ne_iff.1 (Subtype.ext.mt f0),
    H.fintypeOfIndexNeZero (by nlinarith! [hB.finrank_sq_eq_relIndex])
  let A (s : _ ⧸ H) := c (-s.out) • hB.thetaShiftEnd (-s.out)
  have P {ι k} [Finite ι] {g : ι → _} (h : g k ≠ 0) := let u (p : ι × _) := (A p.2 (g p.1)).1 z
    (@Finite.exists_max _ _ _ ⟨k, 0⟩ _ (ValuationRing.valuation O ℂ <| u ·)).imp fun a v ↦
    have o (M : Submodule O _) (x : thetaSpace ..) (s : ∀ r : _ ⧸ H, _ → c r.out • B.thetaShift
      r.out (u a • x) ∈ M) j : x.1 z • (g j).1 ∈ M := (M.smul_mem_iff_of_isUnit (isUnit_of_dvd_unit
      (card_dvd_exponent_nsmul_rank' (_ ⧸ H) (Quot.ind ((eq_zero_iff _).2 <| t _ ·.2))).natCast
      (by simp [n.pow]))).1 (Eq.subst (by
      ext; simp [← mul_assoc, A, u, @Algebra.smul_def O,
      ← sum_shift_mul_shift (_ ⧸ H) (·.out) (⟨.addLeft ·, fun _ ↦ eq_iff_sub_mem (N :=
      H).1 (by simp)⟩)]; congr!; grind [algebraMap.coe_eq_zero_iff, Units.ne_zero])
      (nsmul_mem (M.sum_smul_mem (fun r ↦ (hc _ r.out.2).choose⁻¹ * (v (j, r)).choose) s) _))
    And.intro (mt (fun _ : u a = 0 ↦ o ⊥ (f i) (by simp_all) k) (by simp_all)) o
  obtain ⟨⟨a, q, Q⟩, b, p, P⟩ := P f0, P g0
  exact ⟨_, by simpa using ⟨q, p⟩, fun M s ↦ ⟨fun h ↦ Q M _ ((smul_inv_smul₀ q _).substr
    (by bound)), fun h ↦ by simpa [*, inv_mul_eq_div] using P M _ ((smul_inv_smul₀ p (A _
    ((_ : ℂ) • _))).substr fun r _ ↦ s _ r.out.2 _ (s _ (-a.2.out).2 _ (h a.1)))⟩⟩

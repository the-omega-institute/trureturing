/- GID: D5/S3/Zeros/GRH/Lib/Adelic/CuspForms/CuspStep
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Adelic/CuspForms/CuspStep
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Adelic.CuspForms.CuspStep. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Adelic/CuspForms/CuspStep.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Adelic.CuspForms.Petersson
import D5.S3.Zeros.GRH.Lib.Weil.MixedModel.AdaptedSplitting
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Cusp forms: rapid decay, finite dimension, Poincaré series; algebraic modular forms
(known result; see Lib.Adelic.CuspForms.Petersson).

This file: Parametrisation and product rule of the unipotent radical; norm bounds for integral
matrices. Deep in the cusp a cuspidal function is bounded by its oscillation, explicit depth. -/
seal Finset.univ Finset.sum Finset.prod

open Finset Fintype G Matrix NumberField RightActions Submodule Norms.L2Operator

namespace Reduction

variable {n R} [Fintype n] [CommRing R] [StarRing R] {J a y e : Matrix n n R} (J' T : Matrix n n R)

/-- For n × n matrices J, T over a commutative ring with involution, the matrix 1 + 2(T − Tᴴ −
TᴴJT)J. -/
noncomputable def radicalElem := 1 + 2 * ((T - Tᴴ - Tᴴ * J' * T) * J')

attribute [scoped simp] radicalElem two_mul mul_sub mul_add sub_mul add_mul mul_assoc

/-- Let J be hermitian invertible, aᴴJa = aᴴJy = 0, ye + 2bsaᴴJ = 1, (u, 1) ∈ `dilationGroup` a, r
any map. For some c, d, x = ex((a·r(d) − y·r(c))saᴴ) is unitary, (x, 1) ∈ `dilationGroup` a, xu =
ex((y(c − r(c)) − a(d − r(d)))saᴴ), ex = `Reduction.radicalElem`. -/
lemma radicalElem_spec {u : U J} (hu : (u, 1) ∈ dilationGroup a) (hJ : Jᴴ = J) (hJ' : IsUnit J) b s
  (r : _ → _) (ha : aᴴ * (J * a) = 0) (hy : aᴴ * (J * y) = 0) (h : y * e + 2 * b * s * aᴴ * J = 1) :
  ∃ c d, let x := radicalElem J ((a * r d - y * r c) * s * aᴴ)
  ∃ h, (U.of hJ' x h, 1) ∈ dilationGroup a ∧ x * u =
    radicalElem J ((y * (c - r c) - a * (d - r d)) * s * aᴴ) :=
  have R {w} (g : aᴴ * (J * w) = 0) (z : Matrix n n R) := by simpa [← eq_sub_iff_add_eq, hJ, hu.1]
    using congr(($h, $g, $gᴴ, $(u.2), $(u.2) * a, ($(u.2) * a)ᴴ, $hᴴ) <• z)
  let c := e * (u - 1 - a * (b * s)ᴴ * J * u) * b
  have : u = radicalElem J (y * c * s * aᴴ) := hJ'.mul_left_cancel (hJ'.mul_right_cancel (by
    linear_combination (norm := (simp [c, R ha]; grind))
      (e - 2 * c * s * aᴴ * J)ᴴ * hu.2 _ _ hy hy * e * J))
  ⟨c, -(y * r c * s)ᴴ * J * y * c, by simp +contextual [dilationGroup, Subgroup.ofDiv, *]; grind
    [R hy 1]⟩

variable {E} [Field E] [CMType E] {r} {a : Matrix n n (𝔸 E)} (r') (a' : Matrix n n (𝔸 E))

/-- The adelic matrix a is integral at all finite places and has operator norm at most r at each
infinite place. -/
def IsIntBounded := (RingHom.snd ..).mapMatrix a' ∈ (Ô E).matrix ∧ ∀ w, ‖(evalInf w).mapMatrix a'‖ ≤
  r'

lemma IsIntBounded.star (h : IsIntBounded r a) :
    IsIntBounded r aᴴ := ⟨fun _ _ ↦ star_mem_Ô (h.1 _ _), ((norm_star _).trans_le <| h.2 ·)⟩

lemma IsIntBounded.nsmul (h : IsIntBounded r a) (M : ℕ) :
    IsIntBounded (M * r) (M • a) := ⟨nsmul_mem h.1 M, (by grw [map_nsmul, norm_nsmul_le, h.2 ·])⟩

lemma IsIntBounded.mul_and_sub {b t} (h : IsIntBounded r a) : IsIntBounded t b →
  IsIntBounded (r * t) (a * b) ∧ IsIntBounded (r + t) (a - b) := by
  grind [IsIntBounded, mul_mem, sub_mem, norm_mul_le_of_le, norm_sub_le]

variable (E n : Type) [Field E] [CMType E] [Fintype n] (N : ℕ) {s} {V : Space E n s} {F B}
  {e : GInf E s → ℂ}

/-- The real number 8fn·rd(E) + 12n⁶[E:ℚ]²N + 1, with f the number of infinite places of E,
rd(E) its root discriminant and n the rank. -/
noncomputable def _root_.cuspConst := 8 * (numInfPlaces E * card n) * rootDiscr E +
    (48 * card n ^ 6 * numInfPlaces E ^ 2 * N + 1)

lemma _root_.one_le_cuspConst : 1 ≤
  cuspConst E n N := by rw [cuspConst, rootDiscr, ← add_assoc]; bound

open Reduction

attribute [local simp] diagonal_natCast Matrix.map_add Matrix.map_natCast Matrix.map_sub
  IsIntBounded Space.map_J

variable {E n}

/-- Let F be a form of level K(M), its type a cusp kernel, N ≠ 0 in the different, κ =
`cuspConst`, 0 < δ ≤ 1, λ(g) < (δ/(Mκ²))ⁿ. If |F(gx) − F(g)| ≤ C for real x with all ‖x_w −
1‖ ≤ δ, then |F(g)| ≤ C. -/
lemma _root_.Space.IsForm.norm_le_of_firstMinimum_lt (hF : V.IsForm e F) (he :
  IsCuspKernel B e) {N} [NeZero N] (hN' : ↑N ∈ differentIdeal ℤ (𝓞 E)) {M : ℕ} (hM : M ≠ 0) (hK :
  HasLevel F (principalLevel n M)) {δ} (h0 : 0 < δ) (h1 : δ ≤ 1) {g C} (h :
  (V.move g).firstMinimum < (δ / (M * cuspConst E n N ^ 2)) ^ card n)
  (c : ∀ x, dist x 1 ≤ δ → ‖F (g * (x, 1)) - F g‖ ≤ C) : ‖F g‖ ≤ C := by
  have z := one_le_cuspConst E n N
  set W := V.move g
  set κ := cuspConst E n N with q
  have ⟨u, v⟩ : δ / (M * κ ^ 2) * κ ∈ Set.Icc 0 1 :=
    ⟨by bound, by grw [h1]; field_simp; bound [hM.pos]⟩
  -- The cusp, from a short vector and the sorted basis of Minkowski's second theorem.
  obtain ⟨p, ⟨Y, x, ⟨d, hy⟩, hx⟩, ξ, hξ, h₀, h⟩ := rootDiscr_pos E, minkowski_second W.x, by
    simpa using mt W.le_firstMinimum_iff.2 h.not_ge ∘ .intro (by grw [h1]; bound [hM.pos])
  have P := (Function.ne_iff.1 h₀).nonempty
  grw [Space.ideleAbs_det_x, one_mul, show _ * _ ≤ κ by rw [q, cuspConst]; bound, ← zpow_natCast,
    zpow_comm, le_self_pow₀ z two_ne_zero, ← pow_mul, ← mul_assoc, pow_mul'] at hx
  have I (f : E ≃+* E) := linearIndependent_rows_of_det_ne_zero (mt (f.map_det Y).trans (by simpa))
  let Z : _ → {y ∈ W.baseLattice | y ≠ 0} := Option.elim' ⟨ξ, hξ, h₀⟩ fun j ↦
    ⟨_, (hy j).1, (I 1).ne_zero j⟩
  let l o := ‖W.archCoords (Z o).1‖
  have ⟨σ, μ⟩ : ∃ σ : _ ≃ _, Monotone (l <| σ ·) :=
    ⟨.trans _ (Fintype.equivFinOfCardEq card_option).symm, Tuple.monotone_sort (l ∘ _)⟩
  set m := (l <| σ ·)
  have ⟨i, o, r⟩ : ∃ i, m i ≤ m i.rev ∧ m i * m i.rev < δ / (M * κ ^ 2) * κ := by
    obtain ⟨i, hi⟩ : ∃ i, m i * m i.rev < δ / (M * κ ^ 2) * κ := by
      simpa using mt (prod_le_prod₀ (s := univ) (g := fun i ↦ m i * m i.rev) fun _ _ ↦ u) (by
        grw [not_le, prod_mul_distrib, Fin.rev_bijective.prod_comp, ← sq, σ.prod_comp l,
          Fin.prod_const, prod_option, @id (l (some _) ≤ _) (hy _).2, ← zpow_sum_of_ne_zero,
          le_of_pow_le_pow_left₀ _ _ hx, @id (l none < _) h, ← mul_pow, ← pow_mul,
          pow_le_pow_of_le_one u v] <;> first | positivity | grind [card_pos_iff])
    exact (le_total ..).elim (⟨i, ·, hi⟩) fun h ↦ ⟨i.rev, by simpa, by simpa [mul_comm] using hi⟩
  let X k := (of fun a ↦ (Z (σ (k ⊓ σ.symm (some a)))).1)ᵀ
  have L k (o : m k ≤ m i.rev) : (X i)ᴴ * (W.J * X k) = 0 := funext₂ fun _ _ ↦
    Space.form_eq_zero_of_norm_mul_lt_one (Z _).2.1 (Z _).2.1 (by grw [← v, ← r, ← o]; bound)
  have R (f : E ≃+* E) k : k ≤ ((X k)ᵀ.map f).rank := by
    grw [← rank_submatrix_le _ ((↑) : (σ.finsetCongr (Iic k)).eraseNone → n) id,
      LinearIndependent.rank_matrix, card_coe, card_eraseNone_eq_card_erase, card_erase_eq_ite]
    bound; convert! (I f).comp _ (@Subtype.ext _ _); clear * -; aesop (add simp min_eq_right)
  have ⟨e, b, hb⟩ := exists_mul_add_mul_eq (x := (X i)ᴴ * W.J) (y :=
    X i.rev) (eq_of_le_of_finrank_le (by simp [L, IsConcreteLE.le_iff]) (by
    simpa [Nat.sub_add_cancel i.is_le, ↓← isUnit_iff_isUnit_det,
      ↓← card_sub_rank] using! add_le_add (R 1 i.rev) (R starRingAut i))).ge
  let A k := W.x⁻¹.1 * (X k).map toAdele
  have S k o := (by simpa [A] using congr($(L k o).map toAdele) : (A i)ᴴ * (stdForm E s * A k) = 0)
  have T k : IsIntBounded _ (A k) := ⟨fun _ _ ↦ (Z _).2.1 _, fun w ↦
    l2_opNorm_le_of_apply fun b a ↦ (PiLp.norm_apply_le _ (w, b)).trans (μ inf_le_left)⟩
  -- Reduction in the radical of the cusp.
  obtain ⟨b, rfl⟩ := ((by simpa : IsUnit (2 * M : E)).map (algebraMap ..)).dvd (a := b)
  refine hF.norm_le_of_dist_le he (S i o) (fun _ e ↦ (Z _).2.2
    (W.eq_zero_of_vecAtPoint_fst congr($eᵀ P.some))) (.prod (isCompact_closedBall 1 δ) (IsLevel.mk
    principalLevel_le_Kf (isOpen_principalLevel (a := M) (by simpa))).isCompact) (fun _ ⟨b,
    d⟩ ↦ by simpa [dist_eq_norm, ← hK _ d (g * (_, 1))] using c _ b) fun u ↦ ?_
  choose f ha hf using Prod.forall'.2 (exists_rat_near_of_mem_differentIdeal NeZero.out hN')
  have k c : IsIntBounded (n := n) _ (c - c.map (toAdele ∘ f)) :=
    ⟨(ha <| c · ·), fun _ ↦ l2_opNorm_le_of_apply fun _ _ ↦ by simpa using hf ..⟩
  have ⟨c, d, h₁, h₂, h₃⟩ :=
    radicalElem_spec u.2 (by simp) (by simp) (W.x⁻¹ * b.map toAdele) M (·.map (toAdele ∘ f))
    (S i o) (S _ le_rfl) (by simpa [A, M.cast_comm] using congr(W.x⁻¹ * ($hb).map toAdele * W.x))
  have hs : IsIntBounded 1 (stdForm E s) := by simp [stdForm, pi_norm_le_iff_of_nonneg]
  refine ⟨⟨ofMat _ h₁, h₂⟩, W.mem_Γ_iff_range.2 (mem_ratMatrices.1 ⟨radicalElem W.J ((X i * d.map f
    - X i.rev * c.map f) * M * (X i)ᴴ), by simp [A, ↓Subgroup.coe_subtype, ← Matrix.map_map]⟩), ?_⟩
  set x := _ * u.1
  have h : IsIntBounded (δ / 6 / M) _ := ((((T i.rev).mul_and_sub (k c)).1.mul_and_sub
    ((T i).mul_and_sub (k d)).1).2.mul_and_sub (T i).star).1.imp id (· · |>.trans ?_)
  grw [o]; field_simp at *
  grw [← r, q, cuspConst, ← p]; ring_nf; bound
  have ⟨Z, hZ, e⟩ : ∃ Z, IsIntBounded _ Z ∧ x.mat - 1 = M • Z := ⟨_,
    (((h.mul_and_sub h.star).2.mul_and_sub ((h.star.mul_and_sub hs).1.mul_and_sub
    (h.nsmul M)).1).2.mul_and_sub hs).1.nsmul 2, by erw [mat_mul, h₃]; simp [M.cast_comm]⟩
  obtain ⟨k, t⟩ := by simpa [← dist_eq_norm, ← e] using hZ.nsmul M
  use dist_pi_le_iff'.2 (t · |>.trans (by field_simp; bound)), by simpa [mem_Kf] using! (add_mem
    k (one_mem _)), fun i j ↦ ⟨_, hZ.1 i j, by simpa [apply_ite] using congr(($e i j).2)⟩

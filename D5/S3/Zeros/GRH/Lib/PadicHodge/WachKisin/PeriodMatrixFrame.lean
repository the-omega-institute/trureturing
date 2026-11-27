/- GID: D5/S3/Zeros/GRH/Lib/PadicHodge/WachKisin/PeriodMatrixFrame
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/PadicHodge/WachKisin/PeriodMatrixFrame
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.PadicHodge.WachKisin.PeriodMatrixFrame. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/PadicHodge/WachKisin/PeriodMatrixFrame.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.PadicHodge.WachKisin.PeriodMatrixBasis
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: Kisin lattice (Breuil–Kisin module) of a crystalline lattice. This file proves
only the existence of a free lattice of finite height inside A_inf that spans the crystalline
periods, and no equivalence of categories. The proof is direct, by linear retractions onto the
Breuil–Kisin ring, without slope theory or étale φ-modules. Source: M. Kisin, Crystalline
representations and F-crystals, Progr. Math. 253 (2006), 459–496; Bhatt–Morrow–Scholze, Integral
p-adic Hodge theory, Publ. IHÉS 128 (2018), 4.26–4.34; Cais–Liu, On F-crystalline representations,
Doc. Math. 21 (2016).

General lemmas of linear algebra and matrices (textbook or folklore).

This file: Existence of a finite-height Kisin frame in A_inf for a crystalline period matrix. -/

namespace Lift.Chart

open BPlus Algebra Matrix MulSemiringAction Function Witt RingHom Ideal Quotient PreTilt
open WittVector renaming constantCoeff → π
variable {p} [ThePrime p] {d} {c : Chart} [Fintype d]
attribute [-simp] map_smul smul_right_inj Matrix.mul_smul

/-- Let R: S → D be a homomorphism to a nontrivial semiring and X a set of vectors over S. If
R(t·x) = 0 for all x in X forces R(t) = 0, some square matrix N with rows in X has R(det N)
≠ 0. -/
lemma exists_det_ne_zero {S D} [CommRing S] [Semiring D] [Nontrivial D] (R : S →+* D) (X : Set (d →
  S)) (h : ∀ t, (∀ x ∈ X, R (t ⬝ᵥ x) = 0) → ∀ i, R (t i) = 0) : ∃ N, R (det N) ≠ 0 ∧ ∀ k, N k ∈ X :=
  (exists_maximalFor_of_wellFoundedGT _ (· · ∈ X) ⟨1, by simp⟩).imp fun N m ↦
  ⟨m.1, fun k ↦ by_contra
  fun hk ↦ m.1 (by simp [N.det_eq_sum_mul_adjugate_row k, h (N.adjugate · k) fun x h ↦ by_contra
  fun n ↦ hk (@m.2 (N.updateRow k x) (by simpa [← cramer_transpose_apply, ← adjugate_transpose,
  cramer_eq_adjugate_mulVec]) (fun l ↦ by by_cases l = k <;> simp [*]) k (by simpa))])⟩

attribute [local simp] map_smul' smul_smul mulVec_sub Set.image_pair pow_succ mul_sub Units.smul_def
  comp_def map_mulVec
attribute [local simp ←] mul_assoc mul_pow Subalgebra.smul_def OFlat.frobEnd_apply iterate_frobenius

/-- A square matrix M of determinant 0 over a valuation ring R has a kernel vector a, with some
coordinate 1, such that g(a) = a for every ring endomorphism g of R with M·g(a) = 0 (Artin's
minimal support argument). -/
lemma _root_.exists_fixed_ker {R} [CommRing R] [IsDomain R] [ValuationRing R] {M : Matrix d d R}
  (h : M.det = 0) : ∃ a ν, a ν = 1 ∧ M *ᵥ a = 0 ∧ ∀ g : R →+* R, M *ᵥ g ∘ a = 0 → g ∘ a = a := by
  have ⟨w, h, hm⟩ := exists_minimalFor_of_wellFoundedLT _ support (exists_mulVec_eq_zero_iff.2 h)
  choose ν a ha using by
    simpa [mem_span_singleton] using @Finite.exists_max _ _ _ (ne_iff.1 h.1).nonempty _ (span {w ·})
  generalize e : w ν = t at *; cases (funext ha : w = t • a)
  use a, ν, ?_, ?_, fun g h ↦ by_contra (@hm _ ⟨sub_ne_zero.2 ·, ?_⟩ ?_ ν ?_ ?_) <;> aesop

/-- For a period matrix U for (h, v) there are Q, L over A_inf, Z over S_B, Z' over B^+, B over
S with QL = τ^h, UZ = E^hQ, Z'Z = E^h, φQ = vQB, and gZ ∈ Z·M_d(A_inf) for all g fixing Λ
and θ(z).

Known result: Kisin lattice (Breuil–Kisin module) of a crystalline lattice. -/
lemma IsPeriodMatrix.exists_frame {U h v} (hU : c.IsPeriodMatrix U h v) : ∃ (Q L Z Z' :
  Matrix d d _) (B : Matrix d d c.S), Q * L = tau ^ h • 1 ∧ (∀ i j, Z i j ∈ c.bicommutant) ∧ U * Z =
  c.E.1 ^ h • Q.map ainfToBPlus ∧ Z' * Z = c.E.1 ^ h • 1 ∧ Q.map frobEnd = v • (Q * B.map (↑)) ∧
  ∀ g, c.FixesThetaZ g → ∃ G, g • Z = Z * .map G ainfToBPlus := by
  obtain ⟨⟨Q, Z, h₀, hZ, e, hN, hA⟩, ⟨⟨U', _⟩, ⟨F, -, _, -, eF⟩⟩, ⟨u, hu, eu⟩,
    ⟨t, ht⟩, q, _, eq⟩ := hU.exists_basis, id hU, c.exists_bicommutant_mul_phi_E_eq_one,
    c.associated_E_mul_tau_mu.dvd, c.exists_bicommutant_mul_p_eq_one
  have act (m : FrobGal) (ρ : Matrix d d _) F w r (h₁ : .map ρ ainfToBPlus * m • U = U * F) (h₂ :
    w * ainfToBPlus (m • c.E.1) = ainfToBPlus (c.E.1 * r)) : U * w ^ h • (F * m • Z) =
    c.E.1 ^ h • (r ^ h • ρ * m • Q).map ainfToBPlus := by
    erw [mul_smul_comm, ← mul_assoc, ← h₁, mul_assoc, ← map_mul (toRingHom _ _ m).mapMatrix]
    ext; simp [@smul_def _ BPlus, mul_apply, Finset.mul_sum, mul_left_comm (ainfToBPlus _), *]
  choose b o using (hN _ _ (fun i ↦ mul_mem (pow_mem (mul_mem (ainfToBPlus_mem_bicommutant _) hu) h)
    (sum_mem fun _ _ ↦ by apply_rules [mul_mem, frobEnd_mem_bicommutant])) congr(col $(act _
    (v⁻¹ • 1) F _ 1 (congr(_ * $eF).trans (by simp)) (by simpa using! congr(_ * $eu))) ·))
  have o : Q * bᵀ.map (↑) = _ := ext_col o
  let R := π.domRestrict c.S
  have A g H := act (1, g) _ 1 1 _ ((hU.3 g H).choose_spec.trans (by simp)) (by
    erw [one_mul, ← (c.associated_smul_E g).choose_spec])
  by_cases h₁ : ↑p ∣ Q.det
  · have H i j t : t ⬝ᵥ c.adicBasis.coord i ∘ Q j = c.adicBasis.coord i ((Q *ᵥ (t ·)) j) := by
      simp [mulVec_eq_sum, dotProduct]
    -- bounded denominators
    choose N D σ τ S using exists_det_ne_zero R {c.adicBasis.coord i ∘ Q j | (i) (j)} fun t h i ↦
      (pi_dvd_iff.2 fun j ↦ p_dvd_iff.2 ((OFlat.isHausdorff_and_shiftDiff_surjective
      (mt Ainf.isUnit_iff_isUnit_constantCoeff.2 c.4)).1.1 _ fun n ↦ .zero.2
      (mem_comap.1 ((Submodule.restrictScalars_mem ..).1 (c.adicBasis.mem_of_coord (by
      simp [Ideal.map_pow, ← map_le_iff_le_comap]; rfl) (mul_mem_right _ _ <| ker_le_comap π <| H ..
      ▸ h _ ⟨·, _, rfl⟩)))))).rec fun w hw ↦ (hN w (Z *ᵥ q • ainfToBPlus ∘ (t ·)) (fun _ ↦
      sum_mem (by simp [mul_mem, *])) (by ext; simpa [e, eq] using congr(_ • (q * ainfToBPlus
      ($hw _))))).rec fun | _, rfl => p_dvd_iff.1 ⟨_, congr($(mulVec_injective_of_det_ne_zero h₀
      (hw.trans (Q.mulVecLin.2 ..).symm)) i)⟩
    have ker {m ρ C a} (h : C = ρ * m • Q) : Q.map π *ᵥ a = 0 → C.map π *ᵥ toRingHom FrobGal _ m ∘ a
      = 0 := (by simpa [h, ← Pi.zero_def] using! congr(_ *ᵥ toRingHom _ _ m ∘ $(·)))
    -- a fixed vector of the kernel
    have ⟨a, ν, e₁, hw, hm⟩ := exists_fixed_ker (π.map_det Q ▸ p_dvd_iff.1 h₁)
    refine let K := R bᵀ.det * R N.det; (mul_ne_zero (fun H ↦ h₀ (eq_of_forall_pow_dvd_sub p (·.rec
        (by simp) fun n h ↦ (map_dvd_iff (MulEquiv.ofBijective _ frobEnd_bijective)).1 (by
      simpa [map_det, IsUnit.pow, ← det_mul, o] using! mul_dvd_mul h (p_dvd_iff.2 H)))))
      D (Perfection.ext (f := K) fun M ↦ ?_)).rec
    choose n s e using ((add_right_injective M).nat_tendsto_atTop.eventually (.all fun i ↦
      c.eventually_exists_coeff_eq_of_fixed
      (fun g hg ↦ congr($(hm _ (ker (by simpa [↓← ext_iff, smul_def, e, ↓E_ne_zero, -Matrix.map_mul]
      using ((by ext; simpa using congr($(hZ _ _ ⟨(toRingHom _ _ g).toAddHom, by
      simp [c.S.smul_def, smul_def, hg]⟩ smul_mem_amaxImage) 1) : g • Z = Z) ▸ A g
      (by simp [← theta_smul, FixesThetaZ, FixesLambda, hg ⟨_, _⟩]) :)) hw)) i)) M)).exists
    have ⟨C, hC, ha⟩ : ∃ C, K * R (det C) ∣ K ^ p ^ n ∧ Q.map π *ᵥ C.map R *ᵥ a ^ p ^ n = 0 := n.rec
      ⟨1, by simpa⟩ fun n ⟨C, h, e⟩ ↦ ⟨bᵀ * C.map c.φ, by
      grw [det_mul, map_mul, pow_succ, pow_mul, ← h, mul_pow, ← pow_dvd_pow K (Fact.out : 1 < p),
        Dvd.intro _ (refl K)]; simp [map_det]; rfl, by simpa [pow_mul, Pi.pow_def] using! ker o e⟩
    simpa [OFlat, K, mul_assoc, by simpa using (map_det ..).trans (
         det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors (funext fun k ↦
         (((coeff _).comp R).map_mulVec (N * C) ..).symm.trans (by
         erw [← mulVec_mulVec, mulVec, dotProduct_comm, ← S, H, ← mk_thetaPhiInv_eq_coeff,
           eq_add_of_sub_eq (c.exists_frobE_dvd_sub_of_dvd _ _ p _
           (by simpa [OFlat, ← eq_zero_iff_dvd, mk_thetaPhiInv_eq_coeff, mulVec_eq_sum, e] using!
           congr(coeff (M + n) ($ha _)))).choose_spec.choose_spec]
         simp [CharP.cast_eq_zero, frobE_dvd_iff.1 dvd_rfl])) ((e ν).subst (by simp [*])))]
      using! map_dvd (coeff (M + n)) hC
  have hQ {X Y} (eY : U * Y = c.E.1 ^ h • .map X ainfToBPlus) : ∃ L, Q * L = X := by
    choose a e using fun i ↦ (hA _ _ congr(col $eY ·) _ _ _ h₁ congr($Q.adjugate_mul i))
    use of a
    simp [← smul_right_inj h₀, ← mul_smul_comm, mul_adjugate, ← (ext e : _ * X = Q.det • of a)]
  choose k a w ea using (exists_Ainf_approx · 0 h)
  obtain ⟨⟨n, hn⟩, L, hL⟩ := Finite.exists_le (k ∘ U.uncurry),
    @hQ (tau ^ h • 1) U' (by simp [-map_pow, *])
  have hX : (U.map fun y ↦ p ^ (n - k y) * a y).map ainfToBPlus =
    U * ainfToBPlus p ^ n • (1 - t ^ h • U' * U.map
    w) := by ext i j; simp [*, ← pow_sub_mul_pow _ (hn (i, j))]; clear * - ea ht; grind [smul_def]
  obtain ⟨Y, rfl⟩ : Q.map ainfToBPlus ∣ U := (hQ (by rw [hX, ← mul_smul_comm])).imp' (q ^ n • ·.map
    ainfToBPlus + (t * c.E) ^ h • L.map ainfToBPlus * U.map w) (by simp +contextual [mul_add,
    ← Matrix.map_mul, *, -map_pow])
  use Q, L, Z, Y, bᵀ, hL, hZ, e, (isRegular_of_isLeftRegular_det (mul_right_injective₀
    (mt (ainfToBPlus.map_det Q).trans (by simpa)))).1 (by simpa), by simp [o]; rfl, fun g H ↦
    (hQ (A g H)).imp fun L hL ↦
    isLeftRegular_iff_mulVec_injective.2 hU.mulVec_injective (by simpa [← hL, e] using! A g H)

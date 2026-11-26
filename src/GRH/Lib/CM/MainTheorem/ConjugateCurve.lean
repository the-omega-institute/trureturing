import GRH.Lib.CM.LocalHeight.IsogenyIntegrality
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Main theorem of complex multiplication for elliptic curves, soft form (known result;
see Lib.CM.FormalGroup.FormalHeight).

This file: Conjugate CM curve, conjugation of isogenies, theta function and its torsion
translates. -/


open CMLattice PowerSeries
variable {d d'} {C D : CMLattice d} {a : ℂ} [PrimeSevenModEight d] (σ : Gal(ℂ/QuadField d))
attribute [local simp, local grind] map_ofNat quadGen_mem_quadInt θ_eq_zero_iff pow_eq_zero_iff'
  monomialSection sigma_eq_zero_iff map_ne_zero two_t_mem t_notMem add_mem_cancel_left sigmaSign
  a₁_sq g₂_eq ne_of_gt

/-- For an isogeny a: C → D of degree N, σ ∈ Aut(ℂ/K), a₁(C′) = σa₁(C), a₁(D′) = σa₁(D):
σ(a)Λ_{C′} ⊂ Λ_{D′}; σ(a)t_{C′} ∈ Λ_{D′} implies at_C ∈ Λ_D; if `PrimeSevenModEight` d′, a ≠ 0 and
σ(a): C′ → D′ has degree N, then (θ_{D′}/σθ_D)(σ(a)z) = (θ_{C′}/σθ_C)(z)^N as series. -/
lemma conj_isogeny_mem_lattice {C' D' : CMLattice d'} {N} (h : C'.a₁ = σ C.a₁) (k : D'.a₁ = σ D.a₁)
  (ha : C.IsIsogeny D.1 a N) : (∀ l ∈ C'.Λ, σ a * l ∈ D'.Λ) ∧ (σ a * C'.t ∈ D'.Λ → a * C.t ∈ D.Λ) ∧
    ∀ [PrimeSevenModEight d'], a ≠ 0 → C'.IsIsogeny D'.1 (σ a) N →
  rescale (σ a) (thetaQuotient D σ D') = thetaQuotient C σ C' ^ N := by
  choose y μ _ _ T using exists_conjugate_section σ h C'.t
  choose A p e v using (T <| C.comp_mul_mem_sections ha <| D.monomialSection_mem ·)
  have := (p · |>.1)
  have Z x := by simpa [thetaQuotient] using congr(coeff 0 $(e x))
  have J := by simpa using (congrFun (by apply eq_of_taylorAtZero_eq <;> simp (disch := fun_prop)
    [e, taylorAtZero_monomialSection σ k, ← rescale_map, -monomialSection, taylorVia]; ring) : ∀ z,
    A (0, 1, 0) z * D'.monomialSection (1, 0) (σ a * z) ^ 2 =
    D'.monomialSection (0, 1, 0) (σ a * z) * A (1, 0) z ^ 2)
  use fun l m ↦ by simpa [↓(p _).2, C'.isAppellHumbert_multiplier.ne_zero, *] using J (0 +
    l), by grind [by simpa [v] using J C'.t], fun _ H ↦ (section_division _ D' 0
    C'.sections_zero_le_const (comp_mul_mem_sections _ H D'.θ_mem) (p (1, 0))
    (by simpa : σ a ≠ 0) (by simp) (by grind)).elim fun | _, ⟨⟨c, rfl⟩, E⟩ => ?_
  simpa [taylorVia, ← rescale_map, ne_of_apply_ne (coeff 0), ← E,
    by simpa [Z] using congr(($E 0, $(taylorAtZero_monomialSection σ k (1, 0))))] using e (1, 0)

omit [PrimeSevenModEight d] in
@[simp, grind] lemma map_eq_self_of_mem_quadInt : a ∈ quadInt d → σ a = a :=
  (·.choose_spec ▸ σ.commutes _)

namespace CMLattice

/-- Let d be a prime ≡ 7 mod 8, C, D CM data for d and σ ∈ Aut(ℂ/K) with a₁(D) = σ(a₁(C)). Then
θ_D/σθ_C = 1: the Taylor series of θ_D is the σ-conjugate of that of θ_C. -/
lemma thetaQuotient_eq_one (h : D.a₁ = σ C.a₁) : thetaQuotient C σ D = 1 := by_contra fun H ↦ by
  let ⟨n, W, e⟩ := WfDvdMonoid.max_power_factor (sub_ne_zero.2 H) X_irreducible
  have K {a} m a0 : a ^ n = a * star a := have ⟨N, k⟩ := exists_isIsogeny_of_mul_mem_lattice (C.5 m)
    have := congr(coeff n $((conj_isogeny_mem_lattice σ h h k).2.2 a0
      (by simp_all [D.5]) ▸ map_sub (rescale (σ a)) _ 1))
    by simp_all [← mul_geom_sum, mul_assoc, ↓coeff_rescale, coeff_X_pow_mul', thetaQuotient,
      X_dvd_iff, field]
  simpa [by simpa [← sq] using congrArg norm ∘ @K 2 (by simp), quadGen, sq, NeZero.ne, field,
    Complex.ext_iff] using K quadGen_mem_quadInt

variable (C D)

/-- For d a prime ≡ 7 mod 8, a CM datum C and an automorphism σ of ℂ over K = ℚ(√−d), there is a
CM datum C' for the same d with a₁(C') = σ(a₁(C)). -/
lemma exists_galConjugate : ∃ C', @a₁ d C' = σ C.a₁ := by
  cases' exists_lattice_of_g₂_g₃
    (by simpa using σ.injective.ne (weierstrass_disc_ne_zero C.1)) with L
  cases' L.exists_weierstrassP_eq_of_cubic (σ (C.weierstrassP C.t)) 0 (by grind [g₃_eq]) with t
  let D :
    CMLattice 0 := by use L, t, σ C.a₁ <;> simp_all [← map_pow, ← derivWeierstrassP_eq_zero_iff]
  have I {a} m := @conj_isogeny_mem_lattice _ _ _ _ a _ σ D D _ rfl rfl
    (exists_isIsogeny_of_mul_mem_lattice (C.5 m)).choose_spec
  refine' ⟨mk L t .., rfl⟩ <;> grind [CMLattice, → conj_mem_quadInt, I quadGen_mem_quadInt]

/-- The conjugate curve: a chosen CM datum for d whose invariant a₁ is σ(a₁(C)). -/
noncomputable def galConjugate := (C.exists_galConjugate σ).choose

/-- Let d be a prime ≡ 7 mod 8, σ ∈ Aut(ℂ/K), a₁(D) = σa₁(C), Λ_C = Ω𝒪_K, S ⊂ K finite. Some v ∈
Λ_D has: for all x ∈ S, σ maps the Taylor series at 0 of U_{xΩ}θ_C to that of U_{xv}θ_D.

Known result: Main theorem of complex multiplication for elliptic curves, soft form. -/
lemma exists_taylorVia_twistedTranslate_theta (e : D.a₁ = σ C.a₁) Ω (H : ∀ {z},
  z ∈ C.latticeModule ↔ ∃ a ∈ quadInt d, Ω * a = z) (S :
  Finset (QuadField d)) : ∃ v ∈ D.latticeModule, ∀ x ∈ S, taylorVia σ
  (C.twistedTranslate 1 (x * Ω) C.θ) = taylorAtZero (D.twistedTranslate 1 (x * v) D.θ) := by
  obtain ⟨n, o, k⟩ := exists_integral_multiples ℤ ℚ S
  obtain ⟨e, u, rfl⟩ : C.a₁ = σ.symm D.a₁ ∧ (2 * n ^ 2 : ℂ) ∣ Ω := by simp [*]
  obtain ⟨M, w, _, μ, ν, -, T⟩ := taylorAtZero_monomialSection σ.symm e, H.2 ⟨1, by simp, rfl⟩,
    exists_conjugate_section σ.symm e u
  simp [↓thetaQuotient_eq_one _ e, -monomialSection] at *
  have Z {m f g a} k (c : taylorAtZero g = taylorVia σ.symm f) s (_ :
    Differentiable ℂ g := by fun_prop) := (T (@comp_mul_mem_sections d D _ D a _
    (exists_isIsogeny_of_mul_mem_lattice (D.5 s)).choose_spec m f k)).elim fun _ ⟨h, _, e⟩ ↦
    eq_of_taylorAtZero_eq (g := (g <| a * ·)) h.1 (by fun_prop) (by aesop) ▸ e
  have v := by simpa [ν, sigma_eq_zero_iff.2 w] using (Z (monomialSection_mem ..) (M 0 1 0)
    (intCast_mem _ (2 * n ^ 2)) :)
  refine ⟨_, v, fun x _ m ↦ have h : n * x ∈ quadInt d := ⟨⟨_, k _ _ m⟩, rfl⟩
    have P {E y} k := (@twistedTranslate_comp_mem d E _ n _ (n * n).natAbs (by simp_all [E.5])
      (by simpa) (mul_assoc _ x y ▸ E.5 h k :))
    (T (P v)).elim fun g ⟨p, q, _⟩ ↦ ext ?_⟩
  obtain ⟨_, ⟨c, rfl⟩, rfl⟩ :=
    section_division _ _ _ C.sections_zero_le_const (P w) p (by simpa) rfl (by
    simp_intro z k [thetaShift_apply]
    obtain ⟨a, m, e⟩ := H.1 (zsmul_mem (add_mem k (sub_mem k C.two_t_mem)) n)
    cases (by grind : z = (a - (n * x + n * x)) * u)
    simp [Z (P v) q (sub_mem m (add_mem h h)) p.1]
    grind [thetaShift_apply, by simpa using Z (monomialSection_mem ..) (M 1 0 0) (zsmul_mem m n)])
  have U {C : CMLattice d} {y z} (h : y = z + z) : C.twistedTranslate 1 y C.θ (-z) = C.θ z ∧
    (C.θ z = 0 → C.twistedTranslate 1 y C.θ 0 = -1) := by simp +contextual [h,
    thetaShift_apply, ↓thetaShift_of_mem C.θ_mem, multiplier_eq_neg_sigmaSign, add_div, add_comm,
    -hermitianForm_apply, fun h : z + C.t ∈ _ ↦ by simpa using add_mem h (sub_mem h C.two_t_mem)]
  simpa [o, show c = 1 by grind [by simpa using congr((
    $(Z (P (zero_mem _)) (ext (by simp [by simpa using M 1 0 0])) (neg_mem h) (P C.Λ.zero_mem).1),
    $(Z (P v) q (neg_mem h) p.1), coeff 0 $q))]] using (congr(σ <| coeff · $q))

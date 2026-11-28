/- GID: D5/S3/Zeros/GRH/Lib/CM/Reciprocity/SemilinearWeilLaw
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/CM/Reciprocity/SemilinearWeilLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.CM.Reciprocity.SemilinearWeilLaw. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/CM/Reciprocity/SemilinearWeilLaw.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Weil.Lift.Staircase
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: the Galois action on CM theta functions and on the finite Weil representation. It
is stated here for Taylor series on a power of one CM curve, and Galois conjugation is a semilinear
map on the finite Weil representation with an explicit factor. Size bounds are added. Source: G.
Shimura, Theta functions with complex multiplication, Duke Math. J. 43 (1976) 673-696.

This file: Semilinear map intertwining Heisenberg translations intertwines the finite Weil
representation. -/


open Matrix ComplexConjugate WeilData stdLattice Submodule Unitary Complex Space
unseal finitePart
variable {E} [Field.{0} E] [CMType E] [WeilData E] {n} [Fintype.{0} n] {s} {V : Space E n s}
  (σ : ℂ →+* ℂ) (g : Gf E n)

/-- The ratio σ(Δ(g))/Δ(g) for a finite unitary point g, with Δ = `finMultiplier`. -/
noncomputable def multiplierRatio := σ (finMultiplier g) / finMultiplier g

lemma map_finMultiplier_mul_conj : σ (finMultiplier g) * σ (conj (finMultiplier g)) = finMultiplier
  g * conj (finMultiplier g) := by simp [← map_mul, mul_conj', ← ofReal_pow, norm_finMultiplier_sq]

attribute [local simp] smul_mem_stdLattice omega_mem_finitePart smul_smul rep_apply_apply
  realMultiplier weilMultiplier integralBox projOn_finHeisOp

/-- For an embedding σ of ℂ into itself and a finite point g of the unitary group, the square of
the factor σΔ(g)/Δ(g) (`multiplierRatio`) equals υ(det g)/σ(υ(det g)). -/
lemma multiplierRatio_sq : multiplierRatio σ g ^ 2 = upsilonU1.1 (detFin 1 g) / σ (upsilonU1.1
  (detFin 1 g)) := by grind [multiplierRatio, finMultiplier_ne_zero, map_finMultiplier_mul_conj,
  map_eq_zero, by simpa using weilMultiplier_neg (g := (1, g)) rfl (G.mat_neg (s := 1) (1, g))]

/-- Let L be σ-semilinear with values in 𝒲_f, Lϱ(x) = ϱ(bx)L on 𝒲_f, σψ₀(z) = ψ₀(bb̄z), R ∩ R̄ =
∅. Then b is a unit, Lω(g) = (σΔ(g)/Δ(g))ω(g)L on 𝒲_f, and some c and unitary adele z have L
vac = cω(z)vac, L(Ψ⊗vac) = cω(z)(σΨ⊗vac), Ψ Schwartz–Bruhat above R.

Known result: Galois action on CM theta functions and on the finite Weil representation. -/
lemma Space.semilinear_intertwines_weil {σ} {L : _ →ₛₗ[σ] V.finitePart} b {R} (hR :
  R.IsConjDisjoint) (hψ : ∀ z, σ (psi₀ E z) = psi₀ E (b * star b * z)) (hL : ∀ᵉ (f ∈ V.finitePart)
  (x), L (V.ϱ (finVec x) f) = V.ϱ (finVec (b • x)) (L f)) : IsUnit b ∧ ∃ c z, L V.vacElem =
  (c : ℂ) • V.ω (1, scalarFin n z) V.vacElem ∧ (∀ᵉ (f ∈ V.finitePart) (g : Gf E n), L (V.ω g f) =
  multiplierRatio σ g • V.ω g (L f)) ∧ ∀ Ψ, IsSchwartzBruhat R Ψ → L (V.name R Ψ V.vacElem) =
  c • V.ω (1, scalarFin n z) (V.name R (σ ∘ Ψ) V.vacElem) := by
  have (f) (h : f ∈ V.finitePart) x : L (V.finHeisOp x f) =
    V.finHeisOp (b • x) (L f) := by simp [finHeisOp, semichar, *]; ac_rfl
  obtain ⟨a, a', u, i, rfl, h⟩ : ∃ (a a' : Ô E) (u : unitary _),
      a.1 * a' = 1 ∧ b = u.1 * a ∧ idem R * a = idem R := by
    obtain ⟨⟨a, a', i⟩, e⟩ := exists_norm_eq_Ô (star_mul_star b b) fun w ↦ by
      have k x := forall_psi₀_mul_eq_one_iff (singleAdele w x)
      simp_rw [← σ.injective.eq_iff (b := 1), hψ, map_one, ← mul_assoc,
        stdLattice.forall_psi₀_mul_eq_one_iff] at k
      simp_all [mem_Ô, ← and_forall_ne w, mul_comm, -map_mul]
      grind [v_uniformizer_inv_mul_le_one_iff, k (uniformizer w).1⁻¹,
        v_uniformizer_inv_mul_le_one_iff (y := 1)]
    simp [Subtype.ext_iff] at e i
    let g x (y : Ô E := ⟨_, idem_mem_Ô R⟩ * (1 - x)) := x + y - star y * x
    use! g a, g a', b * g a' <;> simp [g, mem_iff] <;>
      grind [idem_mul_self, idem_mul_star, star_mul, star_one]
  choose c j using fun g ↦ exists_eq_smul_omega_vacElem (g :=
    scalarFin n u * g) (L _).2 fun y _ ↦ by simpa [scalarFin, mul_assoc, *,
    ← smul_one_eq_diagonal] using congr((L $(V.omega_finHeisOp g (a'.1 • y) V.vacElem)).1).symm
  have := by simpa using j 1
  have k : ∀ f ∈ V.finitePart, V.dataInner (V.ω (scalarFin n u) V.vacElem) (L f) =
    c 1 * σ (V.dataInner V.vacElem f) := by
    apply span_induction <;> simp +contextual [field, *]; intro x
    erw [mul_smul, ← diagonal_const_mulVec, ← omega_finHeisOp _ (1, scalarFin n u), dataInner_omega,
      ← projOn_vacElem (S := ⊤)]
    by_cases x ∈ stdLattice .. <;> simp [*, (smul_mem_stdLattice a'.2).mt, ↓dataInner_projOn,
      mul_comm]
  refine ⟨isUnit_coe.mul (.of_mul_eq_one _ i), _, _, this, ?_,
    fun _ ↦ ?_ ∘ (exists_schrodingerComb_eq hR ·)⟩
  · apply span_induction <;> simp +contextual [*, (commute_scalarFin _).eq, mul_comm]
    grind [multiplierRatio, map_finMultiplier_mul_conj, finMultiplier_ne_zero, map_eq_zero, by
      simpa [j, dataInner_omega_left] using (k _ <| omega_mem_finitePart · vacElem_mem_finitePart)]
  rintro ⟨d, rfl : ∑ _ ∈ _, _ = _⟩
  rw [show σ ∘ _ = ∑ y ∈ _, σ (d y) • schrodingerAct R (a.1 • y) (boxIndicator n R) by
    ext; simp [schrodingerAct, apply_ite σ, *]; congr! 4; grind [u.2.2]]
  simp [name_schrodingerAct_boxIndicator, *, ω_ϱ, mulVec_finVec, Finset.smul_sum]
  congr! 1
  erw [diagonal_const_mulVec u.1]; simp; ring

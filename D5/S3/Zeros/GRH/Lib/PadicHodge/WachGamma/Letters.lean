/- GID: D5/S3/Zeros/GRH/Lib/PadicHodge/WachGamma/Letters
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/PadicHodge/WachGamma/Letters
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.PadicHodge.WachGamma.Letters. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/PadicHodge/WachGamma/Letters.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.PadicHodge.WachGamma.KisinModuleDefs
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Kisin modules, with the Galois action trivial modulo the variable and the Hodge–Tate weights
read off. This is the analogue, for the Kisin module of one Kummer chart inside A_inf, of the known
statements on Wach modules. It is stated per unramified embedding of the coefficients, and for the
weights it gives only upper bounds by the multiplicity of each jump. Source: L. Berger, Limites de
représentations cristallines, Compositio Math. 140 (2004), 1473–1498, §III; N. Wach, Représentations
p-adiques potentiellement cristallines, Bull. SMF 124 (1996), 375–400.

Part of: Kisin lattice (Breuil–Kisin module) of a crystalline lattice (known result; see
Lib.PadicHodge.WachKisin.PeriodMatrixFrame).

This file: Functoriality of Kisin modules, projectors to embeddings, pole orders of invariant
forms. -/

open Finset Algebra Module Set Submodule WittVector Lift.FrobGroup

variable {p} [ThePrime p] [Γ : GroupOverGp p] {k : Lift.KummerChart Γ} {O} {L L' :
  Lift.KummerChart.JumpLattice O} {l a b : ℕ} {i i' : Lift.KummerChart.Letter} {n : ℤ} {x :
  L.Ambient} (g : k.galMonoid) (F : L.Hom L') (m : Lift.FrobGroup Γ) {μ : L.Functional}

namespace Lift.KummerChart.JumpLattice

attribute [-instance] NormedAlgebra.toAlgebra NormedSpace.toModule

attribute [-simp] Algebra.toRingHom_ofId map_one pow_eq_one_iff smul_right_inj

attribute [local simp] frobGroup_smul_smul Nat.cast_smul_eq_nsmul invOf_smul_eq_iff smul_pow

@[simp] lemma Hom.wittMap_smul : ∀ x, F.wittMap (m • x) = m • F.wittMap x :=
  diagTensor_induction (by simp [F.isIntertwining])

lemma wittMap_mem_ainfLattice F : x ∈ L.ainfLattice → L.wittMap L' F x ∈ L'.ainfLattice :=
  (mapsTo_span (f := (wittMap ..).restrictScalars _) (by simp) ·)

lemma Hom.comp_wittMap_mem_forms {μ} : μ ∈ L'.forms →
  μ ∘ₗ F.wittMap ∈ L.forms := by simp_all [forms, F.isIntertwining]

lemma Hom.map_mem_kisinAinf : x ∈ L.kisinAinf → F.wittMap x ∈ L'.kisinAinf :=
  .imp (.imp fun _ ↦ .imp_right (by simpa using wittMap_mem_ainfLattice _ ·)) fun H n _ ↦
  F.wittMap_smul .. ▸ H n _ ∘ F.comp_wittMap_mem_forms

lemma Hom.wittMap_mem_frobKisinAinf : x ∈ L.frobKisinAinf l → F.wittMap x ∈ L'.frobKisinAinf l :=
  (F.wittMap_smul .. ▸ F.map_mem_kisinAinf · :)

@[simp] lemma letterOp_pow_mk n a t : (L.letterOp i ^ n) (no_index (.mk a t)) =
  k.letterTeich i⁻¹ ^ n • .mk a
  (O.ζ.1 ^ n • t) := by induction n <;> simp_all [letterOp, pow_succ', mulZeta, smul_smul, mul_comm]

lemma mem_letterPart_iff_mulZeta : x ∈ letterPart i ↔ L.mulZeta.wittMap x = k.letterTeich i • x :=
  sub_eq_zero.trans (inv_smul_eq_iff (g := k.letterTeich.toHomUnits i))

lemma S_smul (s : k.S) : s • x = s.1 • x := rfl

@[simp] lemma Hom.wittMap_letterProj : ∀ x, F.wittMap (L.letterProj i x) =
  L'.letterProj i (F.wittMap x) := diagTensor_induction (by simp [letterProj])

lemma smul_letterProj {m : FrobGroup Γ} (h : m • (k.letterTeich i⁻¹).1 = k.letterTeich i'⁻¹) :
    ∀ x, m • L.letterProj i x = L.letterProj i' (m • x) :=
  diagTensor_induction (by simp_all [letterProj, smul_comm m, smul_sum, S_smul])

lemma gal_smul_letterProj : ∀ x, g.1 • L.letterProj i x = L.letterProj i (g.1 • x) :=
  smul_letterProj (g.2.choose_spec ▸ (fixes _).1 _)

lemma phi_pow_smul_letterTeich : φ ^ l • (letterTeich i⁻¹).1 =
  letterTeich ((letterFrob ^ l) i)⁻¹ := by erw [phi_pow_smul, k.letterFrob.coe_pow,
  pow_iterate, map_pow, k.S.coe_pow, Subtype.coe_mk, map_teichmuller]; simp

lemma letterProj_mem_letterPart : L.letterProj i x ∈ letterPart i :=
  (diagTensor_induction (by simp [letterProj, mul_geom_sum, ← map_pow, by
  simpa using O.ζ.2, map_one]) : ∀ x, ((_ - 1) * L.letterProj i) x = 0) x

lemma mem_letterPart_iff_letterProj : x ∈ letterPart i ↔ L.letterProj i x = x := ⟨by simp_all
  [letterProj, End.pow_apply, letterPart, Function.iterate_fixed], (· ▸ letterProj_mem_letterPart)⟩

lemma gal_smul_mem_letterPart : g • x ∈ letterPart i ↔ x ∈ letterPart i := by
  simp [mem_letterPart_iff_letterProj, k.galMonoid.smul_def, ← gal_smul_letterProj,
    smul_left_cancel_iff]

lemma phi_pow_smul_mem_letterPart_iff : φ ^ a • x ∈ letterPart i ↔
  x ∈ letterPart (i.stepBack a) := by simp [mem_letterPart_iff_letterProj,
  ← Equiv.apply_symm_apply .. ▸ smul_letterProj phi_pow_smul_letterTeich, smul_left_cancel_iff]

lemma frobKisinAinf_zero : L.frobKisinAinf 0 = kisinAinf := Submodule.ext (by simp [frobKisinAinf])

lemma frobEUnit_pow_smul n : k.frobEUnit a ^ n • x =
  (k.frobE a).1 ^ n • x := by simp [Units.smul_def, frobEUnit, ← map_pow]

lemma finrank_wittFq [ThePrime b] {f} : finrank ℤ_[b] (WittFq f) = f := by
  simpa [Nat.pow_right_inj Fact.out] using (congrArg (·.index) (AddSubgroup.ext (H := pPowMultiples
    (WittFq f) 1) (by simp [mem_span_singleton, mul_comm]))).trans (Nat.card_congr quotientPEquiv.1)

lemma zTauUnit_smul : k.zTauUnit • x = k.zTau • x := (rfl)

@[simp] lemma frobEUnit_smul : k.frobEUnit a • x = (k.frobE a).1 • x := (rfl)

/-- The B_dR-linear map sending μ: W(C^♭) ⊗ L → B_dR to the vector of its values μ(1 ⊗ e_l) on a
chosen Z_p-basis (e_l) of L. -/
noncomputable def basisValues : L.Functional →ₗ[BdR] Fin (finrank ℤ_[p] L.Carrier) → BdR :=
  .pi fun l ↦ .applyₗ' _ (.mk 1 (finBasis _ _ l))

lemma ainfLattice_eq_span_basis : L.ainfLattice = span _ (.range (DiagTensor.mk 1 ∘ finBasis ℤ_[p]
  _)) := .trans (by simp [range_comp]; rfl) (span_span_of_tower ℤ_[p] ..)

lemma apply_eq_of_mem_fracSpan (f f' : L.Functional) (h : basisValues f = basisValues f') :
  x ∈ fracSpan → f x = f' x := fun ⟨_, a, e⟩ ↦ by
  simpa [smul_right_inj, by simpa using a] using
    f.eqOn_span (by simpa) (ainfLattice_eq_span_basis.le e)

@[simp] lemma inr_smul {r : Ainf} (g : Γ) : inr g • r = toGp g • r := rfl

/-- The conjugate of an A_inf-linear map μ: W(C^♭) ⊗ L → B_dR by g in Γ, namely x ↦
j(g)⁻¹·μ(gx). -/
@[simps] noncomputable def conjForm (μ : L.Functional) (g : Γ) :
    L.Functional := ⟨⟨fun x ↦ (toGp g)⁻¹ • μ (inr g • x), by simp⟩, by simp [smul_distrib_smul]⟩

lemma form_gal_smul (hμ : μ ∈ L.forms) (hx : x ∈ fracSpan) : μ (g • x) =
  g • μ x := have ⟨_, _, rfl⟩ := g
  inv_smul_eq_iff.1
    (apply_eq_of_mem_fracSpan (conjForm ..) _ (funext (by simp [basisValues, hμ _])) hx)

lemma smul_mem_ainfLattice : x ∈ ainfLattice → m • x ∈ ainfLattice :=
  (mapsTo_span (f := semilinearAct m) (by simp) ·)

lemma smul_mem_fracSpan : x ∈ fracSpan → m • x ∈ fracSpan :=
  .imp' (m • ·) (by simp_all [smul_eq_zero_iff_eq, ← frobGroup_smul_smul, smul_mem_ainfLattice])

lemma valueAt_frobEUnit_zpow_smul : ∀ x, valueAt a μ (k.frobEUnit b ^ n • x) =
  phiInvToBdR a (k.frobE b) ^ n * valueAt a μ x := (MulAction.surjective
  (k.frobEUnit b ^ (-n).toNat)).forall.2 (by cases n <;> simp [↓smul_smul, frobEUnit_pow_smul])

lemma mk_one_mem_ainfLattice t : no_index (.mk 1 t) ∈ L.ainfLattice := subset_span ⟨t, rfl⟩

lemma letterProj_mk_mem_ainfLattice t : L.letterProj i (.mk 1 t) ∈ ainfLattice := by
  simp (maxDischargeDepth := 4) [letterProj, sum_mem, smul_of_tower_mem, mk_one_mem_ainfLattice]

lemma comp_letterProj_mem_forms (h : μ ∈ L.forms) : μ ∘ₗ L.letterProj i ∈ L.forms := fun t g ↦ by
  erw [← form_gal_smul ⟨_, g, rfl⟩ h (le_saturateBy (letterProj_mk_mem_ainfLattice t)),
    gal_smul_letterProj]; simp

lemma valueAt_comp_wittMap {μ} : valueAt a (μ ∘ₗ F.wittMap) x =
  valueAt a μ (F.wittMap x) := by simp [valueAt]

lemma sum_letterProj x : ∑ i, L.letterProj i x = x := by
  simp [letterProj, letterOp, ← smul_sum]
  rw [sum_comm, sum_eq_single 0 fun n a b ↦ by erw [← sum_smul, sum_hom_units_eq_zero
    (k.letterTeich.comp invMonoidHom ^ n) fun e ↦ (exists_pow_ne_one_of_isCyclic b (by aesop)).rec
    fun x : Letter ↦ (· (Units.ext (by simpa [letterTeich, RingHom.algebraMap_toAlgebra,
    ← map_pow] using! congr(($e x⁻¹).1.1 0)))), zero_smul]] <;> simp

/-- Let O be a domain and L potentially crystalline. The forms of type u at the letter i
(`Lift.KummerChart.JumpLattice.formsOfType`) are spanned over Q̄_p, modulo those of type u − 1, by
at most Σ jump_γ(u) of them, summed over the γ with γ(ζ) = θ(ω(i)).

Known result: Kisin modules: Galois action trivial modulo the variable, Hodge–Tate weights read
off. -/
lemma exists_span_formsOfType_mod_pred i u : ∃ r ≤ L.jumpMultiplicity i u, ∃ ν : Fin r →
  L.formsOfType i u, ∀ μ ∈ L.formsOfType i u, ∃ c :
  _ → PadicAlgCl p, μ - ∑ m, c m • (ν m).1 ∈ formsOfType i (u - 1) := by
  choose a ha using fun μ : L.formsOfType i u ↦ (mem_span_singleton.1 <| μ.2.2 ·)
  have A {μ t z y} h (e : thetaBdR y = z := by simp +zetaDelta [smul_def']) :=
    (congrArg _ ((smul_left_inj NeZero.out).1 ((ha μ t).trans h))).trans e
  let f μ : L.Carrier →ₛₗ[(ofId ℤ_[p] ℂ_[p] : ℤ_[p] →+* ℂ_[p])] _ := ⟨⟨thetaBdR ∘ a μ, fun _
    _ ↦ A (by simp [add_smul, ← ha]) (map_add ..)⟩, fun c t ↦ A (y := c • a μ t) (by simp [← ha])⟩
  have G μ t (g : k.Γ') : f μ (L.ρ g t) = (χ g ^ (-u)).1 • toGp g • f μ t :=
    A (by erw [comp_letterProj_mem_forms μ.2.1, ← ha, smul_distrib_smul, smul_tUnit_zpow, smul_comm,
    ← smul_assoc])
  choose _ ν hs' li using exists_fun_fin_finrank_span_eq ℂ_[p] (.range f)
  choose ν eν using ν
  refine ⟨_, L.inClass.isPotCrys.sum_jump_eq_jump_overZp.2 _ _ _ _ (forall_mem_range.2 fun μ ↦
    ⟨(nearOne_le <| G μ ·), fun t ↦ A (by erw [← mulZeta.wittMap_letterProj (.mk 1 t),
    mem_letterPart_iff_mulZeta.1 letterProj_mem_letterPart, μ.1.map_smul, ← ha, ← smul_assoc])⟩), ν,
    SetCoe.forall'.2 fun μ ↦ ?_⟩
  obtain ⟨c, hc⟩ := (mem_span_range_iff_exists_fun _).1 (hs'.ge (subset_span ⟨μ, rfl⟩))
  choose c' K e' using fun m ↦ (forall_smul_eq_iff_mem_localFieldOf k.Γ').1 fun g ↦
    (li.eq_coords_of_eq (g := toGp g • c) (LinearMap.ext ((L.ρ.apply_bijective g).2.forall.2 (by
    simpa [← hc, ← eν, G, smul_sum] using G μ · g))) m).symm
  use c', fun t g ↦ by simp_all [μ.2.1 t, (ν _).2.1 t, smul_sub, smul_sum, smul_def'], fun t ↦ by
    simpa [← ha, ↓← smul_def', sub_smul, sum_smul] using! mul_mem_hodgeFil (n := -u)
      (algebraMap_mem_hodgeFil_one_iff (y := a μ t - ∑ m,
      c' m • a _ t).2 (by simpa [← eν, e', smul_def'] using! congr($hc.symm t))) (subset_span rfl)

/-- If n is not in the set U_i of allowed jumps, every invariant form with pole order at most n
on the part of L at the letter i has pole order at most n − 1 there. -/
lemma formsOfType_subset_pred_of_notMem (h : n ∉ L.U i) :
  L.formsOfType i n ⊆ L.formsOfType i (n - 1) := (L.exists_span_formsOfType_mod_pred i n).elim
  (by rw [jumpMultiplicity, sum_eq_zero (by grind [InClass, JumpLattice])]; aesop)

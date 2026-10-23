/- GID: D5/S3/Quantum/Entanglement/HypercubeRendezvousQuantumGap
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/HypercubeRendezvousQuantumGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Balanced hypercube rendezvous has a dimension-independent quantum gap. -/
import D5.S3.Quantum.Entanglement.RendezvousVectorSystemGap
import D5.S3.Weil.ZetaLinear.RankTrace
import Mathlib.Analysis.Matrix.Order
noncomputable section
open scoped BigOperators symmDiff ComplexOrder Kronecker MatrixOrder
namespace D5.S3.Quantum.Entanglement.HypercubeRendezvousQuantumGap
open D5.S3.Quantum.Entanglement.RendezvousVectorSystemGap
abbrev Correlation (d t : ℕ) := Vertex d → Vertex d → Output d t → Output d t → ℝ
def Promised (d t : ℕ) (σ τ : Vertex d) : Prop := (σ ∆ τ).card = 2 * t
def Inputs (d t : ℕ) : Finset (Vertex d × Vertex d) := by
  classical
  exact Finset.univ.filter (fun p => Promised d t p.1 p.2)
def value {d t : ℕ} (P : Correlation d t) : ℝ := by
  classical
  exact (∑ p ∈ Inputs d t, ∑ A, ∑ B, if Wins p.1 p.2 A B then P p.1 p.2 A B else 0) /
    ((Inputs d t).card : ℝ)
structure QStrategy (d t : ℕ) (α : Type*) (β : Type*)
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] where
  ρ : Matrix (α × β) (α × β) ℂ
  rho_psd : ρ.PosSemidef
  rho_trace : Matrix.trace ρ = 1
  E : Vertex d → Output d t → Matrix α α ℂ
  F : Vertex d → Output d t → Matrix β β ℂ
  E_psd : ∀ σ A, (E σ A).PosSemidef
  F_psd : ∀ τ B, (F τ B).PosSemidef
  E_sum : ∀ σ, (∑ A, E σ A) = 1
  F_sum : ∀ τ, (∑ B, F τ B) = 1
def QStrategy.prob {d t : ℕ} {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (S : QStrategy d t α β) : Correlation d t := fun σ τ A B =>
  (Matrix.trace (S.ρ * Matrix.kronecker (S.E σ A) (S.F τ B))).re
def IsQuantum {d t : ℕ} (P : Correlation d t) : Prop :=
  ∃ (α β : Type) (fα : Fintype α) (fβ : Fintype β)
      (dα : DecidableEq α) (dβ : DecidableEq β),
    letI : Fintype α := fα
    letI : Fintype β := fβ
    letI : DecidableEq α := dα
    letI : DecidableEq β := dβ
    ∃ S : QStrategy d t α β, S.prob = P
def IsNS {d t : ℕ} (P : Correlation d t) : Prop :=
  (∀ σ τ A B, 0 ≤ P σ τ A B) ∧ (∀ σ τ, (∑ A, ∑ B, P σ τ A B) = 1) ∧
  (∀ σ τ τ' A, (∑ B, P σ τ A B) = ∑ B, P σ τ' A B) ∧
  (∀ σ σ' τ B, (∑ A, P σ τ A B) = ∑ A, P σ' τ A B)
def QValues (d t : ℕ) : Set ℝ := {r | ∃ P : Correlation d t, IsQuantum P ∧ value P = r}
def NSValues (d t : ℕ) : Set ℝ := {r | ∃ P : Correlation d t, IsNS P ∧ value P = r}
def omegaQ (d t : ℕ) : ℝ := sSup (QValues d t)
def omegaNS (d t : ℕ) : ℝ := sSup (NSValues d t)
def claim : Prop := ∀ t d : ℕ, 2 ≤ t → 2 * t < d → omegaQ d t < omegaNS d t


section QuantumBridge
private abbrev G (d : ℕ) := Vertex d × Equiv.Perm (Fin d)
private def pmap {d : ℕ} (p : Equiv.Perm (Fin d)) (s : Finset (Fin d)) : Finset (Fin d) :=
  s.map p.toEmbedding
private def actV {d : ℕ} (g : G d) (s : Vertex d) : Vertex d :=
  g.1 ∆ pmap g.2 s
private def actO {d t : ℕ} (g : G d) (A : Output d t) : Output d t :=
  ⟨pmap g.2 A.val, by dsimp only [pmap]; rw [Finset.card_map]; exact A.property⟩
private lemma pmap_symmDiff {d : ℕ} (p : Equiv.Perm (Fin d)) (s t : Finset (Fin d)) :
    pmap p (s ∆ t) = pmap p s ∆ pmap p t := by
  dsimp only [pmap]
  simpa only [Finset.map_eq_image, Equiv.coe_toEmbedding] using
    Finset.image_symmDiff s t p.injective
private lemma pmap_comp {d : ℕ} (p q : Equiv.Perm (Fin d)) (s : Finset (Fin d)) :
    pmap p (pmap q s) = pmap (p * q) s := by
  dsimp only [pmap]; rw [Finset.map_map]; rfl
private lemma pmap_refl {d : ℕ} (s : Finset (Fin d)) : pmap (Equiv.refl _) s = s := by
  dsimp only [pmap]; exact Finset.map_refl
private lemma pmap_one {d : ℕ} (s : Finset (Fin d)) : pmap 1 s = s := by
  change pmap (Equiv.refl _) s = s
  exact pmap_refl s
private lemma pmap_card {d : ℕ} (p : Equiv.Perm (Fin d)) (s : Finset (Fin d)) :
    (pmap p s).card = s.card := by dsimp only [pmap]; exact Finset.card_map _
private abbrev VG (d : ℕ) (α β : Type*) [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] := G d → Matrix (α × β) (α × β) ℂ
private def hvec {d : ℕ} {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] : VG d α β := fun _ => 1
private def uvec {d t : ℕ} {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (S : QStrategy d t α β) (σ : Vertex d) (A : Output d t) :
    VG d α β := fun g => Matrix.kronecker (S.E (actV g σ) (actO g A)) 1
private def vvec {d t : ℕ} {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (S : QStrategy d t α β) (τ : Vertex d) (B : Output d t) :
    VG d α β := fun g => Matrix.kronecker 1 (S.F (actV g τ) (actO g B))
private def effect {d t : ℕ} {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (S : QStrategy d t α β) (σ : Vertex d)
    (T : Finset (Output d t)) : Matrix α α ℂ := ∑ A ∈ T, S.E σ A
private lemma effect_nonneg {d t : ℕ} {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (S : QStrategy d t α β) (σ : Vertex d)
    (T : Finset (Output d t)) : (effect S σ T).PosSemidef := by
  dsimp only [effect]
  exact Matrix.posSemidef_sum T (fun A hA => S.E_psd σ A)
private lemma effect_le_one {d t : ℕ} {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (S : QStrategy d t α β) (σ : Vertex d)
    (T : Finset (Output d t)) : effect S σ T ≤ 1 := by
  dsimp only [effect]
  rw [← S.E_sum σ]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
    (fun A _ _ => (S.E_psd σ A).nonneg)
private lemma contraction_sq {α : Type*} [Fintype α] [DecidableEq α]
    (X : Matrix α α ℂ) (hp : X.PosSemidef) (hc : X ≤ 1) : X * X ≤ X := by
  have hc' : 0 ≤ 1 - X := (Matrix.le_iff.mp hc).nonneg
  have hcomm : Commute X (1 - X) :=
    (Commute.one_right _).sub_right (Commute.refl _)
  have hmul := Commute.mul_nonneg hp.nonneg hc' hcomm
  have hprod : (X * (1 - X)).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp hmul
  have heq : X - X * X = X * (1 - X) := by
    simp [mul_sub, mul_one]
  have hpsd : (X - X * X).PosSemidef := by
    rw [heq]
    exact hprod
  exact Matrix.le_iff.mpr hpsd
private lemma effect_sq_le {d t : ℕ} {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (S : QStrategy d t α β) (σ : Vertex d)
    (T : Finset (Output d t)) : effect S σ T * effect S σ T ≤ effect S σ T :=
  contraction_sq _ (effect_nonneg S σ T) (effect_le_one S σ T)
private def pairTrace {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] (ρ : Matrix (α × β) (α × β) ℂ)
    (x y : Matrix (α × β) (α × β) ℂ) : ℝ :=
  (Matrix.trace (star x * y * ρ)).re
private lemma trace_budget {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (ρ X : Matrix (α × β) (α × β) ℂ)
    (hρ : ρ.PosSemidef) (hX : X.PosSemidef) (hsq : X * X ≤ X) :
    pairTrace ρ X X ≤ pairTrace ρ 1 X := by
  have hp := RHLinalg.trace_mul_nonneg_of_posSemidef (Matrix.le_iff.mp hsq) hρ
  rw [Matrix.sub_mul, Matrix.trace_sub] at hp
  change 0 ≤ ((X * ρ).trace - (X * X * ρ).trace).re at hp
  rw [Complex.sub_re] at hp
  dsimp only [pairTrace]
  rw [Matrix.star_eq_conjTranspose, hX.isHermitian.eq,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_one, one_mul]
  linarith
private lemma kron_sq_le {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] (X : Matrix α α ℂ) (hsq : X * X ≤ X) :
    (X ⊗ₖ (1 : Matrix β β ℂ)) * (X ⊗ₖ (1 : Matrix β β ℂ)) ≤ X ⊗ₖ 1 ∧
      ((1 : Matrix β β ℂ) ⊗ₖ X) * ((1 : Matrix β β ℂ) ⊗ₖ X) ≤ 1 ⊗ₖ X := by
  classical
  have hp := Matrix.le_iff.mp hsq
  constructor
  · apply Matrix.le_iff.mpr
    rw [← Matrix.mul_kronecker_mul, one_mul]
    convert hp.kronecker (Matrix.PosSemidef.one (n := β) (R := ℂ)) using 1
    ext i j
    simp only [Matrix.sub_apply, Matrix.kroneckerMap_apply]
    ring
  · apply Matrix.le_iff.mpr
    rw [← Matrix.mul_kronecker_mul, one_mul]
    convert (Matrix.PosSemidef.one (n := β) (R := ℂ)).kronecker hp using 1
    ext i j
    simp only [Matrix.sub_apply, Matrix.kroneckerMap_apply]
    ring
private lemma effect_budget {d t : ℕ} {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (S : QStrategy d t α β) (σ : Vertex d)
    (T : Finset (Output d t)) :
    pairTrace S.ρ (effect S σ T ⊗ₖ (1 : Matrix β β ℂ)) (effect S σ T ⊗ₖ 1) ≤
      pairTrace S.ρ 1 (effect S σ T ⊗ₖ 1) :=
  trace_budget S.ρ _ S.rho_psd ((effect_nonneg S σ T).kronecker Matrix.PosSemidef.one)
    (kron_sq_le (effect S σ T) (effect_sq_le S σ T)).1
private lemma kron_trace_uv {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (ρ : Matrix (α × β) (α × β) ℂ)
    (E : Matrix α α ℂ) (F : Matrix β β ℂ) (hE : E.IsHermitian) :
    pairTrace ρ (Matrix.kronecker E 1) (Matrix.kronecker 1 F) =
      (Matrix.trace (ρ * Matrix.kronecker E F)).re := by
  dsimp only [pairTrace]
  change (((Matrix.kroneckerMap (fun x y : ℂ => x * y) E 1).conjTranspose *
      Matrix.kroneckerMap (fun x y : ℂ => x * y) 1 F * ρ).trace.re) = _
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
  simp only [Matrix.conjTranspose_one, hE.eq, Matrix.mul_one, Matrix.one_mul]
  rw [Matrix.trace_mul_comm]
  rfl
private def rightMul {d : ℕ} (h g : G d) : G d :=
  (g.1 ∆ pmap g.2 h.1, g.2 * h.2)
private def rightMul_equiv {d : ℕ} (h : G d) : G d ≃ G d := by
  refine ⟨rightMul h, fun g =>
    (g.1 ∆ pmap (g.2 * h.2⁻¹) h.1, g.2 * h.2⁻¹), ?_, ?_⟩
  · intro g; apply Prod.ext <;> (dsimp only [rightMul]; simp [mul_assoc])
  · intro g; apply Prod.ext <;> (dsimp only [rightMul]; simp [mul_assoc])
private lemma actV_rightMul {d : ℕ} (h g : G d) (σ : Vertex d) :
    actV (rightMul h g) σ = actV g (actV h σ) := by
  dsimp only [actV, rightMul]
  rw [pmap_symmDiff, pmap_comp, symmDiff_assoc]
private lemma actO_rightMul {d t : ℕ} (h g : G d) (A : Output d t) :
    actO (rightMul h g) A = actO g (actO h A) := by
  apply Subtype.ext
  dsimp only [actO, rightMul]
  rw [pmap_comp]
private def actO_equiv {d t : ℕ} (g : G d) : Output d t ≃ Output d t := by
  refine ⟨actO g, actO (∅, g.2⁻¹), ?_, ?_⟩
  · intro A; apply Subtype.ext
    dsimp only [actO]
    rw [pmap_comp, inv_mul_cancel, pmap_one]
  · intro A; apply Subtype.ext
    dsimp only [actO]
    rw [pmap_comp, mul_inv_cancel, pmap_one]
private lemma sum_rightMul {d : ℕ} {R : Type*} [AddCommMonoid R] (h : G d) (f : G d → R) :
    ∑ g, f (rightMul h g) = ∑ g, f g :=
  Fintype.sum_equiv (rightMul_equiv h) (fun g => f (rightMul h g)) f (fun _ => rfl)
private lemma input_output_transitive {d t : ℕ} (σ σ' : Vertex d) (A A' : Output d t) :
    ∃ h : G d, actV h σ = σ' ∧ actO h A = A' := by
  obtain ⟨p, hp⟩ := Equiv.Perm.exists_map_finset_eq A.val A'.val
    (A.property.trans A'.property.symm)
  refine ⟨(σ' ∆ pmap p σ, p), ?_, ?_⟩
  · dsimp only [actV]
    exact symmDiff_symmDiff_cancel_right _ _
  · exact Subtype.ext hp
private lemma orbit_sum_constant {d t : ℕ} {R : Type*} [AddCommMonoid R]
    (f : Vertex d → Output d t → R) (σ σ' : Vertex d) (A A' : Output d t) :
    ∑ g : G d, f (actV g σ) (actO g A) = ∑ g : G d, f (actV g σ') (actO g A') := by
  obtain ⟨h, hσ, hA⟩ := input_output_transitive σ σ' A A'
  rw [← hσ, ← hA]
  symm
  calc
    ∑ g : G d, f (actV g (actV h σ)) (actO g (actO h A)) =
      ∑ g : G d, f (actV (rightMul h g) σ) (actO (rightMul h g) A) := by
        apply Finset.sum_congr rfl
        intro g hg
        rw [actV_rightMul, actO_rightMul]
    _ = _ := sum_rightMul h (fun g => f (actV g σ) (actO g A))
private abbrev weightedCore {d t : ℕ} {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (S : QStrategy d t α β) :
    PreInnerProductSpace.Core ℝ (VG d α β) := by
  classical
  let _ : Nonempty (Vertex d) := ⟨∅⟩
  let _ : Nonempty (Equiv.Perm (Fin d)) := ⟨Equiv.refl _⟩
  let k : ℝ := (n d t) / (Fintype.card (G d) : ℝ)
  let I : VG d α β → VG d α β → ℝ := fun x y =>
    k * ∑ g, pairTrace S.ρ (x g) (y g)
  refine {
    inner := I
    conj_inner_symm := ?_
    re_inner_nonneg := ?_
    add_left := ?_
    smul_left := ?_ }
  · intro x y; dsimp only [I, pairTrace]
    simp only [RCLike.conj_to_real]
    congr 1; apply Fintype.sum_congr
    intro g
    have hρ : S.ρ.conjTranspose = S.ρ := S.rho_psd.isHermitian.eq
    have h := Matrix.trace_conjTranspose (star (y g) * x g * S.ρ)
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hρ] at h
    have h' := congrArg Complex.re h
    change _ = ((starRingEnd ℂ) (star (y g) * x g * S.ρ).trace).re at h'
    rw [Complex.conj_re] at h'
    have h'' : (Matrix.trace (S.ρ * ((x g).conjTranspose * y g))).re =
        (Matrix.trace ((y g).conjTranspose * x g * S.ρ)).re := by
      simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose] using h'
    have hxy := Matrix.trace_mul_cycle S.ρ (x g).conjTranspose (y g)
    have hyx := Matrix.trace_mul_cycle (y g) S.ρ (x g).conjTranspose
    have hxy' : (Matrix.trace (S.ρ * ((x g).conjTranspose * y g))).re =
        (Matrix.trace (y g * S.ρ * (x g).conjTranspose)).re := by
      simpa only [mul_assoc] using congrArg Complex.re hxy
    have hyx' : (Matrix.trace (y g * S.ρ * (x g).conjTranspose)).re =
        (Matrix.trace ((x g).conjTranspose * y g * S.ρ)).re := by
      simpa only using congrArg Complex.re hyx
    calc
      (Matrix.trace (star (y g) * x g * S.ρ)).re =
          (Matrix.trace (S.ρ * ((x g).conjTranspose * y g))).re := h''.symm
      _ = (Matrix.trace (y g * S.ρ * (x g).conjTranspose)).re := hxy'
      _ = (Matrix.trace ((x g).conjTranspose * y g * S.ρ)).re := hyx'
  · intro x; dsimp only [I, pairTrace]
    have hcard : 0 < (Fintype.card (G d) : ℝ) := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (G d))
    have hk : 0 ≤ k := by dsimp only [k, n]; positivity
    apply mul_nonneg hk
    apply Finset.sum_nonneg
    intro g hg
    exact RHLinalg.trace_mul_nonneg_of_posSemidef
      (Matrix.posSemidef_conjTranspose_mul_self (x g)) S.rho_psd
  · intro x y z; dsimp only [I]
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro g hg
    dsimp only [pairTrace]
    rw [Matrix.star_eq_conjTranspose, Pi.add_apply, Matrix.conjTranspose_add, Matrix.add_mul,
      Matrix.add_mul, Matrix.trace_add, Matrix.star_eq_conjTranspose]
    rfl
  · intro x y r; dsimp only [I]
    have hr : (starRingEnd ℝ) r = r := RCLike.conj_to_real
    rw [hr]
    calc
      k * ∑ g, pairTrace S.ρ ((r • x) g) (y g) =
          k * ∑ g, r * pairTrace S.ρ (x g) (y g) := by
            congr 1
            apply Finset.sum_congr rfl
            intro g hg
            dsimp only [pairTrace, Pi.smul_apply]
            rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul,
              Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_smul]
            simp only [Complex.smul_re, smul_eq_mul]
            change r * _ = r * _
            rfl
      _ = r * (k * ∑ g, pairTrace S.ρ (x g) (y g)) := by
        rw [← Finset.mul_sum]
        ring
private lemma inner_uv_eq {d t : ℕ} {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (S : QStrategy d t α β)
    (σ : Vertex d) (τ : Vertex d) (A : Output d t) (B : Output d t) :
    (weightedCore S).inner (uvec S σ A) (vvec S τ B) =
      (n d t / (Fintype.card (G d) : ℝ)) *
        ∑ g, S.prob (actV g σ) (actV g τ) (actO g A) (actO g B) := by
  classical
  let _ : Nonempty (Vertex d) := ⟨∅⟩
  let _ : Nonempty (Equiv.Perm (Fin d)) := ⟨Equiv.refl _⟩
  change (n d t / (Fintype.card (G d) : ℝ)) *
      ∑ g, pairTrace S.ρ (uvec S σ A g) (vvec S τ B g) = _
  congr 1
  apply Finset.sum_congr rfl
  intro g hg
  dsimp only [uvec, vvec]
  rw [kron_trace_uv _ _ _ (S.E_psd _ _).isHermitian]
  rfl
private lemma inner_hh {d t : ℕ} {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (S : QStrategy d t α β) :
    (weightedCore S).inner hvec hvec = n d t := by
  classical
  let _ : Nonempty (Vertex d) := ⟨∅⟩
  let _ : Nonempty (Equiv.Perm (Fin d)) := ⟨Equiv.refl _⟩
  have hc : (Fintype.card (G d) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (G d) ≠ 0)
  change n d t / (Fintype.card (G d) : ℝ) * ∑ g : G d, pairTrace S.ρ 1 1 = _
  dsimp only [pairTrace]
  rw [star_one, one_mul, one_mul, S.rho_trace]
  simp only [Complex.one_re, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact div_mul_cancel₀ _ hc
private lemma inner_u_budget {d t : ℕ} {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (S : QStrategy d t α β)
    (σ : Vertex d) (A : Output d t) :
    (weightedCore S).inner (uvec S σ A) (uvec S σ A) ≤
      (weightedCore S).inner hvec (uvec S σ A) := by
  classical
  change n d t / (Fintype.card (G d) : ℝ) *
    ∑ g, pairTrace S.ρ (uvec S σ A g) (uvec S σ A g) ≤
      n d t / (Fintype.card (G d) : ℝ) * ∑ g, pairTrace S.ρ 1 (uvec S σ A g)
  apply mul_le_mul_of_nonneg_left _ (by dsimp only [n]; positivity)
  apply Finset.sum_le_sum
  intro g hg
  have hb := effect_budget S (actV g σ) {actO g A}
  dsimp only [effect] at hb
  rw [Finset.sum_singleton] at hb
  exact hb
private lemma sum_uvec {d t : ℕ} {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (S : QStrategy d t α β) (σ : Vertex d) :
    ∑ A, uvec S σ A = hvec := by
  classical
  funext g
  rw [Finset.sum_apply]
  dsimp only [uvec, hvec]
  have hs : (∑ A, S.E (actV g σ) (actO g A)) = 1 :=
    (Fintype.sum_equiv (actO_equiv g)
      (fun A => S.E (actV g σ) (actO g A)) (S.E (actV g σ)) (fun _ => rfl)).trans
        (S.E_sum (actV g σ))
  have hk := map_sum ((Matrix.kroneckerBilinear (R := ℂ) (α := ℂ)).flip
    (1 : Matrix β β ℂ)) (fun A => S.E (actV g σ) (actO g A)) Finset.univ
  change (∑ A, S.E (actV g σ) (actO g A)) ⊗ₖ (1 : Matrix β β ℂ) =
    ∑ A, S.E (actV g σ) (actO g A) ⊗ₖ 1 at hk
  change (∑ A, S.E (actV g σ) (actO g A) ⊗ₖ (1 : Matrix β β ℂ)) = 1
  rw [← hk, hs, Matrix.one_kronecker_one]
private lemma inner_hu {d t : ℕ} {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (S : QStrategy d t α β) (htd : t ≤ d)
    (σ : Vertex d) (A : Output d t) : (weightedCore S).inner hvec (uvec S σ A) = 1 := by
  classical
  have heq : ∀ A', (weightedCore S).inner hvec (uvec S σ A') =
      (weightedCore S).inner hvec (uvec S σ A) := by
    intro A'
    change n d t / (Fintype.card (G d) : ℝ) *
      ∑ g, pairTrace S.ρ 1 (S.E (actV g σ) (actO g A') ⊗ₖ 1) =
        n d t / (Fintype.card (G d) : ℝ) *
          ∑ g, pairTrace S.ρ 1 (S.E (actV g σ) (actO g A) ⊗ₖ 1)
    congr 1
    exact orbit_sum_constant (fun σ A => pairTrace S.ρ 1 (S.E σ A ⊗ₖ 1)) σ σ A' A
  let L : VG d α β →+ ℝ := {
    toFun := (weightedCore S).inner hvec
    map_zero' := @InnerProductSpace.Core.inner_zero_right ℝ _ _ _ _ (weightedCore S) hvec
    map_add' := fun x y =>
      @InnerProductSpace.Core.inner_add_right ℝ _ _ _ _ (weightedCore S) hvec x y }
  have hs := map_sum L (uvec S σ) Finset.univ
  change (weightedCore S).inner hvec (∑ A, uvec S σ A) =
    ∑ A, (weightedCore S).inner hvec (uvec S σ A) at hs
  rw [sum_uvec, inner_hh] at hs
  have hsum : (∑ A', (weightedCore S).inner hvec (uvec S σ A')) =
      ∑ _ : Output d t, (weightedCore S).inner hvec (uvec S σ A) :=
    Finset.sum_congr rfl (fun A' _ => heq A')
  rw [hsum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  have hc : (Fintype.card (Output d t) : ℝ) = n d t := by
    dsimp only [Output, n]
    rw [Fintype.card_finset_len, Fintype.card_fin]
  rw [hc] at hs
  have hn : n d t ≠ 0 := by
    dsimp only [n]
    exact_mod_cast (Nat.choose_pos htd).ne'
  apply mul_left_cancel₀ hn
  rw [mul_one]
  exact hs.symm
private lemma inner_qu {d t : ℕ} {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (S : QStrategy d t α β) (htd : t ≤ d)
    (σ : Vertex d) (A : Output d t) :
    (weightedCore S).inner (uvec S σ A) (uvec S σ A) ≤ 1 :=
  (inner_u_budget S σ A).trans_eq (inner_hu S htd σ A)
private lemma inner_pair_budget {d t : ℕ} {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (S : QStrategy d t α β) (htd : t ≤ d)
    (σ : Vertex d) (A A' : Output d t) (hAA : A ≠ A') :
    (weightedCore S).inner (uvec S σ A + uvec S σ A')
      (uvec S σ A + uvec S σ A') ≤ 2 := by
  classical
  calc
    (weightedCore S).inner (uvec S σ A + uvec S σ A')
        (uvec S σ A + uvec S σ A') ≤
      (weightedCore S).inner hvec (uvec S σ A + uvec S σ A') := by
      change n d t / (Fintype.card (G d) : ℝ) *
        ∑ g, pairTrace S.ρ (uvec S σ A g + uvec S σ A' g)
          (uvec S σ A g + uvec S σ A' g) ≤
        n d t / (Fintype.card (G d) : ℝ) *
          ∑ g, pairTrace S.ρ 1 (uvec S σ A g + uvec S σ A' g)
      apply mul_le_mul_of_nonneg_left _ (by dsimp only [n]; positivity)
      apply Finset.sum_le_sum
      intro g hg
      have hne : actO g A ≠ actO g A' := fun he => hAA ((actO_equiv g).injective he)
      have hb := effect_budget S (actV g σ) {actO g A, actO g A'}
      dsimp only [effect] at hb
      rw [Finset.sum_pair hne] at hb
      dsimp only [uvec]
      change pairTrace S.ρ
        (S.E (actV g σ) (actO g A) ⊗ₖ 1 + S.E (actV g σ) (actO g A') ⊗ₖ 1)
        (S.E (actV g σ) (actO g A) ⊗ₖ 1 + S.E (actV g σ) (actO g A') ⊗ₖ 1) ≤
        pairTrace S.ρ 1
          (S.E (actV g σ) (actO g A) ⊗ₖ 1 + S.E (actV g σ) (actO g A') ⊗ₖ 1)
      rw [← Matrix.add_kronecker]
      exact hb
    _ = 2 := by
      rw [@InnerProductSpace.Core.inner_add_right ℝ _ _ _ _ (weightedCore S),
        inner_hu S htd σ A, inner_hu S htd σ A']
      norm_num
private lemma sum_vvec {d t : ℕ} {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (S : QStrategy d t α β) (τ : Vertex d) :
    ∑ B, vvec S τ B = hvec := by
  classical
  funext g
  rw [Finset.sum_apply]
  dsimp only [vvec, hvec]
  have hs : (∑ B, S.F (actV g τ) (actO g B)) = 1 :=
    (Fintype.sum_equiv (actO_equiv g)
      (fun B => S.F (actV g τ) (actO g B)) (S.F (actV g τ)) (fun _ => rfl)).trans
        (S.F_sum (actV g τ))
  have hk := map_sum ((Matrix.kroneckerBilinear (R := ℂ) (α := ℂ))
    (1 : Matrix α α ℂ)) (fun B => S.F (actV g τ) (actO g B)) Finset.univ
  change (1 : Matrix α α ℂ) ⊗ₖ (∑ B, S.F (actV g τ) (actO g B)) =
    ∑ B, 1 ⊗ₖ S.F (actV g τ) (actO g B) at hk
  change (∑ B, (1 : Matrix α α ℂ) ⊗ₖ S.F (actV g τ) (actO g B)) = 1
  rw [← hk, hs, Matrix.one_kronecker_one]
private lemma inner_hv {d t : ℕ} {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (S : QStrategy d t α β) (htd : t ≤ d)
    (τ : Vertex d) (B : Output d t) : (weightedCore S).inner hvec (vvec S τ B) = 1 := by
  classical
  have heq : ∀ B', (weightedCore S).inner hvec (vvec S τ B') =
      (weightedCore S).inner hvec (vvec S τ B) := by
    intro B'
    change n d t / (Fintype.card (G d) : ℝ) *
      ∑ g, pairTrace S.ρ 1 (1 ⊗ₖ S.F (actV g τ) (actO g B')) =
        n d t / (Fintype.card (G d) : ℝ) *
          ∑ g, pairTrace S.ρ 1 (1 ⊗ₖ S.F (actV g τ) (actO g B))
    congr 1
    exact orbit_sum_constant (fun τ B => pairTrace S.ρ 1 (1 ⊗ₖ S.F τ B)) τ τ B' B
  let L : VG d α β →+ ℝ := {
    toFun := (weightedCore S).inner hvec
    map_zero' := @InnerProductSpace.Core.inner_zero_right ℝ _ _ _ _ (weightedCore S) hvec
    map_add' := fun x y =>
      @InnerProductSpace.Core.inner_add_right ℝ _ _ _ _ (weightedCore S) hvec x y }
  have hs := map_sum L (vvec S τ) Finset.univ
  change (weightedCore S).inner hvec (∑ B, vvec S τ B) =
    ∑ B, (weightedCore S).inner hvec (vvec S τ B) at hs
  rw [sum_vvec, inner_hh] at hs
  have hsum : (∑ B', (weightedCore S).inner hvec (vvec S τ B')) =
      ∑ _ : Output d t, (weightedCore S).inner hvec (vvec S τ B) :=
    Finset.sum_congr rfl (fun B' _ => heq B')
  rw [hsum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  have hc : (Fintype.card (Output d t) : ℝ) = n d t := by
    dsimp only [Output, n]
    rw [Fintype.card_finset_len, Fintype.card_fin]
  rw [hc] at hs
  have hn : n d t ≠ 0 := by
    dsimp only [n]
    exact_mod_cast (Nat.choose_pos htd).ne'
  apply mul_left_cancel₀ hn
  rw [mul_one]
  exact hs.symm
private lemma inner_qv {d t : ℕ} {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (S : QStrategy d t α β) (htd : t ≤ d)
    (τ : Vertex d) (B : Output d t) :
    (weightedCore S).inner (vvec S τ B) (vvec S τ B) ≤ 1 := by
  classical
  apply le_trans _ (inner_hv S htd τ B).le
  change n d t / (Fintype.card (G d) : ℝ) *
    ∑ g, pairTrace S.ρ (vvec S τ B g) (vvec S τ B g) ≤
      n d t / (Fintype.card (G d) : ℝ) * ∑ g, pairTrace S.ρ 1 (vvec S τ B g)
  apply mul_le_mul_of_nonneg_left _ (by dsimp only [n]; positivity)
  apply Finset.sum_le_sum
  intro g hg
  have hf := S.F_psd (actV g τ) (actO g B)
  have hle : S.F (actV g τ) (actO g B) ≤ 1 := by
    rw [← S.F_sum (actV g τ)]
    calc
      S.F (actV g τ) (actO g B) = ∑ b ∈ {actO g B}, S.F (actV g τ) b :=
        (Finset.sum_singleton _ _).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun b _ _ => (S.F_psd _ b).nonneg)
  exact trace_budget _ _ S.rho_psd (Matrix.PosSemidef.one.kronecker hf)
    (kron_sq_le _ (contraction_sq _ hf hle)).2
private lemma pair_perm {d t : ℕ} (A B A' B' : Output d t)
    (hAB : Disjoint A.val B.val) (hAB' : Disjoint A'.val B'.val) :
    ∃ p : Equiv.Perm (Fin d), pmap p A.val = A'.val ∧ pmap p B.val = B'.val := by
  classical
  let ea : A.val ≃ A'.val := Fintype.equivOfCardEq (by simp [A.property, A'.property])
  let eb : B.val ≃ B'.val := Fintype.equivOfCardEq (by simp [B.property, B'.property])
  let e := (Equiv.Finset.union A.val B.val hAB).symm |>.trans
    (Equiv.sumCongr ea eb) |>.trans (Equiv.Finset.union A'.val B'.val hAB')
  let q : Equiv.Perm (Fin d) := e.extendSubtype
  have hq : ∀ x (hx : x ∈ A.val ∪ B.val), q x = (e ⟨x, hx⟩).val := by
    exact fun x hx => e.extendSubtype_apply_of_mem x hx
  refine ⟨q, Finset.eq_of_subset_of_card_le ?_ (by rw [pmap_card, A.property, A'.property]),
    Finset.eq_of_subset_of_card_le ?_ (by rw [pmap_card, B.property, B'.property])⟩
  · intro x hx; obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    change q y ∈ A'.val
    rw [hq y (Finset.mem_union_left _ hy)]
    dsimp only [e, Equiv.trans_apply]
    rw [Equiv.Finset.union_symm_left hAB hy]
    exact (ea ⟨y, hy⟩).property
  · intro x hx; obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    change q y ∈ B'.val
    rw [hq y (Finset.mem_union_right _ hy)]
    dsimp only [e, Equiv.trans_apply]
    rw [Equiv.Finset.union_symm_right hAB hy]
    exact (eb ⟨y, hy⟩).property
private lemma wins_act {d t : ℕ} (g : G d) (σ τ : Vertex d) (A B : Output d t) :
    Wins (actV g σ) (actV g τ) (actO g A) (actO g B) ↔ Wins σ τ A B := by
  dsimp only [Wins, actV, actO]
  rw [symmDiff_symmDiff_symmDiff_comm, symmDiff_self, bot_symmDiff,
    ← pmap_symmDiff g.2 σ τ]
  dsimp only [pmap]
  rw [Finset.disjoint_map, ← Finset.map_union, Finset.map_inj]
private lemma winning_transitive {d t : ℕ} (σ τ σ' τ' : Vertex d)
    (A B A' B' : Output d t) (hw : Wins σ τ A B) (hw' : Wins σ' τ' A' B') :
    ∃ g : G d, actV g σ = σ' ∧ actV g τ = τ' ∧ actO g A = A' ∧ actO g B = B' := by
  obtain ⟨p, hpA, hpB⟩ := pair_perm A B A' B' hw.1 hw'.1
  let g : G d := (σ' ∆ pmap p σ, p)
  have hs : actV g σ = σ' := symmDiff_symmDiff_cancel_right _ _
  have ha : actO g A = A' := Subtype.ext hpA
  have hb : actO g B = B' := Subtype.ext hpB
  have hx := (wins_act g σ τ A B).mpr hw
  rw [hs, ha, hb] at hx
  have hxx := hx.2
  rw [hw'.2] at hxx
  have ht := congrArg (fun s => σ' ∆ s) hxx
  rw [symmDiff_symmDiff_cancel_left, symmDiff_symmDiff_cancel_left] at ht
  exact ⟨g, hs, ht.symm, ha, hb⟩
private def flip {d t : ℕ} (η : Vertex d) (A : Output d t) : Output d t := by
  classical
  exact if h : η.card = 2 * t ∧ A.val ⊆ η then
    ⟨η \ A.val, by rw [Finset.card_sdiff_of_subset h.2, h.1, A.property]; omega⟩ else A
private lemma flip_involutive {d t : ℕ} (η : Vertex d) :
    Function.Involutive (flip (t := t) η) := by
  classical
  intro A
  by_cases h : η.card = 2 * t ∧ A.val ⊆ η
  · dsimp only [flip]; rw [dif_pos h, dif_pos ⟨h.1, Finset.sdiff_subset⟩]
    apply Subtype.ext
    change η \ (η \ A.val) = A.val
    rw [Finset.sdiff_sdiff_self_left, Finset.inter_eq_right.mpr h.2]
  · dsimp only [flip]; rw [dif_neg h, dif_neg h]
private def flipEquiv {d t : ℕ} (η : Vertex d) : Output d t ≃ Output d t :=
  ⟨flip η, flip η, flip_involutive η, flip_involutive η⟩
private lemma wins_iff {d t : ℕ} (σ τ : Vertex d) (A B : Output d t)
    (hp : Promised d t σ τ) :
    Wins σ τ A B ↔ A.val ⊆ σ ∆ τ ∧ B = flip (σ ∆ τ) A := by
  classical
  constructor
  · intro h
    have hs : A.val ⊆ σ ∆ τ := h.2 ▸ Finset.subset_union_left
    refine ⟨hs, ?_⟩
    dsimp only [flip]; rw [dif_pos ⟨hp, hs⟩]; apply Subtype.ext
    change B.val = (σ ∆ τ) \ A.val
    rw [← h.2, Finset.union_sdiff_left, Finset.sdiff_eq_self_iff_disjoint.mpr h.1.symm]
  · rintro ⟨hs, rfl⟩
    dsimp only [flip]; rw [dif_pos ⟨hp, hs⟩]
    exact ⟨Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hs⟩
open scoped Classical in
private lemma winning_sum {d t : ℕ} (σ τ : Vertex d) (hp : Promised d t σ τ) (r : ℝ) :
    (∑ A : Output d t, ∑ B : Output d t, if Wins σ τ A B then r else 0) =
      (Nat.choose (2 * t) t : ℝ) * r := by
  classical
  have hr : ∀ A : Output d t, (∑ B : Output d t, if Wins σ τ A B then r else 0) =
      if A.val ⊆ σ ∆ τ then r else 0 := by
    intro A; simp_rw [wins_iff σ τ A _ hp]
    by_cases hs : A.val ⊆ σ ∆ τ <;> simp [hs]
  simp_rw [hr]
  rw [← Finset.sum_filter]
  have he : (∑ A ∈ Finset.univ.filter (fun A : Output d t => A.val ⊆ σ ∆ τ), r) =
      ∑ T ∈ (σ ∆ τ).powersetCard t, r := by
    apply Finset.sum_bij (fun A _ => A.val)
    · intro A hA
      exact Finset.mem_powersetCard.mpr ⟨(Finset.mem_filter.mp hA).2, A.property⟩
    · intro A _ A' _ he; exact Subtype.ext he
    · intro T hT
      refine ⟨⟨T, (Finset.mem_powersetCard.mp hT).2⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_powersetCard.mp hT).1⟩
    · intro A hA; rfl
  rw [he, Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard]
  exact congrArg (fun k : ℕ => (k : ℝ) * r) (congrArg (fun k => Nat.choose k t) hp)
private lemma inputs_pos {d t : ℕ} (hd : 2 * t ≤ d) : 0 < (Inputs d t).card := by
  classical
  obtain ⟨η, _, hη⟩ := Finset.exists_subset_card_eq
    (show 2 * t ≤ (Finset.univ : Vertex d).card by
      rw [Finset.card_univ, Fintype.card_fin]; exact hd)
  apply Finset.card_pos.mpr
  refine ⟨(∅, η), ?_⟩
  change (∅, η) ∈ Finset.univ.filter (fun p : Vertex d × Vertex d => Promised d t p.1 p.2)
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  change (∅ ∆ η).card = 2 * t
  simpa only [Finset.symmDiff_def, Finset.empty_sdiff, Finset.sdiff_empty,
    Finset.empty_union] using hη
private def actVEquiv {d : ℕ} (g : G d) : Vertex d ≃ Vertex d := by
  refine ⟨actV g, fun s => pmap g.2⁻¹ (g.1 ∆ s), ?_, ?_⟩
  · intro s; dsimp only [actV]
    rw [symmDiff_symmDiff_cancel_left, pmap_comp, inv_mul_cancel, pmap_one]
  · intro s; dsimp only [actV]
    rw [pmap_comp, mul_inv_cancel, pmap_one, symmDiff_symmDiff_cancel_left]
private lemma promised_act {d t : ℕ} (g : G d) (σ τ : Vertex d) :
    Promised d t (actV g σ) (actV g τ) ↔ Promised d t σ τ := by
  dsimp only [Promised, actV]
  rw [symmDiff_symmDiff_symmDiff_comm, symmDiff_self, bot_symmDiff,
    ← pmap_symmDiff, pmap_card]
private lemma value_transport {d t : ℕ} (P : Correlation d t) (g : G d) :
    value (fun σ τ A B => P (actV g σ) (actV g τ) (actO g A) (actO g B)) = value P := by
  classical
  let e := Equiv.prodCongr (actVEquiv g) (actVEquiv g)
  have hm : ∀ p, p ∈ Inputs d t ↔ e p ∈ Inputs d t := by
    intro p; change p ∈ Finset.univ.filter _ ↔ e p ∈ Finset.univ.filter _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (promised_act g p.1 p.2).symm
  let ei : (Inputs d t) ≃ (Inputs d t) := e.subtypeEquiv hm
  dsimp only [value]
  congr 1
  conv_lhs => rw [← Finset.sum_coe_sort]
  conv_rhs => rw [← Finset.sum_coe_sort]
  apply Fintype.sum_equiv ei
  intro p
  apply Fintype.sum_equiv (actO_equiv g)
  intro A
  apply Fintype.sum_equiv (actO_equiv g)
  intro B
  change (if Wins p.val.1 p.val.2 A B then _ else 0) =
    (if Wins (actV g p.val.1) (actV g p.val.2) (actO g A) (actO g B) then _ else 0)
  rw [wins_act]
  rfl
private lemma value_sum {d t : ℕ} {ι : Type*} [Fintype ι]
    (P : ι → Correlation d t) (k : ℝ) :
    value (fun σ τ A B => k * ∑ i, P i σ τ A B) = k * ∑ i, value (P i) := by
  classical
  have hi : ∀ σ τ A B, (if Wins σ τ A B then k * ∑ i, P i σ τ A B else 0) =
      k * ∑ i, if Wins σ τ A B then P i σ τ A B else 0 := by
    intro σ τ A B; split_ifs <;> simp
  dsimp only [value]
  simp_rw [hi, ← Finset.mul_sum]
  have he : (∑ p ∈ Inputs d t, ∑ A, ∑ B, ∑ i, if Wins p.1 p.2 A B then
      P i p.1 p.2 A B else 0) =
      ∑ i, ∑ p ∈ Inputs d t, ∑ A, ∑ B, if Wins p.1 p.2 A B then P i p.1 p.2 A B else 0 := by
    simp_rw [Finset.sum_comm (f := fun B i => if Wins _ _ _ B then P i _ _ _ B else 0)]
    simp_rw [Finset.sum_comm (f := fun A i => ∑ B, if Wins _ _ A B then P i _ _ A B else 0)]
    rw [Finset.sum_comm]
  rw [he, ← Finset.sum_div]
  ring
private lemma value_constant {d t : ℕ} (hd : 2 * t ≤ d) (P : Correlation d t) (r : ℝ)
    (h : ∀ σ τ A B, Wins σ τ A B → P σ τ A B = r) :
    value P = (Nat.choose (2 * t) t : ℝ) * r := by
  classical
  have hp : ((Inputs d t).card : ℝ) ≠ 0 := by exact_mod_cast (inputs_pos hd).ne'
  dsimp only [value]
  have hs : ∀ p ∈ Inputs d t, (∑ A, ∑ B, if Wins p.1 p.2 A B then P p.1 p.2 A B else 0) =
      (Nat.choose (2 * t) t : ℝ) * r := by
    intro p hp
    have hpr : Promised d t p.1 p.2 := (Finset.mem_filter.mp hp).2
    convert winning_sum p.1 p.2 hpr r using 1
    apply Finset.sum_congr rfl; intro A hA
    apply Finset.sum_congr rfl; intro B hB
    split_ifs with hw
    · exact h _ _ _ _ hw
    · rfl
  rw [Finset.sum_congr rfl hs, Finset.sum_const, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ hp
private lemma inner_winning_constant {d t : ℕ} {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (S : QStrategy d t α β)
    (σ τ σ' τ' : Vertex d) (A B A' B' : Output d t)
    (hw : Wins σ τ A B) (hw' : Wins σ' τ' A' B') :
    (weightedCore S).inner (uvec S σ A) (vvec S τ B) =
      (weightedCore S).inner (uvec S σ' A') (vvec S τ' B') := by
  obtain ⟨h, hs, ht, ha, hb⟩ := winning_transitive σ τ σ' τ' A B A' B' hw hw'
  rw [inner_uv_eq, inner_uv_eq, ← hs, ← ht, ← ha, ← hb]
  congr 1
  simp_rw [← actV_rightMul, ← actO_rightMul]
  exact (sum_rightMul h (fun g => S.prob (actV g σ) (actV g τ) (actO g A) (actO g B))).symm
private lemma winning_cross {d t : ℕ} {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (S : QStrategy d t α β) (hd : 2 * t ≤ d)
    (σ τ : Vertex d) (A B : Output d t) (hw : Wins σ τ A B) :
    (weightedCore S).inner (uvec S σ A) (vvec S τ B) =
      n d t * value S.prob / (Nat.choose (2 * t) t : ℝ) := by
  classical
  let P : Correlation d t := fun σ τ A B => (weightedCore S).inner (uvec S σ A) (vvec S τ B)
  have hconst := value_constant hd P (P σ τ A B)
    (fun σ' τ' A' B' hw' => inner_winning_constant S σ' τ' σ τ A' B' A B hw' hw)
  have havg : value P = n d t * value S.prob := by
    have he : P = fun σ τ A B => n d t / (Fintype.card (G d) : ℝ) *
        ∑ g, S.prob (actV g σ) (actV g τ) (actO g A) (actO g B) := by
      funext σ τ A B; exact inner_uv_eq S σ τ A B
    rw [he, value_sum]
    simp_rw [value_transport]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hc : (Fintype.card (G d) : ℝ) ≠ 0 := by
      let _ : Nonempty (Vertex d) := ⟨∅⟩
      let _ : Nonempty (Equiv.Perm (Fin d)) := ⟨Equiv.refl _⟩
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card (G d) ≠ 0)
    rw [← mul_assoc, div_mul_cancel₀ _ hc]
  have hc : (Nat.choose (2 * t) t : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show t ≤ 2 * t by omega)).ne'
  apply (eq_div_iff hc).mpr
  rw [havg] at hconst
  exact (mul_comm _ _).trans hconst.symm
private lemma exists_win {d t : ℕ} (hd : 2 * t ≤ d) :
    ∃ σ τ : Vertex d, ∃ A B : Output d t, Wins σ τ A B := by
  classical
  obtain ⟨p, hp⟩ := Finset.card_pos.mp (inputs_pos hd)
  have hpr : Promised d t p.1 p.2 := (Finset.mem_filter.mp hp).2
  obtain ⟨T, hT, hc⟩ := Finset.exists_subset_card_eq
    (show t ≤ (p.1 ∆ p.2).card by change _ = 2 * t at hpr; omega)
  exact ⟨p.1, p.2, ⟨T, hc⟩, flip (p.1 ∆ p.2) ⟨T, hc⟩,
    (wins_iff _ _ _ _ hpr).mpr ⟨hT, rfl⟩⟩
private lemma quantum_bound {d t : ℕ} {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (S : QStrategy d t α β)
    (ht : 2 ≤ t) (hd : 2 * t < d) :
    value S.prob ≤ ((Nat.choose (2 * t) t : ℝ) / n d t) * (1 - kappa d t) := by
  classical
  let δ := 1 - n d t * value S.prob / (Nat.choose (2 * t) t : ℝ)
  obtain ⟨σ, τ, A, B, hw⟩ := exists_win hd.le
  have hcross := winning_cross S hd.le σ τ A B hw
  have hnonneg : 0 ≤ (weightedCore S).inner (uvec S σ A) (vvec S τ B) := by
    rw [inner_uv_eq]
    apply mul_nonneg (by dsimp only [n]; positivity)
    apply Finset.sum_nonneg; intro g hg
    exact RHLinalg.trace_mul_nonneg_of_posSemidef S.rho_psd
      ((S.E_psd _ _).kronecker (S.F_psd _ _))
  have hcs := @InnerProductSpace.Core.inner_mul_inner_self_le ℝ _ _ _ _
    (weightedCore S) (uvec S σ A) (vvec S τ B)
  have hsym := (weightedCore S).conj_inner_symm (vvec S τ B) (uvec S σ A)
  simp only [RCLike.conj_to_real] at hsym
  rw [← hsym] at hcs
  have hcs' : ((weightedCore S).inner (uvec S σ A) (vvec S τ B)) ^ 2 ≤
      (weightedCore S).inner (uvec S σ A) (uvec S σ A) *
        (weightedCore S).inner (vvec S τ B) (vvec S τ B) := by
    simpa only [Real.norm_eq_abs, ← sq, sq_abs, RCLike.re_to_real] using hcs
  have hqu := inner_qu S (by omega) σ A
  have hqv := inner_qv S (by omega) τ B
  have hq0 := (weightedCore S).re_inner_nonneg (uvec S σ A)
  change 0 ≤ (weightedCore S).inner (uvec S σ A) (uvec S σ A) at hq0
  have hδ0 : 0 ≤ δ := by
    dsimp only [δ]; rw [← hcross]
    nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hqv)]
  have hδ1 : δ ≤ 1 := by dsimp only [δ]; rw [← hcross]; linarith
  have hg := vector_system_gap (weightedCore S) ht hd hvec (uvec S) (vvec S) δ hδ0 hδ1
    (inner_hh S) (inner_hu S (by omega)) (inner_hv S (by omega))
    (inner_qu S (by omega)) (inner_qv S (by omega)) (inner_pair_budget S (by omega))
    (fun σ τ A B hw => by rw [winning_cross S hd.le σ τ A B hw]; dsimp only [δ]; ring)
  have hn : 0 < n d t := by dsimp only [n]; exact_mod_cast Nat.choose_pos (by omega : t ≤ d)
  have hc : 0 < (Nat.choose (2 * t) t : ℝ) := by
    exact_mod_cast Nat.choose_pos (show t ≤ 2 * t by omega)
  dsimp only [δ] at hg
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hn).mpr
  have hh := (div_le_iff₀ hc).mp (show n d t * value S.prob /
    (Nat.choose (2 * t) t : ℝ) ≤ 1 - kappa d t by linarith)
  convert hh using 1 <;> ring
private def nsP (d t : ℕ) : Correlation d t := by
  classical
  exact fun σ τ A B => if B = flip (σ ∆ τ) A then 1 / n d t else 0
private lemma nsP_isNS {d t : ℕ} (htd : t ≤ d) : IsNS (nsP d t) := by
  classical
  have hn : n d t ≠ 0 := by dsimp only [n]; exact_mod_cast (Nat.choose_pos htd).ne'
  have hc : (Fintype.card (Output d t) : ℝ) = n d t := by
    dsimp only [Output, n]; rw [Fintype.card_finset_len, Fintype.card_fin]
  have row : ∀ σ τ A, (∑ B, nsP d t σ τ A B) = 1 / n d t := by
    intro σ τ A; dsimp only [nsP]; simp
  have col : ∀ σ τ B, (∑ A, nsP d t σ τ A B) = 1 / n d t := by
    intro σ τ B; dsimp only [nsP]
    have he := Fintype.sum_equiv (flipEquiv (σ ∆ τ))
      (fun A => if B = flip (σ ∆ τ) A then 1 / n d t else 0)
      (fun A => if B = A then 1 / n d t else 0) (fun _ => rfl)
    rw [he]; simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro σ τ A B; dsimp only [nsP]; split_ifs
    · dsimp only [n]; positivity
    · exact le_rfl
  · intro σ τ; simp_rw [row]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc]
    exact mul_one_div_cancel hn
  · intro σ τ τ' A; rw [row, row]
  · intro σ σ' τ B; rw [col, col]
private lemma nsP_value {d t : ℕ} (hd : 2 * t ≤ d) :
    value (nsP d t) = (Nat.choose (2 * t) t : ℝ) / n d t := by
  classical
  have h : ∀ σ τ A B, Wins σ τ A B → nsP d t σ τ A B = 1 / n d t := by
    intro σ τ A B hw
    have hp : Promised d t σ τ := by
      change (σ ∆ τ).card = 2 * t
      rw [← hw.2, Finset.card_union_of_disjoint hw.1, A.property, B.property]; omega
    dsimp only [nsP]; rw [if_pos ((wins_iff σ τ A B hp).mp hw).2]
  exact (value_constant hd (nsP d t) (1 / n d t) h).trans (by ring)
private lemma ns_bound {d t : ℕ} (hd : 2 * t ≤ d) (P : Correlation d t) (hp : IsNS P) :
    value P ≤ 1 := by
  classical
  have hc : 0 < ((Inputs d t).card : ℝ) := by exact_mod_cast inputs_pos hd
  dsimp only [value]
  apply (div_le_iff₀ hc).mpr
  have hr : ∀ p ∈ Inputs d t,
      (∑ A, ∑ B, if Wins p.1 p.2 A B then P p.1 p.2 A B else 0) ≤ 1 := by
    intro p hpr
    rw [← hp.2.1 p.1 p.2]
    apply Finset.sum_le_sum; intro A hA
    apply Finset.sum_le_sum; intro B hB
    split_ifs
    · exact le_rfl
    · exact hp.1 _ _ _ _
  convert Finset.sum_le_sum hr using 1; simp
private def deterministic {d t : ℕ} (A : Output d t) : QStrategy d t Unit Unit := by
  classical
  exact {
    ρ := 1
    rho_psd := Matrix.PosSemidef.one
    rho_trace := by rw [Matrix.trace_one]; simp
    E := fun _ B => if B = A then 1 else 0
    F := fun _ B => if B = A then 1 else 0
    E_psd := fun _ B => by
      by_cases h : B = A
      · rw [if_pos h]; exact Matrix.PosSemidef.one
      · rw [if_neg h]; exact Matrix.PosSemidef.zero
    F_psd := fun _ B => by
      by_cases h : B = A
      · rw [if_pos h]; exact Matrix.PosSemidef.one
      · rw [if_neg h]; exact Matrix.PosSemidef.zero
    E_sum := fun _ => by simp
    F_sum := fun _ => by simp }
private lemma q_nonempty {d t : ℕ} (htd : t ≤ d) : (QValues d t).Nonempty := by
  classical
  obtain ⟨T, _, hT⟩ := Finset.exists_subset_card_eq
    (show t ≤ (Finset.univ : Vertex d).card by rw [Finset.card_univ, Fintype.card_fin]; exact htd)
  let S := deterministic (⟨T, hT⟩ : Output d t)
  refine ⟨value S.prob, S.prob, ?_, rfl⟩
  exact ⟨Unit, Unit, inferInstance, inferInstance, inferInstance, inferInstance, S, rfl⟩
theorem result : claim := by
  intro t d ht hd
  have hn : 0 < n d t := by dsimp only [n]; exact_mod_cast Nat.choose_pos (by omega : t ≤ d)
  have hc : 0 < (Nat.choose (2 * t) t : ℝ) := by
    exact_mod_cast Nat.choose_pos (show t ≤ 2 * t by omega)
  have hk : 0 < kappa d t := by dsimp only [kappa]; positivity
  have hq : omegaQ d t ≤ ((Nat.choose (2 * t) t : ℝ) / n d t) * (1 - kappa d t) := by
    apply csSup_le (q_nonempty (by omega))
    rintro r ⟨P, ⟨α, β, fα, fβ, dα, dβ, S, hS⟩, hr⟩
    subst P; subst r
    exact quantum_bound S ht hd
  have hns : (Nat.choose (2 * t) t : ℝ) / n d t ≤ omegaNS d t := by
    apply le_csSup
    · refine ⟨1, ?_⟩
      rintro r ⟨P, hp, rfl⟩; exact ns_bound hd.le P hp
    · exact ⟨nsP d t, nsP_isNS (by omega), nsP_value hd.le⟩
  exact (hq.trans_lt (mul_lt_of_lt_one_right (div_pos hc hn) (by linarith))).trans_le hns
end QuantumBridge
end D5.S3.Quantum.Entanglement.HypercubeRendezvousQuantumGap

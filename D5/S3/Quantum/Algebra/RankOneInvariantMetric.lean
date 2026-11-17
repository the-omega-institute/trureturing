/- GID: D5/S3/Quantum/Algebra/RankOneInvariantMetric
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/RankOneInvariantMetric
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A finite real metric Lie algebra with a regular centralizer line has dimension one or three. -/

import D5.S3.QuadraticForms.PositiveDefiniteWilliamson
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Algebra.Lie.Sl2
import Mathlib.Algebra.Lie.BaseChange
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic
import Mathlib.Analysis.Complex.Polynomial.Basic

namespace D5.S3.Quantum.Algebra.RankOneInvariantMetric

open Module
open scoped InnerProductSpace RealInnerProductSpace TensorProduct
noncomputable section
universe u
variable {L : Type u} [NormedAddCommGroup L] [InnerProductSpace ℝ L]
  [FiniteDimensional ℝ L]

private theorem min_frequency (D : L →ₗ[ℝ] L)
    (hD : ∀ x y, ⟪D x,y⟫_ℝ = -⟪x,D y⟫_ℝ) (hDn : D ≠ 0) :
    ∃ (μ : ℝ) (u : L), 0 < μ ∧ ‖u‖ = 1 ∧
      D (D u) = -(μ^2) • u ∧
      ∀ (ρ : ℝ) (x : L), 0 < ρ → x ≠ 0 →
        D (D x) = -(ρ^2) • x → μ ≤ ρ := by
  classical
  let E := WithLp 2 (L × L)
  let A : E →ₗ[ℝ] E :=
    (WithLp.linearEquiv 2 ℝ (L × L)).symm.toLinearMap ∘ₗ
      (D.prodMap D) ∘ₗ (WithLp.linearEquiv 2 ℝ (L × L)).toLinearMap
  have hA (x y : E) : ⟪A x,y⟫_ℝ = -⟪x,A y⟫_ℝ := by
    change ⟪D (WithLp.ofLp x).1,(WithLp.ofLp y).1⟫_ℝ +
      ⟪D (WithLp.ofLp x).2,(WithLp.ofLp y).2⟫_ℝ =
      -(⟪(WithLp.ofLp x).1,D (WithLp.ofLp y).1⟫_ℝ +
        ⟪(WithLp.ofLp x).2,D (WithLp.ofLp y).2⟫_ℝ)
    rw [hD,hD]; ring
  have hdim : Even (finrank ℝ E) := by
    have he := (WithLp.linearEquiv 2 ℝ (L × L)).finrank_eq
    rw [Module.finrank_prod] at he
    exact ⟨finrank ℝ L, by simpa [two_mul] using he⟩
  obtain ⟨κ,inst,b,ν,hν,hl,hr⟩ :=
    D5.S3.QuadraticForms.PositiveDefiniteWilliamson.skew_paired_basis_induction
      (finrank ℝ E) A hA rfl hdim
  let : Fintype κ := inst
  have hAnonzero : A ≠ 0 := by
    intro hz
    apply hDn
    ext x
    have hh := DFunLike.congr_fun hz (WithLp.toLp 2 (x,0))
    exact congrArg (fun y : E => (WithLp.ofLp y).1) hh
  have hex : ∃ k, 0 < ν k := by
    by_contra! hh
    have hzero : ∀ k, ν k = 0 := fun k => le_antisymm (hh k) (hν k)
    apply hAnonzero
    apply b.toBasis.ext
    intro i
    cases i with
    | inl k => simp [hl,hzero]
    | inr k => simp [hr,hzero]
  obtain ⟨k,hk,hmin⟩ := Set.exists_min_image {k : κ | 0 < ν k} ν
    (Set.toFinite _) hex
  have hkpos : 0 < ν k := hk
  have hsquare (i : κ ⊕ κ) : A (A (b i)) =
      -(ν (Sum.elim id id i)^2) • b i := by
    cases i with
    | inl j => rw [hl,map_smul,hr,smul_smul]; simp; ring_nf
    | inr j => rw [hr,map_smul,hl,smul_smul]; simp; ring_nf
  have hminall (ρ : ℝ) (x : E) (hρ : 0 < ρ) (hx : x ≠ 0)
      (he : A (A x) = -(ρ^2) • x) : ν k ≤ ρ := by
    have hsym : (A ∘ₗ A).IsSymmetric := by
      intro p q
      simp only [LinearMap.comp_apply]
      rw [hA,hA,neg_neg]
    have hcoord : ∃ i, ⟪b i,x⟫_ℝ ≠ 0 := by
      by_contra! hh
      apply hx
      have hz : b.repr x = 0 := by
        ext i
        change b.repr x i = 0
        rw [b.repr_apply_apply]
        exact hh i
      exact b.repr.injective (by simpa using hz)
    obtain ⟨i,hi⟩ := hcoord
    have heq := hsym (b i) x
    change ⟪A (A (b i)),x⟫_ℝ = ⟪b i,A (A x)⟫_ℝ at heq
    rw [hsquare,he,real_inner_smul_left,real_inner_smul_right] at heq
    have hsq : ν (Sum.elim id id i)^2 = ρ^2 := by
      nlinarith [mul_right_cancel₀ hi heq]
    have hfreq : ν (Sum.elim id id i) = ρ := by
      nlinarith [hν (Sum.elim id id i)]
    have hm := hmin (Sum.elim id id i) (by simpa [hfreq] using hρ)
    simpa [hfreq] using hm
  let p := (WithLp.ofLp (b (Sum.inl k))).1
  let q := (WithLp.ofLp (b (Sum.inl k))).2
  have hpq : p ≠ 0 ∨ q ≠ 0 := by
    by_contra! hh
    have hbzero : b (Sum.inl k) = 0 := by
      apply WithLp.ofLp_injective
      exact Prod.ext hh.1 hh.2
    exact b.orthonormal.ne_zero _ hbzero
  have hp : D (D p) = -(ν k^2) • p := by
    exact congrArg (fun y : E => (WithLp.ofLp y).1) (hsquare (Sum.inl k))
  have hq : D (D q) = -(ν k^2) • q := by
    exact congrArg (fun y : E => (WithLp.ofLp y).2) (hsquare (Sum.inl k))
  obtain ⟨x,hxn,hxe⟩ : ∃ x : L, x ≠ 0 ∧ D (D x) = -(ν k^2) • x := by
    rcases hpq with hn | hn
    · exact ⟨p,hn,hp⟩
    · exact ⟨q,hn,hq⟩
  refine ⟨ν k,(‖x‖⁻¹ : ℝ) • x,hkpos,?_,?_,?_⟩
  · rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hxn)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hxn)]
  · rw [map_smul,map_smul,hxe,smul_comm]
  · intro ρ y hρ hyn he
    refine hminall ρ (WithLp.toLp 2 (y,0)) hρ ?_ ?_
    · intro hz
      exact hyn (congrArg (fun z : E => (WithLp.ofLp z).1) hz)
    · apply WithLp.ofLp_injective
      change (D (D y),D (D 0)) = (-(ρ^2) • y,-(ρ^2) • (0 : L))
      simp [he]


private theorem min_frame (br : L →ₗ[ℝ] L →ₗ[ℝ] L)
    (halt : ∀ z : L, br z z = 0)
    (hjac : ∀ x y z : L, br x (br y z) = br (br x y) z + br y (br x z))
    (a : L) (ha : ‖a‖ = 1)
    (hinv : ∀ x y z : L, ⟪br x y,z⟫_ℝ = -⟪y,br x z⟫_ℝ)
    (hcent : ∀ z : L, br a z = 0 → ∃ c : ℝ, z = c • a)
    (hn : br a ≠ 0) :
    ∃ (μ : ℝ) (u v : L), 0 < μ ∧ ‖u‖ = 1 ∧ ‖v‖ = 1 ∧
      ⟪a,u⟫_ℝ = 0 ∧ ⟪a,v⟫_ℝ = 0 ∧ ⟪u,v⟫_ℝ = 0 ∧
      br a u = μ • v ∧ br a v = -μ • u ∧ br u v = μ • a ∧
      ∀ (ρ : ℝ) (x : L), 0 < ρ → x ≠ 0 →
        br a (br a x) = -(ρ^2) • x → μ ≤ ρ := by
  let D := br a
  have hD (x y : L) : ⟪D x,y⟫_ℝ = -⟪x,D y⟫_ℝ := hinv a x y
  obtain ⟨μ,u,hμ,hu,hsq,hmin⟩ := min_frequency D hD hn
  have hμ0 : μ ≠ 0 := hμ.ne'
  let v := μ⁻¹ • D u
  have hnorm : ‖D u‖^2 = μ^2 := by
    have hh := hD u (D u)
    simpa [hsq,inner_smul_right,real_inner_self_eq_norm_sq,hu] using hh
  have hv : ‖v‖ = 1 := by
    have hd : ‖D u‖ = μ := by nlinarith [norm_nonneg (D u)]
    simp [v,norm_smul,Real.norm_eq_abs,abs_of_pos hμ,hd,hμ0]
  have huv : ⟪u,v⟫_ℝ = 0 := by
    have hh := hD u u
    have hcomm := real_inner_comm u (D u)
    have hh0 : ⟪u,D u⟫_ℝ = 0 := by linarith
    simp [v,inner_smul_right,hh0]
  have hau : br a u = μ • v := by simp [v,smul_smul,hμ0,D]
  have hav : br a v = -μ • u := by
    change D v = -μ • u
    simp only [v,map_smul,hsq,smul_smul]
    congr 1
    field_simp
  have hau0 : ⟪a,u⟫_ℝ = 0 := by
    have hh := hinv a a v
    rw [halt,inner_zero_left,hav,inner_smul_right] at hh
    exact (mul_eq_zero.mp (by linarith : μ * ⟪a,u⟫_ℝ = 0)).resolve_left hμ0
  have hav0 : ⟪a,v⟫_ℝ = 0 := by
    have hh := hinv a a u
    rw [halt,inner_zero_left,hau,inner_smul_right] at hh
    exact (mul_eq_zero.mp (by linarith : μ * ⟪a,v⟫_ℝ = 0)).resolve_left hμ0
  have hc : br a (br u v) = 0 := by
    rw [hjac,hau,hav]
    simp [halt]
  obtain ⟨c,hc⟩ := hcent (br u v) hc
  have hskew : br u a = -(br a u) := by
    have hh := halt (u+a)
    simp only [map_add,LinearMap.add_apply,halt,zero_add,add_zero] at hh
    exact eq_neg_of_add_eq_zero_right hh
  have hcμ : c = μ := by
    have hh := hinv u v a
    rw [hc,real_inner_smul_left,real_inner_self_eq_norm_sq,ha,
      hskew,hau,inner_neg_right,inner_smul_right,
      real_inner_self_eq_norm_sq,hv] at hh
    nlinarith
  exact ⟨μ,u,v,hμ,hu,hv,hau0,hav0,huv,hau,hav,hcμ ▸ hc,hmin⟩


variable {M : Type u} [AddCommGroup M] [Module ℝ M]
private def rpart : ℂ ⊗[ℝ] M →ₗ[ℝ] M :=
  (TensorProduct.lid ℝ M).toLinearMap ∘ₗ Complex.reLm.rTensor M
private def ipart : ℂ ⊗[ℝ] M →ₗ[ℝ] M :=
  (TensorProduct.lid ℝ M).toLinearMap ∘ₗ Complex.imLm.rTensor M
@[simp] private theorem rpart_tmul (c : ℂ) (x : M) : rpart (c ⊗ₜ[ℝ] x) = c.re • x := by
  simp [rpart]
@[simp] private theorem ipart_tmul (c : ℂ) (x : M) : ipart (c ⊗ₜ[ℝ] x) = c.im • x := by
  simp [ipart]
private theorem decompose (z : ℂ ⊗[ℝ] M) :
    z = (1 : ℂ) ⊗ₜ[ℝ] rpart z + Complex.I ⊗ₜ[ℝ] ipart z := by
  induction z using TensorProduct.inductionOn with
  | tmul c x =>
    simp only [rpart_tmul,ipart_tmul]
    calc
      c ⊗ₜ[ℝ] x = (c.re • (1 : ℂ) + c.im • Complex.I) ⊗ₜ[ℝ] x := by
        congr 1
        apply Complex.ext <;> simp
      _ = _ := by simp only [TensorProduct.add_tmul,TensorProduct.smul_tmul,TensorProduct.tmul_smul]
  | add x y hx hy =>
    calc
      x+y = (1 ⊗ₜ[ℝ] rpart x + Complex.I ⊗ₜ[ℝ] ipart x) +
        (1 ⊗ₜ[ℝ] rpart y + Complex.I ⊗ₜ[ℝ] ipart y) := congrArg₂ (·+·) hx hy
      _ = _ := by simp only [map_add,TensorProduct.tmul_add]; abel
private theorem part_smul (c : ℂ) (z : ℂ ⊗[ℝ] M) :
    rpart (c • z) = c.re • rpart z - c.im • ipart z ∧
    ipart (c • z) = c.im • rpart z + c.re • ipart z := by
  induction z using TensorProduct.inductionOn with
  | tmul d x =>
    constructor <;>
      simp [TensorProduct.smul_tmul',Complex.mul_re,Complex.mul_im,sub_smul,add_smul,smul_smul] <;> module
  | add x y hx hy =>
    constructor
    · simp only [smul_add,map_add]
      rw [hx.1,hy.1]
      module
    · simp only [smul_add,map_add]
      rw [hx.2,hy.2]
      module


variable {S : Type*} [LieRing S] [LieAlgebra ℝ S]
  [LieRingModule S M] [LieModule ℝ S M]
private theorem part_bracket (a : S) (z : ℂ ⊗[ℝ] M) :
    rpart ⁅(1 : ℂ) ⊗ₜ[ℝ] a,z⁆ = ⁅a,rpart z⁆ ∧
    ipart ⁅(1 : ℂ) ⊗ₜ[ℝ] a,z⁆ = ⁅a,ipart z⁆ := by
  induction z using TensorProduct.inductionOn with
  | tmul c x => simp [LieAlgebra.ExtendScalars.bracket_tmul,lie_smul]
  | add x y hx hy =>
    have hadd : ⁅(1 : ℂ) ⊗ₜ[ℝ] a,x+y⁆ =
        ⁅(1 : ℂ) ⊗ₜ[ℝ] a,x⁆ + ⁅(1 : ℂ) ⊗ₜ[ℝ] a,y⁆ :=
      (LieModule.toEnd ℂ (ℂ ⊗[ℝ] S) (ℂ ⊗[ℝ] M) (1 ⊗ₜ a)).map_add x y
    simp only [hadd,map_add,lie_add]
    exact ⟨by rw [hx.1,hy.1],by rw [hx.2,hy.2]⟩

private theorem exists_small_weight {T V : Type*} [LieRing T] [LieAlgebra ℂ T]
    [AddCommGroup V] [Module ℂ V] [LieRingModule T V] [LieModule ℂ T V]
    [FiniteDimensional ℂ V] [Nontrivial V] {h e f : T} (t : IsSl2Triple h e f) :
    ∃ w : V, w ≠ 0 ∧ (⁅h,w⁆ = 0 ∨ ⁅h,w⁆ = w) := by
  obtain ⟨r,z,hz,P⟩ := t.exists_hasPrimitiveVectorWith (R := ℂ) (M := V)
  obtain ⟨n,hn⟩ := P.exists_nat
  let j := n/2
  let w := (LieModule.toEnd ℂ T V f ^ j) z
  have hw : w ≠ 0 := P.pow_toEnd_f_ne_zero_of_eq_nat hn (Nat.div_le_self n 2)
  have heig := P.lie_h_pow_toEnd_f j
  have hnmod : n = 2*j ∨ n = 2*j+1 := by dsimp [j]; omega
  refine ⟨w,hw,?_⟩
  rcases hnmod with h0 | h1
  · left
    have hc : r - 2*(j : ℂ) = 0 := by rw [hn,h0]; push_cast; ring
    simpa [w,hc] using heig
  · right
    have hc : r - 2*(j : ℂ) = 1 := by rw [hn,h1]; push_cast; ring
    simpa [w,hc] using heig

private theorem rotation_sl2 {T : Type*} [LieRing T] [LieAlgebra ℂ T]
    (a u v : T) (han : a ≠ 0) (hau : ⁅a,u⁆ = v)
    (hav : ⁅a,v⁆ = -u) (huv : ⁅u,v⁆ = a) :
    IsSl2Triple ((2*Complex.I) • a) (u+Complex.I • v) (-u+Complex.I • v) := by
  have hvu : ⁅v,u⁆ = -a := by rw [← lie_skew,huv]
  constructor
  · exact smul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) han
  · simp only [add_lie,lie_add,smul_lie,lie_smul,neg_lie,lie_neg,lie_self,
      huv,hvu,smul_neg,neg_neg,smul_zero,zero_smul,zero_add,add_zero,smul_smul]
    match_scalars <;> ring_nf <;> simp [Complex.I_sq]
  · simp only [smul_lie,lie_add,lie_smul,hau,hav,smul_add,smul_smul,smul_neg,two_smul]
    match_scalars <;> ring_nf <;> simp [Complex.I_sq]
  · simp only [smul_lie,lie_add,lie_smul,lie_neg,hau,hav,smul_add,smul_smul,smul_neg,two_smul]
    match_scalars <;> ring_nf <;> simp [Complex.I_sq]

variable {K : Type u} [LieRing K] [LieAlgebra ℝ K] [FiniteDimensional ℝ K]
attribute [local instance] LieRing.ofAssociativeRing
/-- No orthogonal complement survives a least-frequency rotation subalgebra. -/
private theorem minimum_frequency_span_eq_top
    (B : InnerProductSpace.Core ℝ K)
    (hinv : ∀ x y z : K, B.inner ⁅x,y⁆ z = -B.inner y ⁅x,z⁆)
    (a u v : K) (ha : a ≠ 0)
    (hcent : ∀ z : K, ⁅a,z⁆ = 0 → ∃ c : ℝ, z = c • a)
    (μ : ℝ) (hμ : 0 < μ)
    (hau : ⁅a,u⁆ = μ • v) (hav : ⁅a,v⁆ = -μ • u) (huv : ⁅u,v⁆ = μ • a)
    (hmin : ∀ (ρ : ℝ) (x : K), 0 < ρ → x ≠ 0 →
      ⁅a,⁅a,x⁆⁆ = -(ρ^2) • x → μ ≤ ρ) :
    Submodule.span ℝ {a,u,v} = ⊤ := by
  classical
  let : NormedAddCommGroup K := B.toNormedAddCommGroup
  let : InnerProductSpace ℝ K := InnerProductSpace.ofCore B.toCore
  let P : Submodule ℝ K := Submodule.span ℝ {a,u,v}
  have haP : a ∈ P := Submodule.subset_span (by simp)
  have huP : u ∈ P := Submodule.subset_span (by simp)
  have hvP : v ∈ P := Submodule.subset_span (by simp)
  have hgen (x : K) (hx : x ∈ ({a,u,v} : Set K))
      (y : K) (hy : y ∈ ({a,u,v} : Set K)) : ⁅x,y⁆ ∈ P := by
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    all_goals first
      | simpa only [lie_self] using P.zero_mem
      | simpa only [hau] using P.smul_mem μ hvP
      | simpa only [hav] using P.smul_mem (-μ) huP
      | simpa only [huv] using P.smul_mem μ haP
      | rw [← lie_skew]; exact P.neg_mem (by
          first | simpa only [hau] using P.smul_mem μ hvP
                | simpa only [hav] using P.smul_mem (-μ) huP
                | simpa only [huv] using P.smul_mem μ haP)
  have hclosed {x y : K} (hx : x ∈ P) (hy : y ∈ P) : ⁅x,y⁆ ∈ P := by
    induction hx using Submodule.span_induction generalizing y with
    | mem x hx =>
      induction hy using Submodule.span_induction with
      | mem y hy => exact hgen x hx y hy
      | zero => simpa using P.zero_mem
      | add y z _ _ hy hz => simpa [lie_add] using P.add_mem hy hz
      | smul c y _ hy => simpa [lie_smul] using P.smul_mem c hy
    | zero => simpa using P.zero_mem
    | add x z _ _ hx hz => simpa [add_lie] using P.add_mem (hx hy) (hz hy)
    | smul c x _ hx => simpa [smul_lie] using P.smul_mem c (hx hy)
  let S : LieSubalgebra ℝ K := { P with lie_mem' := hclosed }
  let M : LieSubmodule ℝ S K :=
    { Pᗮ with
      lie_mem := by
        intro s m hm
        apply (P.mem_orthogonal' _).mpr
        intro t ht
        change ⟪⁅(s : K),m⁆,t⟫_ℝ = 0
        rw [hinv]
        have hs : (s : K) ∈ P := s.property
        rw [(P.mem_orthogonal' m).mp hm ⁅(s : K),t⁆ (hclosed hs ht),neg_zero] }
  have hMzero : Subsingleton M := by
    by_contra htriv
    let : Nontrivial M := not_subsingleton_iff_nontrivial.mp htriv
    let aS : S := ⟨a,haP⟩
    let uS : S := ⟨u,huP⟩
    let vS : S := ⟨v,hvP⟩
    have haSn : aS ≠ 0 := fun hz => ha (congrArg Subtype.val hz)
    have hAU : ⁅aS,uS⁆ = μ • vS := Subtype.ext hau
    have hAV : ⁅aS,vS⁆ = -μ • uS := Subtype.ext hav
    have hUV : ⁅uS,vS⁆ = μ • aS := Subtype.ext huv
    have hμc : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ.ne'
    let ac : ℂ ⊗[ℝ] S := (μ : ℂ)⁻¹ • ((1 : ℂ) ⊗ₜ aS)
    let uc : ℂ ⊗[ℝ] S := (μ : ℂ)⁻¹ • ((1 : ℂ) ⊗ₜ uS)
    let vc : ℂ ⊗[ℝ] S := (μ : ℂ)⁻¹ • ((1 : ℂ) ⊗ₜ vS)
    have hbase (x y z : S) (h : ⁅x,y⁆ = μ • z) :
        ⁅(μ : ℂ)⁻¹ • ((1 : ℂ) ⊗ₜ[ℝ] x),(μ : ℂ)⁻¹ • ((1 : ℂ) ⊗ₜ[ℝ] y)⁆ =
          (μ : ℂ)⁻¹ • ((1 : ℂ) ⊗ₜ[ℝ] z) := by
      simp only [TensorProduct.smul_tmul',smul_eq_mul,mul_one,
        LieAlgebra.ExtendScalars.bracket_tmul,h]
      rw [TensorProduct.tmul_smul,TensorProduct.smul_tmul']
      apply congrArg (fun c : ℂ => c ⊗ₜ[ℝ] z)
      change (μ : ℂ)*((μ : ℂ)⁻¹*(μ : ℂ)⁻¹) = (μ : ℂ)⁻¹
      field_simp
    have hacuc : ⁅ac,uc⁆ = vc := hbase aS uS vS hAU
    have hacvc : ⁅ac,vc⁆ = -uc := by
      have hh : ⁅aS,vS⁆ = μ • (-uS) := by simpa using hAV
      simpa only [ac,vc,uc,TensorProduct.tmul_neg,smul_neg] using hbase aS vS (-uS) hh
    have hucvc : ⁅uc,vc⁆ = ac := hbase uS vS aS hUV
    have hacn : ac ≠ 0 := by
      apply smul_ne_zero (inv_ne_zero hμc)
      intro hz
      apply haSn
      have hh := congrArg (rpart (M := S)) hz
      simpa using hh
    let H : ℂ ⊗[ℝ] S := (2*Complex.I) • ac
    let E : ℂ ⊗[ℝ] S := uc + Complex.I • vc
    let F : ℂ ⊗[ℝ] S := -uc + Complex.I • vc
    have t : IsSl2Triple H E F := rotation_sl2 ac uc vc hacn hacuc hacvc hucvc
    have hCpos : 0 < finrank ℂ (ℂ ⊗[ℝ] M) := by
      rw [Module.finrank_baseChange]
      exact finrank_pos
    let : Nontrivial (ℂ ⊗[ℝ] M) := Module.nontrivial_of_finrank_pos hCpos
    obtain ⟨w,hwn,hw⟩ := exists_small_weight (V := ℂ ⊗[ℝ] M) t
    have hzero (m : M) (hm : ⁅aS,m⁆ = 0) : m = 0 := by
      have hh : ⁅a,(m : K)⁆ = 0 := congrArg Subtype.val hm
      obtain ⟨c,hc⟩ := hcent m hh
      have hp := (P.mem_orthogonal' (m : K)).mp m.property a haP
      rw [hc,real_inner_smul_left] at hp
      have hnn : ⟪a,a⟫_ℝ ≠ 0 := fun hh => ha (B.definite a hh)
      have hc0 : c = 0 := (mul_eq_zero.mp hp).resolve_right hnn
      apply Subtype.ext
      simpa [hc0] using hc
    have hHaction : ⁅H,w⁆ = ((2*Complex.I)/(μ : ℂ)) • ⁅(1 : ℂ) ⊗ₜ[ℝ] aS,w⁆ := by
      simp [H,ac,smul_lie,smul_smul,div_eq_mul_inv]
    have hscalar : (2*Complex.I)/(μ : ℂ) ≠ 0 :=
      div_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) hμc
    have hr := (part_bracket aS w).1
    have hi := (part_bracket aS w).2
    rcases hw with hw | hw
    · rw [hHaction] at hw
      have hz : ⁅(1 : ℂ) ⊗ₜ[ℝ] aS,w⁆ = 0 :=
        (smul_eq_zero.mp hw).resolve_left hscalar
      have hrz : rpart w = 0 := hzero _ (by rw [← hr,hz]; simp)
      have hiz : ipart w = 0 := hzero _ (by rw [← hi,hz]; simp)
      exact hwn (by rw [decompose w,hrz,hiz]; simp)
    · rw [hHaction] at hw
      have hc : ((2*Complex.I)/(μ : ℂ))⁻¹ = -(μ : ℂ)*Complex.I/2 := by
        field_simp
        simp [Complex.I_sq]
      have had : ⁅(1 : ℂ) ⊗ₜ[ℝ] aS,w⁆ = (-(μ : ℂ)*Complex.I/2) • w := by
        have hh := congrArg (fun z => ((2*Complex.I)/(μ : ℂ))⁻¹ • z) hw
        rw [smul_smul,inv_mul_cancel₀ hscalar,one_smul,hc] at hh
        exact hh
      have hparts := part_smul (-(μ : ℂ)*Complex.I/2) w
      have hreal : ⁅aS,rpart w⁆ = (μ/2) • ipart w := by
        rw [← hr,had,hparts.1]
        simp [neg_div,neg_smul]
      have himag : ⁅aS,ipart w⁆ = -(μ/2) • rpart w := by
        rw [← hi,had,hparts.2]
        simp [neg_div,neg_smul]
      have hrr : ⁅a,⁅a,((rpart w : M) : K)⁆⁆ = -((μ/2)^2) • ((rpart w : M) : K) := by
        have hh : ⁅aS,⁅aS,rpart w⁆⁆ = -((μ/2)^2) • rpart w := by
          rw [hreal,lie_smul,himag,smul_smul]
          congr 1
          ring
        exact congrArg Subtype.val hh
      have hii : ⁅a,⁅a,((ipart w : M) : K)⁆⁆ = -((μ/2)^2) • ((ipart w : M) : K) := by
        have hh : ⁅aS,⁅aS,ipart w⁆⁆ = -((μ/2)^2) • ipart w := by
          rw [himag,lie_smul,hreal,smul_smul]
          congr 1
          ring
        exact congrArg Subtype.val hh
      have hm : μ ≤ μ/2 := by
        by_cases hz : rpart w = 0
        · have hin : ((ipart w : M) : K) ≠ 0 := by
            intro hi0
            have hiz : ipart w = 0 := Subtype.ext hi0
            exact hwn (by rw [decompose w,hz,hiz]; simp)
          exact hmin (μ/2) _ (by linarith) hin hii
        · have hrn : ((rpart w : M) : K) ≠ 0 := fun hh => hz (Subtype.ext hh)
          exact hmin (μ/2) _ (by linarith) hrn hrr
      linarith
  have hperp : Pᗮ = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro x hx
    change x = 0
    have hz : (⟨x,hx⟩ : M) = 0 := Subsingleton.elim _ _
    exact congrArg Subtype.val hz
  have hPtop : P = ⊤ := Submodule.orthogonal_eq_bot_iff.mp hperp
  exact hPtop

/-- A positive invariant metric and a one-dimensional centralizer force dimension one or three. -/
theorem finrank_eq_one_or_three (B : InnerProductSpace.Core ℝ K)
    (hinv : ∀ x y z : K, B.inner ⁅x,y⁆ z = -B.inner y ⁅x,z⁆)
    (a : K) (ha : a ≠ 0)
    (hcent : ∀ z : K, ⁅a,z⁆ = 0 → ∃ c : ℝ, z = c • a) :
    finrank ℝ K = 1 ∨ finrank ℝ K = 3 := by
  classical
  let : NormedAddCommGroup K := B.toNormedAddCommGroup
  let : InnerProductSpace ℝ K := InnerProductSpace.ofCore B.toCore
  let br : K →ₗ[ℝ] K →ₗ[ℝ] K := (LieAlgebra.ad ℝ K).toLinearMap
  by_cases hD : br a = 0
  · left
    have hspan : Submodule.span ℝ {a} = ⊤ := by
      apply top_unique
      intro x _
      obtain ⟨c,hc⟩ := hcent x (DFunLike.congr_fun hD x)
      exact Submodule.mem_span_singleton.mpr ⟨c,hc.symm⟩
    have hh := finrank_span_singleton ha (K := ℝ)
    rw [hspan,finrank_top] at hh
    exact hh
  right
  let a' := (‖a‖⁻¹ : ℝ) • a
  have han : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  have haunit : ‖a'‖ = 1 := by
    simp [a',norm_smul,Real.norm_eq_abs,abs_of_pos (norm_pos_iff.mpr ha),han]
  have hcent' : ∀ z : K, ⁅a',z⁆ = 0 → ∃ c : ℝ, z = c • a' := by
    intro z hz
    have hz' : ⁅a,z⁆ = 0 := by
      simpa only [a',smul_lie,smul_eq_zero,inv_eq_zero,han,false_or] using hz
    obtain ⟨c,hc⟩ := hcent z hz'
    refine ⟨c*‖a‖,?_⟩
    change z = (c*‖a‖) • ((‖a‖⁻¹ : ℝ) • a)
    rw [hc,smul_smul]
    congr 1
    field_simp
  have hD' : br a' ≠ 0 := by
    intro hz
    apply hD
    ext x
    have hh := DFunLike.congr_fun hz x
    change ⁅a',x⁆ = 0 at hh
    change ⁅a,x⁆ = 0
    simpa only [a',smul_lie,smul_eq_zero,inv_eq_zero,han,false_or] using hh
  obtain ⟨μ,u,v,hμ,hu,hv,hau0,hav0,huv0,hau,hav,huv,hmin⟩ :=
    min_frame br (fun z => lie_self z) (fun x y z => leibniz_lie x y z)
      a' haunit hinv hcent' hD'
  change ⁅a',u⁆ = μ • v at hau
  change ⁅a',v⁆ = -μ • u at hav
  change ⁅u,v⁆ = μ • a' at huv
  change ∀ (ρ : ℝ) (x : K), 0 < ρ → x ≠ 0 → ⁅a',⁅a',x⁆⁆ = -(ρ^2) • x → μ ≤ ρ at hmin
  let P : Submodule ℝ K := Submodule.span ℝ {a',u,v}
  have ha'n : a' ≠ 0 := by
    intro hz
    have hh := congrArg norm hz
    simpa [haunit] using hh
  have hPtop : P = ⊤ := minimum_frequency_span_eq_top B hinv a' u v ha'n
    hcent' μ hμ hau hav huv hmin
  have hua0 : ⟪u,a'⟫_ℝ = 0 := by rw [real_inner_comm]; exact hau0
  have hva0 : ⟪v,a'⟫_ℝ = 0 := by rw [real_inner_comm]; exact hav0
  have hvu0 : ⟪v,u⟫_ℝ = 0 := by rw [real_inner_comm]; exact huv0
  have horth : Orthonormal ℝ ![a',u,v] := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [haunit,hu,hv,hau0,hav0,huv0,hua0,hva0,hvu0,real_inner_self_eq_norm_sq]
  have hh := finrank_span_eq_card horth.linearIndependent
  have hrange : Set.range ![a',u,v] = ({a',u,v} : Set K) := by
    ext x
    simp [Matrix.range_cons,Matrix.range_empty]
    tauto
  rw [hrange,show Submodule.span ℝ {a',u,v} = P from rfl,hPtop,finrank_top] at hh
  simpa using hh


end

end D5.S3.Quantum.Algebra.RankOneInvariantMetric

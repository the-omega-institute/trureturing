/- GID: D5/S3/VertexAlgebra/Sectors/VBKMPrimitiveKernel
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/VBKMPrimitiveKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Virasoro and Borcherds presentation, action, and ideal structure. -/

/-
admission_basis: escape-witness
escape_witness: D5.S3.VertexAlgebra.Sectors.VBKMPrimitiveKernel.normalized_not_proper
Direct frozen dependencies: none; all D5 prerequisites are in this delivery.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/30339
Definitions are labelled bind-only as encodings, not as proofs of new propositions.
Declarations (consumer names are qualified by their owning module):
raising_kernel_on_span: proof_shape: content; frozen: none; escape_witness: VBKMPrimitiveKernel.raising_kernel_on_span; consumers: VBKMPrimitiveKernel.primitive_kernel.
primitive_kernel: proof_shape: content; frozen: none; escape_witness: VBKMPrimitiveKernel.raising_kernel_on_span; consumers: VBKMPrimitiveKernel.primitive_kernel_generated.
primitive_kernel_generated: proof_shape: content; frozen: none; escape_witness: VBKMPrimitiveKernel.raising_kernel_on_span; consumers: VBKMPrimitiveKernel.primitive_not_proper.
primitive_not_proper: proof_shape: content; frozen: none; escape_witness: VBKMPrimitiveKernel.raising_kernel_on_span; consumers: VBKMPrimitiveKernel.normalized_not_proper.
normalized_not_proper: proof_shape: content; frozen: none; escape_witness: VBKMPrimitiveKernel.raising_kernel_on_span; consumers: ZverykIdealRigidityRefutation.datum_no_rank_highest.
-/


import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Lie.Sl2

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable
attribute [local instance] LieRing.ofAssociativeRing
universe u v
namespace D5.S3.VertexAlgebra.Sectors.VBKMPrimitiveKernel

set_option maxHeartbeats 2000000

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

private theorem raising_kernel_on_span (E : Module.End ℂ M) (v : ℕ → M) (c : ℕ → ℂ)
    (hv : LinearIndependent ℂ v) (h0 : E (v 0) = 0)
    (hE : ∀ n : ℕ, E (v (n+1)) = c n • v n)
    (hc : ∀ n : ℕ, c n ≠ 0) (x : M)
    (hx : x ∈ Submodule.span ℂ (Set.range v)) (hEx : E x = 0) :
    ∃ a : ℂ, x = a • v 0 := by
  classical
  obtain ⟨f,hf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hx
  let N := f.support.sup id
  have hsupport : f.support ⊆ Finset.range (N+1) := by
    exact Finset.subset_range_sup_succ f.support
  have hxsum : x = ∑ n ∈ Finset.range (N+1), f n • v n := by
    rw [← hf]
    dsimp [Finsupp.sum]
    apply Finset.sum_subset hsupport
    intro n hn hns
    simp [Finsupp.notMem_support_iff.mp hns]
  have hcalc (k : ℕ) : E (∑ n ∈ Finset.range (k+1), f n • v n) =
      ∑ n ∈ Finset.range k, (f (n+1) * c n) • v n := by
    induction k with
    | zero => simp [h0]
    | succ k ih =>
      rw [Finset.sum_range_succ, map_add, map_smul, hE, ih]
      simp only [Finset.sum_range_succ, smul_smul]
  have hz : (∑ n ∈ Finset.range N, (f (n+1) * c n) • v n) = 0 := by
    rw [← hcalc, ← hxsum]
    exact hEx
  have hcoeff (n : ℕ) (hn : n < N) : f (n+1) = 0 := by
    have hh := linearIndependent_iff'.mp hv (Finset.range N)
      (fun n => f (n+1) * c n) hz n (Finset.mem_range.mpr hn)
    exact (mul_eq_zero.mp hh).resolve_right (hc n)
  refine ⟨f 0, ?_⟩
  rw [hxsum]
  apply Finset.sum_eq_single 0
  · intro n hn hn0
    obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    have hm : m < N := by have := Finset.mem_range.mp hn; omega
    simp [hcoeff m hm]
  · simp

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]
  [LieRingModule L M] [LieModule ℂ L M]

private theorem primitive_kernel (h e f : L) (t : IsSl2Triple h e f) (w : M) (μ : ℂ)
    (P : t.HasPrimitiveVectorWith w μ) (hμ : ∀ n : ℕ, μ ≠ (n : ℂ))
    (x : M) (hx : x ∈ Submodule.span ℂ (Set.range
      (fun n : ℕ => (LieModule.toEnd ℂ L M f ^ n) w)))
    (hEx : ⁅e,x⁆ = 0) : ∃ a : ℂ, x = a • w := by
  classical
  let v (n : ℕ) : M := (LieModule.toEnd ℂ L M f ^ n) w
  let c (n : ℕ) : ℂ := (n+1) * (μ-n)
  have hc (n : ℕ) : c n ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (Nat.cast_add_one_ne_zero n) (sub_ne_zero.mpr (hμ n))
  have hE (n : ℕ) : (LieModule.toEnd ℂ L M e) (v (n+1)) = c n • v n := by
    exact P.lie_e_pow_succ_toEnd_f n
  have hvne (n : ℕ) : v n ≠ 0 := by
    induction n with
    | zero => simpa [v] using P.ne_zero
    | succ n ih =>
      intro hz
      have hh := hE n
      rw [hz,map_zero] at hh
      exact (smul_ne_zero (hc n) ih) hh.symm
  have hμinj : Function.Injective (fun n : ℕ => μ-2*n) := by
    intro n m hnm
    have hnm' : (n : ℂ) = m := by linear_combination (-1/2 : ℂ) * hnm
    exact Nat.cast_injective hnm'
  have hv : LinearIndependent ℂ v :=
    (LieModule.toEnd ℂ L M h).eigenvectors_linearIndependent'
      (fun n : ℕ => μ-2*n) hμinj v (fun n =>
        ⟨Module.End.mem_eigenspace_iff.mpr (P.lie_h_pow_toEnd_f n), hvne n⟩)
  obtain ⟨a,ha⟩ := raising_kernel_on_span (LieModule.toEnd ℂ L M e) v c hv
    (by simpa [v] using P.lie_e) hE hc x hx hEx
  exact ⟨a, by simpa [v] using ha⟩


private theorem primitive_kernel_generated (h e f : L) (t : IsSl2Triple h e f) (w : M) (μ : ℂ)
    (P : t.HasPrimitiveVectorWith w μ) (hμ : ∀ n : ℕ, μ ≠ (n : ℂ))
    (S : Set L) (hS : S ⊆ t.toLieSubalgebra ℂ)
    (x : M) (hx : x ∈ LieSubmodule.lieSpan ℂ (LieSubalgebra.lieSpan ℂ L S) ({w} : Set M))
    (hEx : ⁅e,x⁆ = 0) : ∃ a : ℂ, x = a • w := by
  let v (n : ℕ) : M := (LieModule.toEnd ℂ L M f ^ n) w
  let V : Submodule ℂ M := Submodule.span ℂ (Set.range v)
  have hv (n : ℕ) : v n ∈ V := Submodule.subset_span ⟨n,rfl⟩
  have hstable (y : L) (hy : y ∈ t.toLieSubalgebra ℂ) (z : M) (hz : z ∈ V) :
      ⁅y,z⁆ ∈ V := by
    obtain ⟨a,b,c,hy⟩ := t.mem_toLieSubalgebra_iff.mp hy
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨n,rfl⟩ := hz
      have he (n : ℕ) : ⁅e,v n⁆ ∈ V := by
        cases n with
        | zero => simpa [v,P.lie_e] using V.zero_mem
        | succ n =>
          rw [show ⁅e,v (n+1)⁆ = ((n+1) * (μ-n)) • v n from P.lie_e_pow_succ_toEnd_f n]
          exact V.smul_mem _ (hv n)
      have hf (n : ℕ) : ⁅f,v n⁆ ∈ V := by
        rw [show ⁅f,v n⁆ = v (n+1) from P.lie_f_pow_toEnd_f n]
        exact hv (n+1)
      have hh (n : ℕ) : ⁅h,v n⁆ ∈ V := by
        rw [show ⁅h,v n⁆ = (μ-2*n) • v n from P.lie_h_pow_toEnd_f n]
        exact V.smul_mem _ (hv n)
      rw [hy,t.lie_e_f]
      simp only [add_lie,smul_lie]
      exact V.add_mem (V.add_mem (V.smul_mem _ (he n)) (V.smul_mem _ (hf n)))
        (V.smul_mem _ (hh n))
    | zero => simp
    | add z z' hz hz' ih ih' => simpa only [lie_add] using V.add_mem ih ih'
    | smul a z hz ih => simpa only [lie_smul] using V.smul_mem a ih
  let V' : LieSubmodule ℂ (LieSubalgebra.lieSpan ℂ L S) M :=
    { toSubmodule := V
      lie_mem := fun {y z} hz => hstable y
        ((LieSubalgebra.lieSpan_le.mpr hS) y.property) z hz }
  have hle : LieSubmodule.lieSpan ℂ (LieSubalgebra.lieSpan ℂ L S) ({w} : Set M) ≤ V' := by
    apply LieSubmodule.lieSpan_le.mpr
    intro z hz
    rcases Set.mem_singleton_iff.mp hz with rfl
    change z ∈ V
    simpa [v] using hv 0
  exact primitive_kernel h e f t w μ P hμ x (hle hx) hEx

private theorem primitive_not_proper (h e f : L) (t : IsSl2Triple h e f) (w : M) (μ : ℂ)
    (P : t.HasPrimitiveVectorWith w μ) (hμ : ∀ n : ℕ, μ ≠ (n : ℂ))
    (S : Set L) (hS : S ⊆ t.toLieSubalgebra ℂ)
    (x : M) (hx : x ∈ LieSubmodule.lieSpan ℂ (LieSubalgebra.lieSpan ℂ L S) ({w} : Set M))
    (hEx : ⁅e,x⁆ = 0) (hxne : x ≠ 0) :
    ¬ (LieSubmodule.lieSpan ℂ (LieSubalgebra.lieSpan ℂ L S) ({x} : Set M)).toSubmodule <
      (LieSubmodule.lieSpan ℂ (LieSubalgebra.lieSpan ℂ L S) ({w} : Set M)).toSubmodule := by
  obtain ⟨a,ha⟩ := primitive_kernel_generated h e f t w μ P hμ S hS x hx hEx
  have ha0 : a ≠ 0 := by intro hz; exact hxne (by simp [ha,hz])
  have hw : w ∈ LieSubmodule.lieSpan ℂ (LieSubalgebra.lieSpan ℂ L S) ({x} : Set M) := by
    have hh := (LieSubmodule.lieSpan ℂ (LieSubalgebra.lieSpan ℂ L S) ({x} : Set M)).smul_mem
      a⁻¹ (LieSubmodule.subset_lieSpan (Set.mem_singleton x))
    simpa [ha,smul_smul,ha0] using hh
  intro hlt
  have hle : LieSubmodule.lieSpan ℂ (LieSubalgebra.lieSpan ℂ L S) ({w} : Set M) ≤
      LieSubmodule.lieSpan ℂ (LieSubalgebra.lieSpan ℂ L S) ({x} : Set M) := by
    apply LieSubmodule.lieSpan_le.mpr
    intro y hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    exact hw
  exact not_le_of_gt hlt hle

theorem normalized_not_proper (H E F : L) (a b : ℂ) (ha : a ≠ 0)
    (hEF : ⁅E,F⁆ = H) (hHE : ⁅H,E⁆ = a • E) (hHF : ⁅H,F⁆ = -a • F)
    (w x : M) (hHw : ⁅H,w⁆ = b • w) (hEw : ⁅E,w⁆ = 0)
    (hμ : ∀ n : ℕ, (2/a)*b ≠ (n : ℂ))
    (S : Set L) (hS0 : S ⊆ Submodule.span ℂ ({E,F,H} : Set L))
    (hx : x ∈ LieSubmodule.lieSpan ℂ (LieSubalgebra.lieSpan ℂ L S) ({w} : Set M))
    (hEx : ⁅E,x⁆ = 0) (hxne : x ≠ 0) :
    ¬ (LieSubmodule.lieSpan ℂ (LieSubalgebra.lieSpan ℂ L S) ({x} : Set M)).toSubmodule <
      (LieSubmodule.lieSpan ℂ (LieSubalgebra.lieSpan ℂ L S) ({w} : Set M)).toSubmodule := by
  have hwne : w ≠ 0 := by
    intro hw
    have hb : LieSubmodule.lieSpan ℂ (LieSubalgebra.lieSpan ℂ L S)
        ({w} : Set M) = ⊥ := by
      apply le_antisymm
      · apply LieSubmodule.lieSpan_le.mpr
        intro y hy
        have hyw : y = w := Set.mem_singleton_iff.mp hy
        simpa [hyw,hw]
      · exact bot_le
    rw [hb] at hx
    exact hxne hx
  have hnormH : (2/a) • H ≠ 0 := by
    intro hz
    have hh : ⁅(2/a) • H,w⁆ = ((2/a)*b) • w := by rw [smul_lie,hHw,smul_smul]
    rw [hz,zero_lie] at hh
    exact (smul_ne_zero (by simpa using hμ 0) hwne) hh.symm
  have he : ⁅(2/a) • H,(2/a) • E⁆ = 2 • ((2/a) • E) := by
    simp only [smul_lie,lie_smul,hHE,smul_smul,two_smul,← add_smul]
    congr 1
    field_simp
    <;> ring
  have hf : ⁅(2/a) • H,F⁆ = -(2 • F) := by
    simp only [smul_lie,hHF,smul_smul,two_smul,← add_smul,← neg_smul]
    congr 1
    field_simp
    <;> module
  have hef : ⁅(2/a) • E,F⁆ = (2/a) • H := by rw [smul_lie,hEF]
  let t : IsSl2Triple ((2/a) • H) ((2/a) • E) F := ⟨hnormH,hef,he,hf⟩
  have hS : ({E,F,H} : Set L) ⊆ t.toLieSubalgebra ℂ := by
    intro y hy
    rcases hy with rfl | rfl | rfl
    · apply t.mem_toLieSubalgebra_iff.mpr
      refine ⟨a/2,0,0,?_⟩
      simp only [zero_smul,add_zero,smul_smul]
      rw [show a/2*(2/a) = 1 by field_simp]
      simp
    · apply t.mem_toLieSubalgebra_iff.mpr
      exact ⟨0,1,0,by simp⟩
    · apply t.mem_toLieSubalgebra_iff.mpr
      refine ⟨0,0,a/2,?_⟩
      rw [hef]
      simp only [zero_smul,zero_add,smul_smul]
      rw [show a/2*(2/a) = 1 by field_simp]
      simp
  have hp : t.HasPrimitiveVectorWith w ((2/a)*b) :=
    ⟨hwne,by rw [smul_lie,hHw,smul_smul],by simp [smul_lie,hEw]⟩
  have hleS : Submodule.span ℂ ({E,F,H} : Set L) ≤ (t.toLieSubalgebra ℂ).toSubmodule :=
    Submodule.span_le.mpr hS
  have hS' : S ⊆ t.toLieSubalgebra ℂ := fun y hy => hleS (hS0 hy)
  exact primitive_not_proper _ _ _ t w _ hp hμ _ hS' x hx
    (by simp [smul_lie,hEx]) hxne




set_option maxHeartbeats 200000
end D5.S3.VertexAlgebra.Sectors.VBKMPrimitiveKernel

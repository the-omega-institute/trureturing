/- GID: D5/S3/Combinatorics/Graph/LegalWords/SignedBoundary
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LegalWords/SignedBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native boundaries have mass-zero image and a natural kernel short exact sequence. -/

import D5.S3.Combinatorics.Graph.LegalWords.EdgeCount
import D5.S3.Fourier.CharacterSelection.SignedIncidenceTotalUnimodularity
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.LegalWords.SignedBoundary

variable {α Y : Type*} {G : SimpleGraph α}

noncomputable section

instance edgeSetFintype [Fintype α] (G : SimpleGraph α) : Fintype (↥G.edgeSet) :=
  Fintype.ofFinite _

variable [AddCommGroup Y] [Module ℝ Y]

open scoped BigOperators
open D5.S1.Words.AdmissibleWords.AdmissibleCount
open D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant
open D5.S3.Combinatorics.Graph.LegalWordDegree
open D5.S3.Combinatorics.Graph.LegalWords.EdgeCount
open private erase erase_adj erase_occupation from
  D5.S3.Combinatorics.Graph.LegalWords.EdgeCount

abbrev Orientation (G : SimpleGraph α) :=
  ∀ e : ↥G.edgeSet, {p : α × α // s(p.1, p.2) = (e : Sym2 α)}

def edgeVector [DecidableEq α] (o : Orientation G) (e : ↥G.edgeSet) : α → ℝ :=
  fun v => (D5.S3.Fourier.CharacterSelection.SignedIncidenceTotalUnimodularity.signedIncidence
    (fun e => (o e).1.1) (fun e => (o e).1.2) v e : ℝ)

def signedBoundary [Fintype α] [DecidableEq α] (o : Orientation G) :
    (↥G.edgeSet → ℝ) →ₗ[ℝ] (α → ℝ) :=
  { toFun := fun f v => ∑ e, f e * edgeVector o e v
    map_add' := by
      intro f g
      funext v
      simp only [Pi.add_apply]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro e he
      ring
    map_smul' := by
      intro a f
      funext v
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      ring }

def totalMass [Fintype α] : (α → ℝ) →ₗ[ℝ] ℝ :=
  { toFun := fun f => ∑ v, f v
    map_add' := by intro f g; simp [Finset.sum_add_distrib]
    map_smul' := by
      intro a f
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      rw [Finset.mul_sum] }

def totalMassZero [Fintype α] : Submodule ℝ (α → ℝ) := LinearMap.ker totalMass

def vertexDelta [DecidableEq α] (v : α) : α → ℝ := Pi.single v 1

private theorem edgeVector_eq_delta [DecidableEq α]
    (o : Orientation G) (e : ↥G.edgeSet) :
    edgeVector o e = vertexDelta (o e).1.2 - vertexDelta (o e).1.1 := by
  funext v
  simp only [edgeVector,
    D5.S3.Fourier.CharacterSelection.SignedIncidenceTotalUnimodularity.signedIncidence,
    Int.cast_sub, Int.cast_ite, Int.cast_one, Int.cast_zero, vertexDelta,
    Pi.sub_apply, Pi.single_apply]

private theorem boundary_single [Fintype α] [DecidableEq α]
    (o : Orientation G) (e : ↥G.edgeSet) :
    signedBoundary o (Pi.single e 1) = edgeVector o e := by
  funext v
  simp [signedBoundary, Pi.single_apply]

private theorem boundary_mem_mass_zero [Fintype α] [DecidableEq α]
    (o : Orientation G) (f : ↥G.edgeSet → ℝ) :
    signedBoundary o f ∈ totalMassZero := by
  change totalMass (signedBoundary o f) = 0
  classical
  simp only [totalMass, signedBoundary, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro e he
  rw [← Finset.mul_sum]
  rw [show (∑ v, edgeVector o e v) = 0 by
    rw [edgeVector_eq_delta]
    simp [vertexDelta, Finset.sum_sub_distrib]]
  simp

private theorem adjacent_delta_mem_range [Fintype α] [DecidableEq α]
    (o : Orientation G) {u v : α} (h : G.Adj u v) :
    vertexDelta v - vertexDelta u ∈ LinearMap.range (signedBoundary o) := by
  classical
  let e : ↥G.edgeSet := ⟨s(u, v), G.mem_edgeSet.mpr h⟩
  have heq : s((o e).1.1, (o e).1.2) = s(u, v) := (o e).2.trans rfl
  rcases Sym2.eq_iff.mp heq with huv | huv
  · rcases huv with ⟨hu, hv⟩
    refine ⟨Pi.single e 1, ?_⟩
    rw [boundary_single, edgeVector_eq_delta, hu, hv]
  · rcases huv with ⟨hv, hu⟩
    refine ⟨-(Pi.single e 1), ?_⟩
    rw [map_neg, boundary_single, edgeVector_eq_delta, hu, hv]
    abel

private theorem walk_delta_mem_range [Fintype α] [DecidableEq α]
    (o : Orientation G) {u v : α} (p : G.Walk u v) :
    vertexDelta v - vertexDelta u ∈ LinearMap.range (signedBoundary o) := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
      have h₁ := adjacent_delta_mem_range o h
      have h₂ := ih
      rw [show vertexDelta w - vertexDelta u =
        (vertexDelta w - vertexDelta v) + (vertexDelta v - vertexDelta u) by abel]
      exact (LinearMap.range (signedBoundary o)).add_mem h₂ h₁

private theorem signedBoundary_range_eq_totalMassZero [Fintype α] [DecidableEq α]
    (hG : G.Connected) (o : Orientation G) :
    LinearMap.range (signedBoundary o) = totalMassZero := by
  apply le_antisymm
  · intro x hx
    rcases hx with ⟨f, rfl⟩
    exact boundary_mem_mass_zero o f
  · intro x hx
    classical
    change totalMass x = 0 at hx
    let r : α := Classical.choice (hG.nonempty)
    have hrepr : x = ∑ v, x v • (vertexDelta v - vertexDelta r) := by
      simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul]
      have hzero : (∑ v, x v) = 0 := hx
      rw [hzero, zero_smul, sub_zero]
      rw [← Finset.univ_sum_single x]
      apply Finset.sum_congr rfl
      intro v _
      funext w
      by_cases hw : w = v <;> simp [vertexDelta, Pi.single_apply, hw]
    rw [hrepr]
    apply Submodule.sum_mem
    intro v hv
    have hrv : G.Reachable r v := hG.preconnected r v
    rcases hrv with ⟨p⟩
    have hp := walk_delta_mem_range o p
    exact (LinearMap.range (signedBoundary o)).smul_mem _ hp

def observation (n : ℕ) [Fintype (Legal n)] :
    (Legal n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  { toFun := fun f i => ∑ b, if b.val i then f b else 0
    map_add' := by
      intro f g
      funext i
      change (∑ b, if b.val i then f b + g b else 0) =
        (∑ b, if b.val i then f b else 0) + ∑ b, if b.val i then g b else 0
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b hb
      by_cases h : b.val i <;> simp [h]
    map_smul' := by
      intro a f
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      by_cases h : b.val i <;> simp [h] }

def kernelBoundaryInclusion [Fintype α] [DecidableEq α]
    (A : (α → ℝ) →ₗ[ℝ] Y) (o : Orientation G) :
    (LinearMap.ker (signedBoundary o)) →ₗ[ℝ]
      (LinearMap.ker (A.comp (signedBoundary o))) :=
  { toFun := fun f => ⟨f.1, by
      change A (signedBoundary o f.1) = 0
      rw [show signedBoundary o f.1 = 0 from f.2, map_zero]⟩
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

def restrictedBoundary [Fintype α] [DecidableEq α]
    (A : (α → ℝ) →ₗ[ℝ] Y) (o : Orientation G) :
    (LinearMap.ker (A.comp (signedBoundary o))) →ₗ[ℝ]
      (LinearMap.ker (A.domRestrict (totalMassZero : Submodule ℝ (α → ℝ)))) :=
  { toFun := fun f =>
      ⟨⟨signedBoundary o f.1, boundary_mem_mass_zero o f.1⟩, f.2⟩
    map_add' := by
      intro f g
      apply Subtype.ext
      apply Subtype.ext
      exact map_add (signedBoundary o) f.val g.val
    map_smul' := by
      intro a f
      apply Subtype.ext
      apply Subtype.ext
      exact map_smul (signedBoundary o) a f.val }

private theorem natural_short_exact [Fintype α] [DecidableEq α]
    (hG : G.Connected) (A : (α → ℝ) →ₗ[ℝ] Y) (o : Orientation G) :
    Function.Injective (kernelBoundaryInclusion A o) ∧
      Function.Exact (kernelBoundaryInclusion A o) (restrictedBoundary A o) ∧
      Function.Surjective (restrictedBoundary A o) := by
  have hB : LinearMap.range (signedBoundary o) = totalMassZero :=
    signedBoundary_range_eq_totalMassZero hG o
  have hinj : Function.Injective (kernelBoundaryInclusion A o) := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : LinearMap.ker (A.comp (signedBoundary o)) => z.val) hxy
  have hex : Function.Exact (kernelBoundaryInclusion A o) (restrictedBoundary A o) := by
    rw [LinearMap.exact_iff]
    apply le_antisymm
    · intro z hz
      refine ⟨⟨z.1, ?_⟩, ?_⟩
      · exact congrArg (fun t => t.val.val) hz
      · rfl
    · rintro z ⟨x, rfl⟩
      apply Subtype.ext
      apply Subtype.ext
      exact x.2
  have hsurj : Function.Surjective (restrictedBoundary A o) := by
    intro z
    have hz : z.val.val ∈ LinearMap.range (signedBoundary o) := by
      rw [hB]
      exact z.val.property
    rcases hz with ⟨f, hf⟩
    let x : LinearMap.ker (A.comp (signedBoundary o)) :=
      ⟨f, by
        change A (signedBoundary o f) = 0
        rw [hf]
        exact z.property⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hf
  exact ⟨hinj, hex, hsurj⟩

private def emptyWord (n : ℕ) : Legal n :=
  ⟨fun _ => false, by simp [adm_iff_no_adjacent_true]⟩

private theorem reaches_empty (n : ℕ) (b : Legal n) :
    (legalWordGraph n).Reachable b (emptyWord n) := by
  classical
  have h : ∀ k : ℕ, ∀ b : Legal n, occupationCount b.val = k →
      (legalWordGraph n).Reachable b (emptyWord n) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro b hk
      by_cases hb : b = emptyWord n
      · subst b
        exact SimpleGraph.Reachable.refl _
      · have hp : ∃ i : Fin n, b.val i = true := by
          by_contra hn
          apply hb
          apply Subtype.ext
          funext i
          have hi : b.val i ≠ true := fun ht => hn ⟨i, ht⟩
          cases hv : b.val i <;> simp_all [emptyWord]
        obtain ⟨i, hi⟩ := hp
        have hd := erase_occupation b i hi
        have hlt : occupationCount (erase b i).val < k := by omega
        exact (erase_adj b i hi).reachable.trans (ih _ hlt _ rfl)
  exact h _ b rfl

private theorem native_connected (n : ℕ) : (legalWordGraph n).Connected := by
  let : Nonempty (Legal n) := ⟨emptyWord n⟩
  exact ⟨fun b c => (reaches_empty n b).trans (reaches_empty n c).symm⟩

/-- The native signed boundary has exactly the mass-zero image and induces the natural
short exact sequence for singleton occupation, at every length and reference orientation. -/
theorem native_boundary_image_short_exact (n : ℕ) (o : Orientation (legalWordGraph n)) :
    LinearMap.range (signedBoundary o) = (totalMassZero : Submodule ℝ (Legal n → ℝ)) ∧
    Function.Injective (kernelBoundaryInclusion (observation n) o) ∧
    Function.Exact (kernelBoundaryInclusion (observation n) o)
      (restrictedBoundary (observation n) o) ∧
    Function.Surjective (restrictedBoundary (observation n) o) := by
  classical
  exact ⟨signedBoundary_range_eq_totalMassZero (native_connected n) o,
    natural_short_exact (native_connected n) (observation n) o⟩

#print axioms native_boundary_image_short_exact
#check native_boundary_image_short_exact

end

end D5.S3.Combinatorics.Graph.LegalWords.SignedBoundary

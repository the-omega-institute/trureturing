/- GID: D5/S3/Topology/WeavingReferenceIncidence
   generality: G
   mirror-B: D5/B/S3/Topology/WeavingReferenceIncidence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Logic.Relation]
   utility: none
   digest: Crossing incidences as unordered endpoint pairs of actual uniform circles. -/

import D5.S3.Topology.WeavingMixedComponents
import Mathlib.Data.Sym.Sym2

/-! Crossing incidences as unordered endpoint pairs of actual uniform circles. -/

set_option autoImplicit false
noncomputable section

namespace D5.S3.Topology.WeavingReferenceIncidence

open D5.S3.Topology.WeavingDiagramPorts
open D5.S3.Topology.WeavingMixedComponents

def vertexCode (P : Parameters) (p : ℕ) (hp : p < 2) : Circle P p → ℕ × ZMod P.m :=
  Quotient.lift (code P p) (fun x y h => (reach_iff_code P p hp x y).mp h)

def endpointCodes (P : Parameters) (p : ℕ) (hp : p < 2) (a : Crossing P) :=
  (vertexCode P p hp (edgeEnds P p a.1 a.2).1,
   vertexCode P p hp (edgeEnds P p a.1 a.2).2)

theorem endpointCodes_cup (P : Parameters) (p : ℕ) (hp : p < 2)
    (t : ZMod P.m) (i : Fin P.n) (h : cup p i) :
    endpointCodes P p hp (t,i) = ((i.val+1,t-1),(i.val+1,t)) := by
  simp [endpointCodes,edgeEnds,vertexCode,circle,code,h]

/-- Even at a boundary, the two COLUMN codes of a vertical edge are i and i+2.
Only its hub time is replaced by zero. -/
theorem endpointCodes_vertical (P : Parameters) (p : ℕ) (hp : p < 2)
    (t : ZMod P.m) (i : Fin P.n) (h : ¬ cup p i) :
    endpointCodes P p hp (t,i) =
      ((i.val,if i.val = 0 then 0 else t),
       (i.val+2,if i.val+1 < P.n then t-1 else 0)) := by
  have hi := i.isLt
  have hn := P.hn
  have hn1 : 1 < P.n := by omega
  by_cases hl : i.val = 0 <;> by_cases hr : i.val+1 < P.n
  · simp [endpointCodes,edgeEnds,vertexCode,circle,code,h,hl,hr,hn1]
  · omega
  · simp [endpointCodes,edgeEnds,vertexCode,circle,code,h,hl,hr,hn1]
  · have he : i.val+2 = P.n+1 := by omega
    simp [endpointCodes,edgeEnds,vertexCode,circle,code,h,hl,hr,he]

private theorem two_ne_zero (P : Parameters) : (2 : ZMod P.m) ≠ 0 := by
  intro h
  have hd : P.m ∣ 2 := (ZMod.natCast_eq_zero_iff 2 P.m).mp h
  have := Nat.le_of_dvd (by decide : 0 < 2) hd
  have := P.hm
  omega

/-- The four edge types are distinguished by column codes. Row reversal would
force 2=0 in ZMod m; this is exactly where m≥3 is needed. -/
theorem unordered_crossing_endpoints_injective (P : Parameters) (p : ℕ) (hp : p < 2)
    (a b : Crossing P)
    (h : endpointCodes P p hp a = endpointCodes P p hp b ∨
      endpointCodes P p hp a = (endpointCodes P p hp b).swap) : a = b := by
  rcases a with ⟨t,i⟩
  rcases b with ⟨u,j⟩
  by_cases hi : cup p i
  · by_cases hj : cup p j
    · rw [endpointCodes_cup P p hp t i hi,endpointCodes_cup P p hp u j hj] at h
      rcases h with h | h
      · have hij : i = j := Fin.ext (by
          have := congrArg (fun q => q.1.1) h
          simpa using this)
        have htu : t = u := congrArg (fun q => q.2.2) h
        exact Prod.ext htu hij
      · have h₁ : t-1 = u := congrArg (fun q => q.1.2) h
        have h₂ : t = u-1 := congrArg (fun q => q.2.2) h
        have hz : (2 : ZMod P.m) = 0 := by linear_combination h₂ - h₁
        exact False.elim (two_ne_zero P hz)
    · rw [endpointCodes_cup P p hp t i hi,endpointCodes_vertical P p hp u j hj] at h
      rcases h with h | h <;>
        have h₁ := congrArg (fun q => q.1.1) h <;>
        have h₂ := congrArg (fun q => q.2.1) h <;> dsimp at h₁ h₂ <;> omega
  · by_cases hj : cup p j
    · rw [endpointCodes_vertical P p hp t i hi,endpointCodes_cup P p hp u j hj] at h
      rcases h with h | h <;>
        have h₁ := congrArg (fun q => q.1.1) h <;>
        have h₂ := congrArg (fun q => q.2.1) h <;> dsimp at h₁ h₂ <;> omega
    · rw [endpointCodes_vertical P p hp t i hi,endpointCodes_vertical P p hp u j hj] at h
      rcases h with h | h
      · have hij : i = j := Fin.ext (congrArg (fun q => q.1.1) h)
        subst j
        have htu : t = u := by
          by_cases hz : i.val = 0
          · have hr : i.val+1 < P.n := by have := P.hn; omega
            have he := congrArg (fun q => q.2.2) h
            simp only [if_pos hr] at he
            linear_combination he
          · have he := congrArg (fun q => q.1.2) h
            simpa only [if_neg hz] using he
        exact Prod.ext htu rfl
      · have h₁ := congrArg (fun q => q.1.1) h
        have h₂ := congrArg (fun q => q.2.1) h
        dsimp at h₁ h₂
        omega

def crossingEdge (P : Parameters) (p : ℕ) (a : Crossing P) : Sym2 (Circle P p) :=
  s((edgeEnds P p a.1 a.2).1,(edgeEnds P p a.1 a.2).2)

theorem crossingEdge_injective (P : Parameters) (p : ℕ) (hp : p < 2) :
    Function.Injective (crossingEdge P p) := by
  intro a b h
  apply unordered_crossing_endpoints_injective P p hp a b
  rcases Sym2.eq_iff.mp h with h | h
  · left
    exact Prod.ext (congrArg (vertexCode P p hp) h.1)
      (congrArg (vertexCode P p hp) h.2)
  · right
    exact Prod.ext (congrArg (vertexCode P p hp) h.1)
      (congrArg (vertexCode P p hp) h.2)

/-- Every simple edge has exactly one original crossing label. -/
def crossingEdgeEquiv (P : Parameters) (p : ℕ) (hp : p < 2) :
    Crossing P ≃ (referenceGraph P p hp Finset.univ).edgeSet :=
  Equiv.ofBijective
    (fun a => ⟨crossingEdge P p a,(referenceGraph P p hp Finset.univ).mem_edgeSet.mpr
      ⟨a,Finset.mem_univ _,Or.inl ⟨rfl,rfl⟩⟩⟩)
    ⟨by
      intro a b h
      exact crossingEdge_injective P p hp (congrArg Subtype.val h),by
      rintro ⟨e,he⟩
      induction e using Sym2.inductionOn with
      | hf u v =>
        obtain ⟨a,ha,h⟩ := (referenceGraph P p hp Finset.univ).mem_edgeSet.mp he
        refine ⟨a,Subtype.ext ?_⟩
        rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · rfl
        · exact Sym2.eq_swap⟩

theorem referenceGraph_edge_card (P : Parameters) (p : ℕ) (hp : p < 2) :
    Nat.card (referenceGraph P p hp Finset.univ).edgeSet = P.n * P.m := by
  rw [← Nat.card_congr (crossingEdgeEquiv P p hp),Nat.card_eq_fintype_card]
  simp [Crossing,Fintype.card_prod,Nat.mul_comm]

end D5.S3.Topology.WeavingReferenceIncidence

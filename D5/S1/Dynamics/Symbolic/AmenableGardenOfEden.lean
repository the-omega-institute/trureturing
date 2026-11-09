/- GID: D5/S1/Dynamics/Symbolic/AmenableGardenOfEden
   generality: G
   mirror-B: D5/B/S1/Dynamics/Symbolic/AmenableGardenOfEden
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite collars and actual image patterns for group cellular maps. -/

import D5.S1.Dynamics.Symbolic.LatticeGardenOfEden
import Mathlib.MeasureTheory.Group.FoelnerFilter
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Algebra.Group.Action.Opposite

/-! Finite-pattern arguments for full shifts on arbitrary groups. -/

set_option autoImplicit false

noncomputable section

namespace D5.S1.Dynamics.Symbolic.AmenableGardenOfEden

open Set Function

universe u v

variable {G : Type v} [Group G] {A : Type u}

/-- The full cellular map with right-multiplied neighborhood coordinates. -/
def localMap (S : Finset G) (φ : (S → A) → A) (x : G → A) : G → A :=
  fun g => φ (fun s => x (g * s))

/-- Injectivity on configurations differing at only finitely many sites. -/
def Preinjective (S : Finset G) (φ : (S → A) → A) : Prop :=
  ∀ x y : G → A, Set.Finite {g | x g ≠ y g} → localMap S φ x = localMap S φ y → x = y

/-- Joint restrictions of one complete cellular image. -/
def ImagePatterns (S : Finset G) (φ : (S → A) → A) (F : Finset G) :=
  Set.range (fun x : G → A => fun f : F => localMap S φ x f)

/-- Replace the pattern on the left translate `t*C`, retaining its complement. -/
def writePattern (C : Finset G) (p : C → A) (t : G) (x : G → A) : G → A := by
  classical
  exact fun g => if h : t⁻¹ * g ∈ C then p ⟨t⁻¹ * g, h⟩ else x g

private def collar (D S : Finset G) : Finset G := by
  classical
  exact D ∪ D.biUnion (fun a => S.biUnion (fun s => S.image (fun r => a * s⁻¹ * r)))

private theorem mem_collar_core (D S : Finset G) {a : G} (ha : a ∈ D) :
    a ∈ collar D S := by
  classical
  exact Finset.mem_union_left _ ha

private theorem mem_collar_window (D S : Finset G) {a s r : G}
    (ha : a ∈ D) (hs : s ∈ S) (hr : r ∈ S) : a * s⁻¹ * r ∈ collar D S := by
  classical
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
    ⟨a, ha, Finset.mem_biUnion.mpr ⟨s, hs, Finset.mem_image.mpr ⟨r, hr, rfl⟩⟩⟩)

private theorem localMap_piecewise_of_collar (D S : Finset G) (φ : (S → A) → A)
    {x y z : G → A} (hout : ∀ a, a ∉ D → x a = y a)
    (himage : localMap S φ x = localMap S φ y)
    (hz : ∀ a ∈ collar D S, z a = x a) :
    localMap S φ ((↑(collar D S) : Set G).piecewise y z) = localMap S φ z := by
  classical
  funext a
  by_cases htouch : ∃ s : S, a * s ∈ D
  · obtain ⟨s, hs⟩ := htouch
    have hwindow (r : S) : a * r ∈ collar D S := by
      simpa only [mul_inv_cancel_right] using mem_collar_window D S hs s.property r.property
    change φ (fun r : S => (↑(collar D S) : Set G).piecewise y z (a * r)) =
      φ (fun r : S => z (a * r))
    have hp : (fun r : S => (↑(collar D S) : Set G).piecewise y z (a * r)) =
        (fun r : S => y (a * r)) := by
      funext r
      exact Set.piecewise_eq_of_mem _ _ _ (hwindow r)
    have he : (fun r : S => z (a * r)) = (fun r : S => x (a * r)) :=
      funext (fun r => hz _ (hwindow r))
    rw [hp, he]
    exact (congrFun himage a).symm
  · apply congrArg φ
    funext r
    change (↑(collar D S) : Set G).piecewise y z (a * r) = z (a * r)
    by_cases hc : a * r ∈ collar D S
    · rw [Set.piecewise_eq_of_mem _ _ _ hc]
      exact (hout _ (fun hd => htouch ⟨r, hd⟩)).symm.trans (hz _ hc).symm
    · exact Set.piecewise_eq_of_notMem _ _ _ hc

private theorem writePattern_at (C : Finset G) (p : C → A) (t : G) (x : G → A)
    (c : C) : writePattern C p t x (t * c) = p c := by
  classical
  simp only [writePattern, inv_mul_cancel_left]
  exact dite_eq_left c.property

private theorem exists_erasable_shape (S : Finset G) (φ : (S → A) → A)
    {x y : G → A} (hf : Set.Finite {a | x a ≠ y a})
    (hi : localMap S φ x = localMap S φ y) (hne : x ≠ y) :
    ∃ C : Finset G, ∃ p q : C → A, p ≠ q ∧
      ∀ (t : G) (z : G → A), (∀ c : C, z (t * c) = p c) →
        localMap S φ (writePattern C q t z) = localMap S φ z := by
  classical
  let D := hf.toFinset
  let C := collar D S
  let p : C → A := fun c => x c
  let q : C → A := fun c => y c
  have hout (a : G) (ha : a ∉ D) : x a = y a := by
    simpa only [D, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using ha
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hne
  have haD : a ∈ D := by
    simpa only [D, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using ha
  have haC : a ∈ C := mem_collar_core D S haD
  refine ⟨C, p, q, (fun he => ha (congrFun he ⟨a, haC⟩)), ?_⟩
  intro t z hz
  let z' : G → A := fun b => z (t * b)
  have hz' : ∀ b ∈ collar D S, z' b = x b := fun b hb => hz ⟨b, hb⟩
  have he := localMap_piecewise_of_collar D S φ hout hi hz'
  funext b
  have he' := congrFun he (t⁻¹ * b)
  change φ (fun s : S => (↑C : Set G).piecewise y z' (t⁻¹ * b * s)) =
    φ (fun s : S => z' (t⁻¹ * b * s)) at he'
  have hw : (fun s : S => writePattern C q t z (b * s)) =
      (fun s : S => (↑C : Set G).piecewise y z' (t⁻¹ * b * s)) := by
    funext s
    dsimp only [writePattern]
    rw [← mul_assoc]
    split_ifs with hc
    · exact (Set.piecewise_eq_of_mem _ _ _ hc).symm
    · rw [Set.piecewise_eq_of_notMem _ _ _ hc]
      simp only [z', mul_assoc, mul_inv_cancel_left]
  change φ (fun s : S => writePattern C q t z (b * s)) = φ (fun s : S => z (b * s))
  rw [hw, he']
  congr 1
  funext s
  simp only [z', mul_assoc, mul_inv_cancel_left]

end D5.S1.Dynamics.Symbolic.AmenableGardenOfEden

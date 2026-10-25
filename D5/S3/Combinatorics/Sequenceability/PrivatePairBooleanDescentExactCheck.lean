import D5.S3.Combinatorics.Sequenceability.PrivatePairBooleanDescent
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
open scoped BigOperators
open Finset
open D5.S3.Combinatorics.Sequenceability.PrivatePairBooleanDescent
noncomputable section
universe u
variable {X : Type u} [DecidableEq X]

-- The source rows are exactly ORIGINAL H, and the coefficient domain is finite H.
example (E : Finset X) (H : Finset (Finset X))
    (hH : ∀ A ∈ H, A ⊆ E ∧ A.Nonempty ∧ A ≠ E)
    (hcover : ∀ b : List X, b.Perm E.toList →
      ∃ t : List X, t <:+: b ∧ t.toFinset ∈ H)
    (S : Finset X)
    (hS : Minimal (Submodule.span ℤ (row '' (H : Set (Finset X)))) E S)
    (hsize : 3 ≤ S.card) (u v : X) (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v)
    (hprivate : ∀ B,
      Minimal (Submodule.span ℤ (row '' (H : Set (Finset X)))) E B →
      (u ∈ B ∨ v ∈ B) → B = S) :
    let M := Submodule.span ℤ (row '' (H : Set (Finset X)))
    let Y := (E.erase u).erase v
    Covers M Y ∧
    (∀ z ∈ reducedSpan M Y, ∃ c : H → ℤ,
      ∑ A : H, c A • row (A : Finset X) = embed Y z) ∧
    (∀ i : Y, Pi.single i (1 : ℤ) ∈ reducedSpan M Y →
      ∃ c : H → ℤ, ∑ A : H, c A • row (A : Finset X) = Pi.single i.val 1) ∧
    (∀ i j : Y, (Pi.single i (1 : ℤ) : Y → ℤ) - Pi.single j (1 : ℤ) ∈ reducedSpan M Y →
      ∃ c : H → ℤ, ∑ A : H, c A • row (A : Finset X) =
        Pi.single i.val 1 - Pi.single j.val 1) := by
  let M := Submodule.span ℤ (row '' (H : Set (Finset X)))
  let Y := (E.erase u).erase v
  have hc : Covers M E := by
    intro b hb he
    have hpw : b.Perm E.toList := by
      apply (List.perm_ext_iff_of_nodup hb E.nodup_toList).mpr
      intro i
      rw [← List.mem_toFinset,he]
      simp
    obtain ⟨t,hti,htH⟩ := hcover b hpw
    obtain ⟨hs,hn,hp⟩ := hH t.toFinset htH
    exact ⟨t,hti,hs,hn,hp,Submodule.subset_span ⟨t.toFinset,htH,rfl⟩⟩
  obtain ⟨hy,_,hspan,_,hunit,hdiff⟩ :=
    private_pair_exact_boolean_descent M E S hc hS hsize u v hu hv huv hprivate
  have hcoeff : ∀ z ∈ reducedSpan M Y, ∃ c : H → ℤ,
      ∑ A : H, c A • row (A : Finset X) = embed Y z := by
    intro z hz
    exact Submodule.mem_span_image_finset_iff_exists_fun.mp (hspan z hz)
  refine ⟨hy,hcoeff,?_,?_⟩
  · intro i hi
    obtain ⟨c,hc⟩ := hcoeff _ hi
    exact ⟨c,hc.trans (hunit i)⟩
  · intro i j hij
    obtain ⟨c,hc⟩ := hcoeff _ hij
    exact ⟨c,hc.trans (hdiff i j)⟩

-- Literal n=2 repaired original lift and both nonempty proper reduced pieces.
example : ([0,2,1,3] : List (Fin 4)).Nodup ∧
    ([0,2,1,3] : List (Fin 4)).toFinset = univ ∧
    ([2] : List (Fin 4)) <:+: [2,3] ∧
    ([3] : List (Fin 4)) <:+: [2,3] ∧
    ({2} : Finset (Fin 4)) ≠ {2,3} ∧ ({3} : Finset (Fin 4)) ≠ {2,3} := by decide

-- The exact complement uses unchanged ORIGINAL coordinates and coefficients +1,-1.
example : row ({3} : Finset (Fin 4)) = row {2,3} - row {2} := by
  ext i
  fin_cases i <;> norm_num [row]

-- Exact ORIGINAL-H complement coefficients, with no division or saturation.
example (H : Finset (Finset X)) (Y A : Finset X) (hAY : A ⊆ Y) (hA : A ∈ H)
    (cY : H → ℤ) (hcY : ∑ j : H, cY j • row (j : Finset X) = row Y) :
    ∑ j : H, (cY j - Pi.single (⟨A,hA⟩ : H) (1 : ℤ) j) • row (j : Finset X)
      = row (Y \ A) := by
  classical
  calc
    _ = (∑ j : H, cY j • row (j : Finset X)) -
        ∑ j : H, Pi.single (⟨A,hA⟩ : H) (1 : ℤ) j • row (j : Finset X) := by
      simp_rw [sub_smul]
      exact Finset.sum_sub_distrib
    _ = row Y - row A := by rw [hcY]; simp [Pi.single_apply, eq_comm]
    _ = row (Y \ A) := by
      ext i
      by_cases ha : i ∈ A <;> by_cases hy : i ∈ Y <;> simp_all [row]

set_option pp.universes true in
#check @D5.S3.Combinatorics.Sequenceability.PrivatePairBooleanDescent.private_pair_exact_boolean_descent

#print axioms D5.S3.Combinatorics.Sequenceability.PrivatePairBooleanDescent.private_pair_exact_boolean_descent

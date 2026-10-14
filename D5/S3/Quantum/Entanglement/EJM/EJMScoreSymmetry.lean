/- GID: D5/S3/Quantum/Entanglement/EJM/EJMScoreSymmetry
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMScoreSymmetry
   mirror-E: none(waiver:exact-inflation-score-symmetry)
   anchors: []
   utility: none
   digest: Exact node permutations and outcome relabelings preserve the centered EJM score. -/

import D5.S3.Quantum.Entanglement.EJMInflationScore
import D5.S3.Quantum.Entanglement.EJM.EJMCertificateData

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option linter.style.longLine false

namespace D5.S3.Quantum.Entanglement.EJM.EJMScoreSymmetry
open D5.S3.Quantum.Entanglement.EJMInflationScore
open D5.S3.Quantum.Entanglement.ElegantJointMeasurementInflation
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (trianglePerm singletonPerm)
open scoped BigOperators

def triangleHeadPerm : Fin 12 → Fin 3 → Fin 3 :=
  ![![0,1,2],
    ![0,1,2],
    ![0,1,2],
    ![0,1,2],
    ![0,1,2],
    ![0,1,2],
    ![1,0,2],
    ![1,0,2],
    ![1,0,2],
    ![1,0,2],
    ![1,0,2],
    ![1,0,2]]

def triangleTailPerm : Fin 12 → Fin 7 → Fin 7 :=
  ![![0,1,2,3,4,5,6],
    ![0,2,1,3,5,4,6],
    ![1,0,2,4,3,5,6],
    ![1,2,0,4,5,3,6],
    ![2,0,1,5,3,4,6],
    ![2,1,0,5,4,3,6],
    ![3,4,5,0,1,2,6],
    ![3,5,4,0,2,1,6],
    ![4,3,5,1,0,2,6],
    ![4,5,3,1,2,0,6],
    ![5,3,4,2,0,1,6],
    ![5,4,3,2,1,0,6]]

def singletonTailPerm : Fin 12 → Fin 8 → Fin 8 :=
  ![![0,1,2,3,4,5,6,7],
    ![0,1,4,5,2,3,6,7],
    ![2,3,0,1,4,5,6,7],
    ![2,3,4,5,0,1,6,7],
    ![4,5,0,1,2,3,6,7],
    ![4,5,2,3,0,1,6,7],
    ![1,0,3,2,5,4,7,6],
    ![1,0,5,4,3,2,7,6],
    ![3,2,1,0,5,4,7,6],
    ![3,2,5,4,1,0,7,6],
    ![5,4,1,0,3,2,7,6],
    ![5,4,3,2,1,0,7,6]]

private theorem head_bijective (k : Fin 12) : Function.Bijective (triangleHeadPerm k) := by
  have h : ∀ k : Fin 12, Function.Bijective (triangleHeadPerm k) := by decide
  exact h k

private noncomputable def headEquiv (k : Fin 12) : Fin 3 ≃ Fin 3 :=
  Equiv.ofBijective (triangleHeadPerm k) (head_bijective k)

private def precomposeEquiv {n : ℕ} (π : Fin n ≃ Fin n) :
    (Fin n → Fin 4) ≃ (Fin n → Fin 4) where
  toFun e := e ∘ π
  invFun e := e ∘ π.symm
  left_inv e := by funext i; simp
  right_inv e := by funext i; simp

private def relabelEquiv {n : ℕ} (ν : Fin 4 ≃ Fin 4) :
    (Fin n → Fin 4) ≃ (Fin n → Fin 4) where
  toFun e := ν ∘ e
  invFun e := ν.symm ∘ e
  left_inv e := by funext i; simp
  right_inv e := by funext i; simp

def triangleCentered (F : (Fin 10 → Fin 4) → ℤ) (e : Fin 10 → Fin 4) : ℤ :=
  256 * F e - ∑ h : Fin 3 → Fin 4, ejmIntNumerator (h 0) (h 1) (h 2) *
    F (Fin.append h (fun i : Fin 7 => e (Fin.natAdd 3 i)))

def singletonCentered (F : (Fin 9 → Fin 4) → ℤ) (e : Fin 9 → Fin 4) : ℤ :=
  256 * F e - 64 * ∑ h : Fin 1 → Fin 4,
    F (Fin.append h (fun i : Fin 8 => e (Fin.natAdd 1 i)))

private theorem triangle_perm_append (k : Fin 12) (h : Fin 3 → Fin 4) (t : Fin 7 → Fin 4) :
    (Fin.append h t) ∘ trianglePerm k =
      Fin.append (h ∘ triangleHeadPerm k) (t ∘ triangleTailPerm k) := by
  have hp : ∀ k : Fin 12, ∀ j : Fin 10,
      trianglePerm k j =
        Fin.append (fun i => Fin.castAdd 7 (triangleHeadPerm k i))
          (fun i => Fin.natAdd 3 (triangleTailPerm k i)) j := by decide
  funext j
  refine Fin.addCases (m := 3) (n := 7) (fun i => ?_) (fun i => ?_) j <;>
    simp only [Function.comp_apply, hp, Fin.append_left, Fin.append_right]

private theorem singleton_perm_append (k : Fin 12) (h : Fin 1 → Fin 4) (t : Fin 8 → Fin 4) :
    (Fin.append h t) ∘ singletonPerm k = Fin.append h (t ∘ singletonTailPerm k) := by
  have hp : ∀ k : Fin 12, ∀ j : Fin 9,
      singletonPerm k j =
        Fin.append (fun i : Fin 1 => Fin.castAdd 8 i)
          (fun i => Fin.natAdd 1 (singletonTailPerm k i)) j := by decide
  funext j
  refine Fin.addCases (m := 1) (n := 8) (fun i => ?_) (fun i => ?_) j <;>
    simp only [Function.comp_apply, hp, Fin.append_left, Fin.append_right]

private theorem numerator_head_perm (k : Fin 12) (h : Fin 3 → Fin 4) :
    ejmIntNumerator (h (triangleHeadPerm k 0)) (h (triangleHeadPerm k 1))
      (h (triangleHeadPerm k 2)) = ejmIntNumerator (h 0) (h 1) (h 2) := by
  have hswap (a b c : Fin 4) : ejmIntNumerator b a c = ejmIntNumerator a b c := by
    fin_cases a <;> fin_cases b <;> fin_cases c <;> norm_num [ejmIntNumerator]
  fin_cases k <;> first | rfl | exact hswap _ _ _

private theorem triangle_tail_comp (k : Fin 12) (e : Fin 10 → Fin 4) :
    (fun i : Fin 7 => (e ∘ trianglePerm k) (Fin.natAdd 3 i)) =
      (fun i : Fin 7 => e (Fin.natAdd 3 i)) ∘ triangleTailPerm k := by
  have hp : ∀ k : Fin 12, ∀ i : Fin 7,
      trianglePerm k (Fin.natAdd 3 i) = Fin.natAdd 3 (triangleTailPerm k i) := by decide
  funext i
  simp only [Function.comp_apply, hp]

private theorem singleton_tail_comp (k : Fin 12) (e : Fin 9 → Fin 4) :
    (fun i : Fin 8 => (e ∘ singletonPerm k) (Fin.natAdd 1 i)) =
      (fun i : Fin 8 => e (Fin.natAdd 1 i)) ∘ singletonTailPerm k := by
  have hp : ∀ k : Fin 12, ∀ i : Fin 8,
      singletonPerm k (Fin.natAdd 1 i) = Fin.natAdd 1 (singletonTailPerm k i) := by decide
  funext i
  simp only [Function.comp_apply, hp]

theorem triangleCentered_coordinate (F : (Fin 10 → Fin 4) → ℤ)
    (hF : ∀ (k : Fin 12) e, F (e ∘ trianglePerm k) = F e)
    (k : Fin 12) (e : Fin 10 → Fin 4) :
    triangleCentered F (e ∘ trianglePerm k) = triangleCentered F e := by
  unfold triangleCentered
  rw [hF, triangle_tail_comp]
  congr 1
  let t : Fin 7 → Fin 4 := fun i => e (Fin.natAdd 3 i)
  let g : (Fin 3 → Fin 4) → ℤ := fun h =>
    ejmIntNumerator (h 0) (h 1) (h 2) * F (Fin.append h (t ∘ triangleTailPerm k))
  calc
    ∑ h, g h = ∑ h, g ((precomposeEquiv (headEquiv k)) h) :=
      ((precomposeEquiv (headEquiv k)).sum_comp g).symm
    _ = ∑ h : Fin 3 → Fin 4,
        ejmIntNumerator (h 0) (h 1) (h 2) * F (Fin.append h t) := by
      apply Finset.sum_congr rfl
      intro h _
      change ejmIntNumerator (h (triangleHeadPerm k 0)) (h (triangleHeadPerm k 1))
          (h (triangleHeadPerm k 2)) *
        F (Fin.append (h ∘ triangleHeadPerm k) (t ∘ triangleTailPerm k)) = _
      rw [numerator_head_perm, ← triangle_perm_append, hF]

theorem singletonCentered_coordinate (F : (Fin 9 → Fin 4) → ℤ)
    (hF : ∀ (k : Fin 12) e, F (e ∘ singletonPerm k) = F e)
    (k : Fin 12) (e : Fin 9 → Fin 4) :
    singletonCentered F (e ∘ singletonPerm k) = singletonCentered F e := by
  unfold singletonCentered
  rw [hF, singleton_tail_comp]
  congr 2
  apply Finset.sum_congr rfl
  intro h _
  rw [← singleton_perm_append, hF]

private theorem numerator_relabel (ν : Fin 4 ≃ Fin 4) (a b c : Fin 4) :
    ejmIntNumerator (ν a) (ν b) (ν c) = ejmIntNumerator a b c := by
  simp only [ejmIntNumerator, ne_eq, ν.injective.eq_iff]

private theorem append_relabel {m n : ℕ} (ν : Fin 4 ≃ Fin 4)
    (h : Fin m → Fin 4) (t : Fin n → Fin 4) :
    ν ∘ Fin.append h t = Fin.append (ν ∘ h) (ν ∘ t) := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
    simp only [Function.comp_apply, Fin.append_left, Fin.append_right]

theorem triangleCentered_relabel (F : (Fin 10 → Fin 4) → ℤ)
    (ν : Fin 4 ≃ Fin 4) (hF : ∀ e, F (ν ∘ e) = F e) (e : Fin 10 → Fin 4) :
    triangleCentered F (ν ∘ e) = triangleCentered F e := by
  unfold triangleCentered
  rw [hF]
  congr 1
  let t : Fin 7 → Fin 4 := fun i => e (Fin.natAdd 3 i)
  let g : (Fin 3 → Fin 4) → ℤ := fun h =>
    ejmIntNumerator (h 0) (h 1) (h 2) * F (Fin.append h (ν ∘ t))
  calc
    ∑ h, g h = ∑ h, g ((relabelEquiv ν) h) := ((relabelEquiv ν).sum_comp g).symm
    _ = ∑ h : Fin 3 → Fin 4,
        ejmIntNumerator (h 0) (h 1) (h 2) * F (Fin.append h t) := by
      apply Finset.sum_congr rfl
      intro h _
      change ejmIntNumerator (ν (h 0)) (ν (h 1)) (ν (h 2)) *
        F (Fin.append (ν ∘ h) (ν ∘ t)) = _
      rw [numerator_relabel, ← append_relabel, hF]

theorem singletonCentered_relabel (F : (Fin 9 → Fin 4) → ℤ)
    (ν : Fin 4 ≃ Fin 4) (hF : ∀ e, F (ν ∘ e) = F e) (e : Fin 9 → Fin 4) :
    singletonCentered F (ν ∘ e) = singletonCentered F e := by
  unfold singletonCentered
  rw [hF]
  congr 2
  let t : Fin 8 → Fin 4 := fun i => e (Fin.natAdd 1 i)
  let g : (Fin 1 → Fin 4) → ℤ := fun h => F (Fin.append h (ν ∘ t))
  calc
    ∑ h, g h = ∑ h, g ((relabelEquiv ν) h) := ((relabelEquiv ν).sum_comp g).symm
    _ = ∑ h : Fin 1 → Fin 4, F (Fin.append h t) := by
      apply Finset.sum_congr rfl
      intro h _
      change F (Fin.append (ν ∘ h) (ν ∘ t)) = _
      rw [← append_relabel, hF]

open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (F1 F2)

theorem actual_triangleCentered_coordinate (k : Fin 12) (e : Fin 10 → Fin 4) :
    triangleCentered F1 (e ∘ trianglePerm k) = triangleCentered F1 e :=
  triangleCentered_coordinate F1 (fun j t => EJMCertificateData.F1_coordinate t j) k e

theorem actual_singletonCentered_coordinate (k : Fin 12) (e : Fin 9 → Fin 4) :
    singletonCentered F2 (e ∘ singletonPerm k) = singletonCentered F2 e :=
  singletonCentered_coordinate F2 (fun j t => EJMCertificateData.F2_coordinate t j) k e

theorem actual_triangleCentered_relabel (ν : Fin 4 ≃ Fin 4) (e : Fin 10 → Fin 4) :
    triangleCentered F1 (ν ∘ e) = triangleCentered F1 e :=
  triangleCentered_relabel F1 ν (fun t => EJMCertificateData.F1_relabel t ν ν.injective) e

theorem actual_singletonCentered_relabel (ν : Fin 4 ≃ Fin 4) (e : Fin 9 → Fin 4) :
    singletonCentered F2 (ν ∘ e) = singletonCentered F2 e :=
  singletonCentered_relabel F2 ν (fun t => EJMCertificateData.F2_relabel t ν ν.injective) e

#print axioms actual_triangleCentered_coordinate
#print axioms actual_singletonCentered_coordinate
#print axioms actual_triangleCentered_relabel
#print axioms actual_singletonCentered_relabel

end D5.S3.Quantum.Entanglement.EJM.EJMScoreSymmetry

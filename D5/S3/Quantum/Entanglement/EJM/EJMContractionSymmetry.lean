/- GID: D5/S3/Quantum/Entanglement/EJM/EJMContractionSymmetry
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMContractionSymmetry
   mirror-E: none(waiver:exact-local-tail-contractions)
   anchors: []
   utility: none
   digest: Actual local coordinate and outcome symmetries preserve exact tail contractions. -/

import D5.S3.Quantum.Entanglement.EJM.EJMScoreSymmetry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.EJM.EJMContractionSymmetry
open D5.S3.Quantum.Entanglement.EJMInflationScore
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (F1 F2 trianglePerm singletonPerm)
open D5.S3.Quantum.Entanglement.EJM.EJMScoreSymmetry
open scoped BigOperators

def triangleContraction (F : (Fin 10 → Fin 4) → ℤ) (t : Fin 7 → Fin 4) : ℤ :=
  ∑ h : Fin 3 → Fin 4, ejmIntNumerator (h 0) (h 1) (h 2) * F (Fin.append h t)

def singletonContraction (F : (Fin 9 → Fin 4) → ℤ) (t : Fin 8 → Fin 4) : ℤ :=
  ∑ h : Fin 1 → Fin 4, F (Fin.append h t)

theorem triangleContraction_coordinate (F : (Fin 10 → Fin 4) → ℤ)
    (hF : ∀ (k : Fin 12) e, F (e ∘ trianglePerm k) = F e)
    (k : Fin 12) (t : Fin 7 → Fin 4) :
    triangleContraction F (t ∘ triangleTailPerm k) = triangleContraction F t := by
  let e : Fin 10 → Fin 4 := Fin.append (fun _ : Fin 3 => 0) t
  have hp : ∀ k : Fin 12, ∀ i : Fin 7,
      trianglePerm k (Fin.natAdd 3 i) = Fin.natAdd 3 (triangleTailPerm k i) := by decide
  have ht : (fun i : Fin 7 => (e ∘ trianglePerm k) (Fin.natAdd 3 i)) =
      t ∘ triangleTailPerm k := by
    funext i
    simp only [Function.comp_apply, hp, e, Fin.append_right]
  have hs := triangleCentered_coordinate F hF k e
  change 256 * F (e ∘ trianglePerm k) -
      triangleContraction F (fun i : Fin 7 => (e ∘ trianglePerm k) (Fin.natAdd 3 i)) =
    256 * F e - triangleContraction F (fun i : Fin 7 => e (Fin.natAdd 3 i)) at hs
  rw [hF, ht] at hs
  have htail : (fun i : Fin 7 => e (Fin.natAdd 3 i)) = t := by
    funext i
    exact Fin.append_right _ _ _
  rw [htail] at hs
  omega

theorem singletonContraction_coordinate (F : (Fin 9 → Fin 4) → ℤ)
    (hF : ∀ (k : Fin 12) e, F (e ∘ singletonPerm k) = F e)
    (k : Fin 12) (t : Fin 8 → Fin 4) :
    singletonContraction F (t ∘ singletonTailPerm k) = singletonContraction F t := by
  let e : Fin 9 → Fin 4 := Fin.append (fun _ : Fin 1 => 0) t
  have hp : ∀ k : Fin 12, ∀ i : Fin 8,
      singletonPerm k (Fin.natAdd 1 i) = Fin.natAdd 1 (singletonTailPerm k i) := by decide
  have ht : (fun i : Fin 8 => (e ∘ singletonPerm k) (Fin.natAdd 1 i)) =
      t ∘ singletonTailPerm k := by
    funext i
    simp only [Function.comp_apply, hp, e, Fin.append_right]
  have hs := singletonCentered_coordinate F hF k e
  change 256 * F (e ∘ singletonPerm k) -
      64 * singletonContraction F (fun i : Fin 8 => (e ∘ singletonPerm k) (Fin.natAdd 1 i)) =
    256 * F e - 64 * singletonContraction F (fun i : Fin 8 => e (Fin.natAdd 1 i)) at hs
  rw [hF, ht] at hs
  have htail : (fun i : Fin 8 => e (Fin.natAdd 1 i)) = t := by
    funext i
    exact Fin.append_right _ _ _
  rw [htail] at hs
  omega

theorem triangleContraction_relabel (F : (Fin 10 → Fin 4) → ℤ)
    (ν : Fin 4 ≃ Fin 4) (hF : ∀ e, F (ν ∘ e) = F e) (t : Fin 7 → Fin 4) :
    triangleContraction F (ν ∘ t) = triangleContraction F t := by
  let e : Fin 10 → Fin 4 := Fin.append (fun _ : Fin 3 => 0) t
  have hs := triangleCentered_relabel F ν hF e
  change 256 * F (ν ∘ e) -
      triangleContraction F (fun i : Fin 7 => (ν ∘ e) (Fin.natAdd 3 i)) =
    256 * F e - triangleContraction F (fun i : Fin 7 => e (Fin.natAdd 3 i)) at hs
  simp only [hF, Function.comp_apply, e, Fin.append_right] at hs
  change 256 * F e - triangleContraction F (ν ∘ t) =
    256 * F e - triangleContraction F t at hs
  omega

theorem singletonContraction_relabel (F : (Fin 9 → Fin 4) → ℤ)
    (ν : Fin 4 ≃ Fin 4) (hF : ∀ e, F (ν ∘ e) = F e) (t : Fin 8 → Fin 4) :
    singletonContraction F (ν ∘ t) = singletonContraction F t := by
  let e : Fin 9 → Fin 4 := Fin.append (fun _ : Fin 1 => 0) t
  have hs := singletonCentered_relabel F ν hF e
  change 256 * F (ν ∘ e) -
      64 * singletonContraction F (fun i : Fin 8 => (ν ∘ e) (Fin.natAdd 1 i)) =
    256 * F e - 64 * singletonContraction F (fun i : Fin 8 => e (Fin.natAdd 1 i)) at hs
  simp only [hF, Function.comp_apply, e, Fin.append_right] at hs
  change 256 * F e - 64 * singletonContraction F (ν ∘ t) =
    256 * F e - 64 * singletonContraction F t at hs
  omega

theorem actual_triangleContraction_coordinate (k : Fin 12) (t : Fin 7 → Fin 4) :
    triangleContraction F1 (t ∘ triangleTailPerm k) = triangleContraction F1 t :=
  triangleContraction_coordinate F1 (fun j e => EJMCertificateData.F1_coordinate e j) k t

theorem actual_singletonContraction_coordinate (k : Fin 12) (t : Fin 8 → Fin 4) :
    singletonContraction F2 (t ∘ singletonTailPerm k) = singletonContraction F2 t :=
  singletonContraction_coordinate F2 (fun j e => EJMCertificateData.F2_coordinate e j) k t

theorem actual_triangleContraction_relabel (ν : Fin 4 ≃ Fin 4) (t : Fin 7 → Fin 4) :
    triangleContraction F1 (ν ∘ t) = triangleContraction F1 t :=
  triangleContraction_relabel F1 ν (fun e => EJMCertificateData.F1_relabel e ν ν.injective) t

theorem actual_singletonContraction_relabel (ν : Fin 4 ≃ Fin 4) (t : Fin 8 → Fin 4) :
    singletonContraction F2 (ν ∘ t) = singletonContraction F2 t :=
  singletonContraction_relabel F2 ν (fun e => EJMCertificateData.F2_relabel e ν ν.injective) t

#print axioms actual_triangleContraction_coordinate
#print axioms actual_singletonContraction_coordinate
#print axioms actual_triangleContraction_relabel
#print axioms actual_singletonContraction_relabel

end D5.S3.Quantum.Entanglement.EJM.EJMContractionSymmetry

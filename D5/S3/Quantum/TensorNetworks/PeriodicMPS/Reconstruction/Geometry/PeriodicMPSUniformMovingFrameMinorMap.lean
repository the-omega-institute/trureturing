/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformMovingFrameMinorMap
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformMovingFrameMinorMap
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Scalar extension of section minors. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformMovingFrameMinorRows

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformMovingFrame

open Matrix MvPolynomial TrivSqZeroExt
open scoped Matrix
open PeriodicMPSUniformAntisymmetricTransfer (BondMatrix TransferMatrix mixedRaw)
open PeriodicMPSUniformVerticalSectionRank (transverseKet tripletReadout tripletReadout_eq_native
  tripletRow tripletShear tripletRotation singletTrace singletTrace_eq_native
  sectionTripletMinor sectionSingletMinor TripletIndex SingletIndex)
open private liftCore outerEntry from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformVerticalSectionTrace
open private sectionBra literalOuterColumn endpoint from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformVerticalSectionRank
open private mapCore map_sectionKet map_sectionBra map_mixedRaw
  from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformMovingFrameSection
open private tripletContract_eq tripletContract_raw from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformMovingFrameMinorRows

noncomputable section

variable {R S : Type*} [CommRing R] [CommRing S]

private def mapDual (f : R →+* S) : DualNumber R →+* DualNumber S where
  toFun x := ⟨f x.fst, f x.snd⟩
  map_zero' := TrivSqZeroExt.ext (map_zero f) (map_zero f)
  map_one' := TrivSqZeroExt.ext (map_one f) (map_zero f)
  map_add' x y := TrivSqZeroExt.ext (map_add f x.fst y.fst) (map_add f x.snd y.snd)
  map_mul' x y := by
    apply TrivSqZeroExt.ext
    · exact map_mul f x.fst y.fst
    · change f (x.fst * y.snd + x.snd * y.fst) = f x.fst * f y.snd + f x.snd * f y.fst
      simp only [map_add, map_mul]

private theorem map_tripletRow (f : R →+* S) (h : R) (i : Fin 3)
    (p : Fin 2 × Fin 2) : f (tripletRow h i p) = tripletRow (f h) i p := by
  rcases p with ⟨a,b⟩
  fin_cases i <;> fin_cases a <;> fin_cases b <;> simp [tripletRow]

private theorem map_tripletReadout (f : R →+* S) (h : R) (A B : Core R) (m : ℕ) :
    (tripletReadout h A B m).map f =
      tripletReadout (f h) (mapCore f A) (mapCore f B) m := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.map_apply, tripletReadout_eq_native, map_sum, map_mul, map_tripletRow]
  suffices hh : ∀ p q, f (mixedRaw A B m p q) =
      mixedRaw (mapCore f A) (mapCore f B) m p q by simp only [hh]
  intro p q
  exact congrFun (congrFun (map_mixedRaw f A B m) p) q

private theorem map_singletTrace (f : R →+* S) (h : R) (A B : Core R) (m : ℕ) :
    f (singletTrace h A B m) = singletTrace (f h) (mapCore f A) (mapCore f B) m := by
  have hh : ∀ p q, f (mixedRaw A B m p q) = mixedRaw (mapCore f A) (mapCore f B) m p q :=
    fun p q => congrFun (congrFun (map_mixedRaw f A B m) p) q
  simp only [singletTrace_eq_native, map_mul, map_sub, map_add, hh]

private theorem map_tripletRotation (f : R →+* S) (upper : Bool) (W : Matrix (Fin 3) (Fin 3) R) :
    (tripletRotation upper W).map f = tripletRotation upper (W.map f) := by
  have hh (b : Bool) : f.mapMatrix (tripletShear b) = tripletShear b := by
    apply Matrix.ext
    intro i j
    cases b <;> fin_cases i <;> fin_cases j <;>
      simp [tripletShear, RingHom.mapMatrix_apply, map_ofNat]
  change f.mapMatrix (tripletRotation upper W) = _
  rw [tripletRotation, map_sub, map_mul, map_mul, hh]
  have hT : f.mapMatrix ((tripletShear (R := R) (!upper)).transpose) =
      (tripletShear (!upper) : Matrix (Fin 3) (Fin 3) S).transpose := by
    rw [← hh (!upper)]
    rfl
  rw [hT]
  rfl

private theorem mapLiftCore (f : R →+* S) (A : Core R) :
    mapCore (mapDual f) (fun i => liftCore (A i)) = fun i => liftCore ((mapCore f A) i) := by
  funext i
  apply Matrix.ext
  intro p q
  apply TrivSqZeroExt.ext
  · rfl
  · exact map_zero f

variable [Algebra ℂ R] [Algebra ℂ S]

private theorem map_parts (σ : R →ₐ[ℂ] S) (x : Fin 5 → R) (m : ℕ) :
    let a : ℂ := 1 / 2
    let h := algebraMap ℂ R a
    let h' := algebraMap ℂ S a
    let B := sectionBra x
    let B' := sectionBra (σ ∘ x)
    let F := tripletReadout h (transverseKet 0) B m
    let F' := tripletReadout h' (transverseKet 0) B' m
    let N := tripletReadout (inl h) (transverseKet (inr 1))
      (fun i => liftCore (B i)) m
    let N' := tripletReadout (inl h') (transverseKet (inr 1))
      (fun i => liftCore (B' i)) m
    F.map σ = F' ∧
      (∀ b, (tripletRotation b F).map σ = tripletRotation b F') ∧
      (N.map snd).map σ = N'.map snd := by
  dsimp only
  let f := σ.toRingHom
  have h₀ : mapCore f (transverseKet (0 : R)) = transverseKet (0 : S) :=
    (map_sectionKet f 0).trans (congrArg transverseKet (map_zero f))
  have h₁ : mapCore (mapDual f) (transverseKet (inr (1 : R))) = transverseKet (inr (1 : S)) :=
    (map_sectionKet (mapDual f) _).trans (congrArg transverseKet
      (TrivSqZeroExt.ext (map_zero f) (map_one f)))
  have hB : mapCore f (sectionBra x) = sectionBra (σ ∘ x) := map_sectionBra f x
  have hh : f (algebraMap ℂ R (1 / 2)) = algebraMap ℂ S (1 / 2) :=
    σ.commutes _
  have hh' : mapDual f (inl (algebraMap ℂ R (1 / 2))) = inl (algebraMap ℂ S (1 / 2)) :=
    TrivSqZeroExt.ext hh (map_zero f)
  have hF := map_tripletReadout f (algebraMap ℂ R (1 / 2)) (transverseKet 0) (sectionBra x) m
  rw [h₀, hB, hh] at hF
  refine ⟨hF, fun b => (map_tripletRotation f b _).trans (congrArg (tripletRotation b) hF), ?_⟩
  have hN := map_tripletReadout (mapDual f) (inl (algebraMap ℂ R (1 / 2)))
    (transverseKet (inr 1)) (fun i => liftCore (sectionBra x i)) m
  rw [h₁, mapLiftCore, hB, hh'] at hN
  exact congrArg (Matrix.map · snd) hN

theorem sectionTripletMinor_map (σ : R →ₐ[ℂ] S) (x : Fin 5 → R) (m : ℕ) :
    (sectionTripletMinor (1 / 2 : ℂ) m x).map σ =
      sectionTripletMinor (1 / 2 : ℂ) m (σ ∘ x) := by
  obtain ⟨_, hr, hn⟩ := map_parts σ x m
  let H : MvPolynomial (Fin 5) ℂ →ₐ[ℂ] S := σ.comp (aeval x)
  have hH : H = aeval (σ ∘ x) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [H, Function.comp_apply]
  unfold sectionTripletMinor
  dsimp only
  rw [Matrix.fromBlocks_map]
  congr 1
  · rw [Matrix.map_map]
    exact congrArg (Matrix.map (literalOuterColumn (1 / 2 : ℂ) m) ·) (congrArg DFunLike.coe hH)
  · apply Matrix.ext
    intro i j
    fin_cases j
    · exact congrFun (congrFun (hr false) _) _
    · exact congrFun (congrFun (hr true) _) _
    · exact congrFun (congrFun hn _) _
  · apply Matrix.ext
    intro i j
    exact map_zero σ
  · apply Matrix.ext
    intro i j
    fin_cases j
    · exact congrFun (congrFun (hr false) _) _
    · exact congrFun (congrFun (hr true) _) _
    · exact congrFun (congrFun hn _) _

theorem sectionSingletMinor_map (σ : R →ₐ[ℂ] S) (x : Fin 5 → R) (m : ℕ) :
    (sectionSingletMinor (1 / 2 : ℂ) m x).map σ =
      sectionSingletMinor (1 / 2 : ℂ) m (σ ∘ x) := by
  have h := sectionTripletMinor_map σ x m
  let f := σ.toRingHom
  have hS := map_singletTrace (mapDual f) (inl (algebraMap ℂ R (1 / 2)))
    (transverseKet (inr 1)) (fun i => liftCore (sectionBra x i)) m
  have h₁ : mapCore (mapDual f) (transverseKet (inr (1 : R))) = transverseKet (inr (1 : S)) :=
    (map_sectionKet (mapDual f) _).trans (congrArg transverseKet
      (TrivSqZeroExt.ext (map_zero f) (map_one f)))
  have hh' : mapDual f (inl (algebraMap ℂ R (1 / 2))) = inl (algebraMap ℂ S (1 / 2)) :=
    TrivSqZeroExt.ext (σ.commutes _) (map_zero f)
  rw [h₁, hh', mapLiftCore, map_sectionBra] at hS
  have hh := congrArg snd hS
  apply Matrix.ext
  intro i j
  rcases i with i | (i | i) <;> rcases j with j | (j | j)
  · exact congrFun (congrFun h (.inl i)) (.inl j)
  · exact congrFun (congrFun h (.inl i)) (.inr j.castSucc)
  · exact congrFun (congrFun h (.inl i)) (.inr 2)
  · exact map_zero σ
  · exact congrFun (congrFun h (.inr (endpoint i))) (.inr j.castSucc)
  · exact congrFun (congrFun h (.inr (endpoint i))) (.inr 2)
  · exact map_zero σ
  · exact map_zero σ
  · exact hh

end
end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformMovingFrame

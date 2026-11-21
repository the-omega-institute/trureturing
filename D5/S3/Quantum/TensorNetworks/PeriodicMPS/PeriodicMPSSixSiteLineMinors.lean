/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteLineMinors
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteLineMinors
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteLineMinors]
   utility: none
   digest: Two critical minors of the six-site adjacent-marginal projection. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteLineMinors
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteMarginal

/-! The two derivatives of the complexified density are evaluated in independent trace inputs. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteLineMinors

open Matrix Polynomial PeriodicMPSSixSiteCoordinates PeriodicMPSSixSiteMarginal
open PeriodicMPSFiveSiteLineMinors (line map_line)
open scoped BigOperators

private def observedRows : Fin 10 → Fin 4 × Fin 4 :=
  ![(0,0), (0,1), (0,3), (1,0), (1,1), (1,2), (1,3), (3,0), (3,1), (3,3)]

private def amplitudes {R : Type*} [CommRing R] (a : Fin 10 → R) (left : Bool) :
    Fin 14 → R :=
  if left then coordinates (a 0 ^ 2) (a 0 * a 1) (a 1 ^ 2) (a 2) (a 3) (a 4)
  else coordinates (a 5 ^ 2) (a 5 * a 6) (a 6 ^ 2) (a 7) (a 8) (a 9)

/-- The raw complexified observation with independent forward and reverse inputs. -/
def observation {R : Type*} [CommRing R] (a : Fin 10 → R) (k : Fin 10) : R :=
  let i := observedRows k
  ∑ j : Fin 16, flatten (amplitudes a true) i.1 j * flatten (amplitudes a false) i.2 j

/-- The Jacobian in weighted trace coordinates, before the square substitution. -/
def jacobian {R : Type*} [CommRing R] (a : Fin 10 → R) : Matrix (Fin 10) (Fin 10) R :=
  fun i j => (observation (R := DualNumber R)
    (fun k => ⟨a k, if k = j then 1 else 0⟩) i).snd

/-- The weighted-coordinate minor with the indicated trace row and column deleted. -/
def residualMinor {R : Type*} [CommRing R] (q : R) (k : Fin 10) : R :=
  ((jacobian (line q)).submatrix k.succAbove k.succAbove).det

set_option maxHeartbeats 900000 in
-- Check the fourteen weight-two coordinate expressions under a coefficient map.
private theorem map_coordinates {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (T U V d e k : R) :
    f ∘ coordinates T U V d e k = coordinates (f T) (f U) (f V) (f d) (f e) (f k) := by
  funext i
  fin_cases i <;> simp [coordinates, map_ofNat]

private theorem map_amplitudes {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a : Fin 10 → R) (b : Bool) :
    f ∘ amplitudes a b = amplitudes (f ∘ a) b := by
  cases b <;> simp only [amplitudes, Bool.false_eq_true, if_false, if_true, Function.comp_apply,
    ← map_mul, ← map_pow] <;> exact map_coordinates f _ _ _ _ _ _

private lemma map_flatten {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (p : Fin 14 → R) :
    (flatten p).map f = flatten (f ∘ p) := by
  ext i j
  rfl

theorem map_observation {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a : Fin 10 → R) (i : Fin 10) :
    f (observation a i) = observation (f ∘ a) i := by
  have ha (b : Bool) : f ∘ amplitudes a b = amplitudes (f ∘ a) b := by
    exact map_amplitudes f a b
  simp only [observation, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro j _
  have h₁ := congrArg (fun M : Matrix (Fin 4) (Fin 16) S => M (observedRows i).1 j)
    ((map_flatten f (amplitudes a true)).trans (congrArg flatten (ha true)))
  have h₂ := congrArg (fun M : Matrix (Fin 4) (Fin 16) S => M (observedRows i).2 j)
    ((map_flatten f (amplitudes a false)).trans (congrArg flatten (ha false)))
  exact congrArg₂ (· * ·) h₁ h₂

private def mapDual {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    DualNumber R →+* DualNumber S where
  toFun x := ⟨f x.fst, f x.snd⟩
  map_one' := by ext <;> simp
  map_mul' x y := by
    apply TrivSqZeroExt.ext
    · change f (x.fst * y.fst) = f x.fst * f y.fst
      exact map_mul f _ _
    · let u : DualNumber S := ⟨f x.fst, f x.snd⟩
      let v : DualNumber S := ⟨f y.fst, f y.snd⟩
      change f (TrivSqZeroExt.snd (x * y)) = TrivSqZeroExt.snd (u * v)
      rw [TrivSqZeroExt.snd_mul x y, TrivSqZeroExt.snd_mul u v]
      simp [smul_eq_mul, mul_comm, u, v]
  map_zero' := by ext <;> simp
  map_add' x y := by
    apply TrivSqZeroExt.ext
    · exact map_add f _ _
    · exact map_add f _ _

theorem map_jacobian {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a : Fin 10 → R) :
    (jacobian a).map f = jacobian (f ∘ a) := by
  ext i j
  let b : Fin 10 → DualNumber R := fun k => ⟨a k, if k = j then 1 else 0⟩
  have h : mapDual f ∘ b = (fun k => ⟨f (a k), if k = j then 1 else 0⟩) := by
    funext k
    apply TrivSqZeroExt.ext
    · rfl
    · change f (if k = j then 1 else 0) = _
      split <;> simp
  have he := map_observation (mapDual f) b i
  rw [h] at he
  exact congrArg TrivSqZeroExt.snd he

theorem map_minor {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (q : R) (k : Fin 10) : f (residualMinor q k) = residualMinor (f q) k := by
  rw [residualMinor, residualMinor, RingHom.map_det]
  congr 1
  have h := map_jacobian f (line q)
  rw [map_line] at h
  exact congrArg (fun M : Matrix (Fin 10) (Fin 10) S =>
    M.submatrix k.succAbove k.succAbove) h

/-- The formula for the minor commutes with evaluation and coefficient reduction. -/
theorem eval₂_minor {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (q : S) (k : Fin 10) :
    (residualMinor (X : R[X]) k).eval₂ f q = residualMinor q k := by
  simpa using map_minor (eval₂RingHom f q) X k

end D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteLineMinors

/- GID: D5/S3/HomologicalAlgebra/QuaternionCandidateRestriction
   generality: I
   mirror-B: D5/B/S3/HomologicalAlgebra/QuaternionCandidateRestriction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.GroupTheory.SpecificGroups.Quaternion]
   utility: none
   digest: A quaternion subgroup distinguishes the split quadratic anomaly candidate. -/

import D5.S3.HomologicalAlgebra.InflatedCubicCandidate

/-! The split quadratic candidate restricts to the quaternion bar detector. -/

open scoped BigOperators

set_option autoImplicit false

noncomputable section

namespace D5.S3.HomologicalAlgebra.QuaternionCandidateRestriction

open D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient (F₂ SignExtension)
open InflatedCubicCandidate
  (Charge ChargeGroup d₂ d₃ etaQ Normalized circle_inflation_has_two_candidates)
open BarnesWallQ8CohomologyDetector
  (Q8 quotientCoordinates etaPolynomial etaExponent coefficientHom coefficientRep eta
    eta_not_coboundary CircleCoefficients half half_add_half half_ne_zero)
open groupCohomology (d₂₃)

variable {ι : Type*} [Fintype ι]

/-- The split extension bilinear form in the ordered charge coordinates. -/
def splitCocycle : Charge ι →+ Charge ι →+ F₂ where
  toFun x :=
    { toFun := fun y => ∑ i, x (i, false) * y (i, true)
      map_zero' := by simp
      map_add' := by
        intro y z
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib] }
  map_zero' := by
    apply AddMonoidHom.ext
    intro y
    change (∑ i, (0 : Charge ι) (i, false) * y (i, true)) = 0
    simp
  map_add' := by
    intro x y
    apply AddMonoidHom.ext
    intro z
    change (∑ i, (x + y) (i, false) * z (i, true)) =
      (∑ i, x (i, false) * z (i, true)) + ∑ i, y (i, false) * z (i, true)
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

variable [DecidableEq ι]

/-- The charge plane sends `(u,v)` to `(X_a,Y_a) = (u+v,u)` and
`(X_b,Y_b) = (v,v)`, with zero coordinates away from the two slots. -/
def plane (a b : ι) : (F₂ × F₂) →+ Charge ι where
  toFun p x :=
    if x.1 = a then (if x.2 then p.1 else p.1 + p.2)
    else if x.1 = b then p.2 else 0
  map_zero' := by
    funext x
    change (if x.1 = a then (if x.2 then (0 : F₂) else 0 + 0)
      else if x.1 = b then 0 else 0) = 0
    simp
  map_add' := by
    intro p q
    funext x
    rcases x with ⟨i, bit⟩
    by_cases ha : i = a
    · cases bit <;> simp [ha, Pi.add_apply, Prod.fst_add, Prod.snd_add,
        add_assoc, add_left_comm, add_comm]
    · by_cases hb : i = b
      · subst i
        simp [ha, Pi.add_apply, Prod.snd_add]
      · simp [ha, hb, Pi.add_apply]

private theorem sum_two_slots (a b : ι) (hab : a ≠ b) (f : ι → F₂)
    (hf : ∀ i, i ≠ a → i ≠ b → f i = 0) :
    ∑ i, f i = f a + f b := by
  calc
    ∑ i, f i = ∑ i ∈ ({a, b} : Finset ι), f i := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      exact hf i (fun h => hi (by simp [h])) (fun h => hi (by simp [h]))
    _ = _ := by simp [hab]

theorem splitCocycle_plane (a b : ι) (hab : a ≠ b) (p q : F₂ × F₂) :
    splitCocycle (plane a b p) (plane a b q) = (p.1 + p.2) * q.1 + p.2 * q.2 := by
  change (∑ i, plane a b p (i, false) * plane a b q (i, true)) = _
  refine (sum_two_slots a b hab _ ?_).trans ?_
  · intro i ha hb
    simp [plane, ha, hb]
  · simp [plane, hab.symm]

theorem etaQ_plane (a b : ι) (hab : a ≠ b) (p q r : F₂ × F₂) :
    etaQ (plane a b p) (plane a b q) (plane a b r) = etaPolynomial p q r := by
  unfold etaQ etaPolynomial
  refine (sum_two_slots a b hab _ ?_).trans ?_
  · intro i ha hb
    simp [plane, ha, hb]
  · simp [plane, hab.symm]

private abbrev coordinates (g : Q8) : F₂ × F₂ := (quotientCoordinates g).toAdd

/-- In the `j i^r` normal form, an odd power of `i` adds the sign from `c(j,i)=1`. -/
private def quaternionSign : Q8 → F₂
  | .a r => ((r.val / 2 : ℕ) : F₂)
  | .xa r => ((r.val / 2 : ℕ) : F₂) + (r.val : F₂)

private theorem quaternionSign_mul : ∀ g h : Q8,
    quaternionSign (g * h) = quaternionSign g + quaternionSign h +
      (((coordinates g).1 + (coordinates g).2) * (coordinates h).1 +
        (coordinates g).2 * (coordinates h).2) := by
  decide +kernel

private theorem quaternionSign_coordinates_injective : ∀ g h : Q8,
    quaternionSign g = quaternionSign h → coordinates g = coordinates h → g = h := by
  decide +kernel

/-- The quaternion lift into the split sign extension supported on two slots. -/
def quaternionLift (a b : ι) (hab : a ≠ b) :
    Q8 →* SignExtension (Charge ι) splitCocycle where
  toFun g := ⟨quaternionSign g, plane a b (coordinates g)⟩
  map_one' := by
    apply SignExtension.ext
    · change quaternionSign 1 = 0
      decide +kernel
    · change plane a b (quotientCoordinates 1).toAdd = 0
      rw [quotientCoordinates.map_one]
      change plane a b 0 = 0
      exact map_zero _
  map_mul' g h := by
    apply SignExtension.ext
    · change quaternionSign (g * h) = quaternionSign g + quaternionSign h +
        splitCocycle (plane a b (coordinates g)) (plane a b (coordinates h))
      rw [splitCocycle_plane a b hab]
      exact quaternionSign_mul g h
    · change plane a b (quotientCoordinates (g * h)).toAdd =
        plane a b (coordinates g) + plane a b (coordinates h)
      rw [quotientCoordinates.map_mul]
      change plane a b (coordinates g + coordinates h) = _
      exact map_add _ _ _

theorem quaternionLift_injective (a b : ι) (hab : a ≠ b) :
    Function.Injective (quaternionLift a b hab) := by
  intro g h heq
  have hs : quaternionSign g = quaternionSign h := congrArg SignExtension.sign heq
  have hc : plane a b (coordinates g) = plane a b (coordinates h) :=
    congrArg SignExtension.charge heq
  have hu : (coordinates g).1 = (coordinates h).1 := by
    simpa [plane] using congrFun hc (a, true)
  have hv : (coordinates g).2 = (coordinates h).2 := by
    simpa [plane, hab.symm] using congrFun hc (b, true)
  exact quaternionSign_coordinates_injective g h hs (Prod.ext hu hv)

theorem etaQ_quaternionLift (a b : ι) (hab : a ≠ b) (g h k : Q8) :
    etaQ (quaternionLift a b hab g).charge (quaternionLift a b hab h).charge
      (quaternionLift a b hab k).charge = etaExponent (g, h, k) :=
  etaQ_plane a b hab (coordinates g) (coordinates h) (coordinates k)

/-- Any coboundary for the split candidate would pull back to one for the detector. -/
theorem etaQ_not_coboundary (a b : ι) (hab : a ≠ b) {M : Type} [AddCommGroup M]
    (t : M) (ht : t + t = 0) (hne : t ≠ 0)
    (B : SignExtension (Charge ι) splitCocycle → SignExtension (Charge ι) splitCocycle → M) :
    ¬ ∀ g h k : SignExtension (Charge ι) splitCocycle,
      d₂ B g h k = coefficientHom t ht (etaQ g.charge h.charge k.charge) := by
  intro hB
  let A := coefficientRep M
  let lift := quaternionLift a b hab
  let β : Q8 × Q8 → M := fun p => B (lift p.1) (lift p.2)
  have hβ : d₂₃ A β = eta t ht := by
    funext p
    rcases p with ⟨g, h, k⟩
    change B (lift h) (lift k) - B (lift (g * h)) (lift k) +
      B (lift g) (lift (h * k)) - B (lift g) (lift h) =
        coefficientHom t ht (etaExponent (g, h, k))
    simp only [map_mul]
    change d₂ B (lift g) (lift h) (lift k) = _
    rw [hB]
    exact congrArg (coefficientHom t ht) (etaQ_quaternionLift a b hab g h k)
  exact eta_not_coboundary t ht hne β hβ

private theorem candidate_index_unique (a b : ι) (hab : a ≠ b)
    (e e' : F₂)
    (B B' : SignExtension (Charge ι) splitCocycle →
      SignExtension (Charge ι) splitCocycle → CircleCoefficients)
    (heq : ∀ g h k : SignExtension (Charge ι) splitCocycle,
      coefficientHom half half_add_half (e * etaQ g.charge h.charge k.charge) + d₂ B g h k =
        coefficientHom half half_add_half (e' * etaQ g.charge h.charge k.charge) + d₂ B' g h k) :
    e = e' := by
  have bit : ∀ x : F₂, x = 0 ∨ x = 1 := by decide +kernel
  rcases bit e with rfl | rfl <;> rcases bit e' with rfl | rfl
  · rfl
  · exfalso
    apply etaQ_not_coboundary a b hab half half_add_half half_ne_zero (fun g h => B g h - B' g h)
    intro g h k
    have h := heq g h k
    simp only [zero_mul, one_mul, map_zero, zero_add, d₂] at h ⊢
    linear_combination (norm := abel) h
  · exfalso
    apply etaQ_not_coboundary a b hab half half_add_half half_ne_zero (fun g h => B' g h - B g h)
    intro g h k
    have h := heq g h k
    simp only [zero_mul, one_mul, map_zero, zero_add, d₂] at h ⊢
    linear_combination (norm := abel) -h
  · rfl

/-- The two candidates selected by the involution tests on the split sign
extension are distinct, and the normalized cocycle determines a unique bit. -/
theorem unique_candidate_after_involution_tests {ι : Type} [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    (f : ChargeGroup ι → ChargeGroup ι → ChargeGroup ι → CircleCoefficients)
    (hf : ∀ a b d t, d₃ f a b d t = 0) (hn : Normalized f)
    (hcyc : ∀ z : SignExtension (Charge ι) splitCocycle, z ≠ 1 → z * z = 1 →
      ∃ B : Subgroup.zpowers z → Subgroup.zpowers z → CircleCoefficients,
        ∀ g h k : Subgroup.zpowers z,
          d₂ B g h k = f (Multiplicative.ofAdd g.val.charge)
            (Multiplicative.ofAdd h.val.charge) (Multiplicative.ofAdd k.val.charge)) :
    ∃! e : F₂, ∃ B, ∀ g h k : SignExtension (Charge ι) splitCocycle,
      f (Multiplicative.ofAdd g.charge) (Multiplicative.ofAdd h.charge)
        (Multiplicative.ofAdd k.charge) =
        coefficientHom half half_add_half (e * etaQ g.charge h.charge k.charge) + d₂ B g h k := by
  obtain ⟨e, B, hB⟩ := circle_inflation_has_two_candidates splitCocycle (fun _ => rfl) f hf hn hcyc
  obtain ⟨a, b, hab⟩ := exists_pair_ne ι
  refine ⟨e, ⟨B, hB⟩, ?_⟩
  rintro e' ⟨B', hB'⟩
  exact candidate_index_unique a b hab e' e B' B (fun g h k =>
    (hB' g h k).symm.trans (hB g h k))

#print axioms unique_candidate_after_involution_tests

end D5.S3.HomologicalAlgebra.QuaternionCandidateRestriction

/- GID: D5/S3/Observer/Dynamics/NonseparatingTwistStabilizerRefutation
   generality: G
   mirror-B: D5/B/S3/Observer/Dynamics/NonseparatingTwistStabilizerRefutation
   mirror-E: none(waiver:explicit-surface-epimorphism)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Observer/Dynamics/NonseparatingTwistStabilizerRefutation.claim; result=D5/S3/Observer/Dynamics/NonseparatingTwistStabilizerRefutation.result; claim=D5/S3/Observer/Dynamics/NonseparatingTwistStabilizerRefutation.claim
   digest: An epimorphism of the actual genus-two presentation to D8 is fixed up to one common conjugation by a nonseparating transvection whose curve image is nontrivial. -/

import D5.S3.Observer.Dynamics.SurfaceTwistCongruence

/-!
Source: Banerjee, Math. Ann. 392 (2025), 5045-5064,
DOI 10.1007/s00208-025-03213-7, Definition 1 and Proposition 3.
The claim is its genus-two geometric-basis consequence, with arbitrary target
group and a surjective homomorphism. Source topology is matched in Library;
this module constructs the presented-group automorphism, not a topological
surface or a Dehn-Nielsen-Baer equivalence. The original separating twist is
not substituted for the nonseparating transvection used here.

The nonseparating generator action is a->a, b->ba, c->c, d->d. Its inverse
is constructed from b->ba^-1. The D8 witness is (r^2,s,r,1), with one common
conjugator r. Equality up to conjugation is not replaced by pointwise equality.

This source is a candidate proof script, not an executed Lean or admission
receipt. The utility field describes the intended refutation route; no
independent escape/admission classification or freezing is asserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Observer.Dynamics.NonseparatingTwistStabilizerRefutation
open D5.S3.Observer.Dynamics.SurfaceTwistCongruence

private abbrev Pi := Surface 0
private abbrev Gen := Generator 0

private def twistImages (n : ℤ) : Gen → Pi
  | Sum.inl i => if i = 1 then
      generator 0 (Sum.inl 1) * generator 0 (Sum.inl 0) ^ n
    else generator 0 (Sum.inl i)
  | Sum.inr i => Fin.elim0 i.1

/-- The signed nonseparating transvection descends through the surface relator. -/
private def signedTwist (n : ℤ) : Pi →* Pi := by
  apply PresentedGroup.toGroup (f := twistImages n)
  intro w hw
  rcases Set.mem_singleton_iff.mp hw with rfl
  have hrel := PresentedGroup.one_of_mem
    (rels := ({surfaceRelator 0} : Set (FreeGroup Gen)))
    (show surfaceRelator 0 ∈ ({surfaceRelator 0} : Set (FreeGroup Gen)) by simp)
  have hc : bracket (generator 0 (Sum.inl 0)) (generator 0 (Sum.inl 1)) *
      bracket (generator 0 (Sum.inl 2)) (generator 0 (Sum.inl 3)) = 1 := by
    change PresentedGroup.mk ({surfaceRelator 0} : Set (FreeGroup Gen))
      (bracket (FreeGroup.of (Sum.inl 0)) (FreeGroup.of (Sum.inl 1)) *
        bracket (FreeGroup.of (Sum.inl 2)) (FreeGroup.of (Sum.inl 3)) * extraWord 0) = 1 at hrel
    simpa [extraWord, bracket, generator, PresentedGroup.of, map_mul, map_inv] using hrel
  simpa [surfaceRelator, extraWord, bracket, twistImages] using
    (show bracket (generator 0 (Sum.inl 0))
        (generator 0 (Sum.inl 1) * generator 0 (Sum.inl 0) ^ n) *
        bracket (generator 0 (Sum.inl 2)) (generator 0 (Sum.inl 3)) = 1 from by
      calc
        _ = bracket (generator 0 (Sum.inl 0)) (generator 0 (Sum.inl 1)) *
              bracket (generator 0 (Sum.inl 2)) (generator 0 (Sum.inl 3)) := by
                dsimp [bracket]
                group
        _ = 1 := hc)

/-- The actual invertible presentation map, including its inverse. -/
private def twist : Pi ≃* Pi := by
  have hg : ∀ n i, signedTwist n (generator 0 i) = twistImages n i := by
    intro n i
    exact PresentedGroup.toGroup.of _
  have hinv : ∀ n : ℤ, (signedTwist (-n)).comp (signedTwist n) = MonoidHom.id Pi := by
    intro n
    apply PresentedGroup.ext
    intro i
    change signedTwist (-n) (signedTwist n (generator 0 i)) = generator 0 i
    rw [hg]
    rcases i with i | i
    · fin_cases i <;> simp [twistImages, map_mul, map_zpow, hg] <;> group
    · exact Fin.elim0 i.1
  exact
    { toFun := signedTwist 1
      invFun := signedTwist (-1)
      left_inv := fun x => congrArg (fun f : Pi →* Pi => f x) (hinv 1)
      right_inv := fun x => by
        simpa using congrArg (fun f : Pi →* Pi => f x) (hinv (-1))
      map_mul' := (signedTwist 1).map_mul }

/-- The genus-two algebraic consequence of the published universal equivalence. -/
def claim : Prop :=
  ∀ (F : Type) [Group F] (φ : Pi →* F), Function.Surjective φ →
    ((∃ z : F, ∀ x : Pi, φ (twist x) = z * φ x * z⁻¹) ↔
      φ (generator 0 (Sum.inl 0)) = 1)

/-- Negation of the complete specialized claim. The target has order eight;
the source remains the infinite genus-two presentation throughout the proof. -/
theorem result : ¬ claim := by
  intro hclaim
  let images : Gen → DihedralGroup 4 := fun i =>
    match i with
    | Sum.inl j => ![DihedralGroup.r 2, DihedralGroup.sr 0, DihedralGroup.r 1, 1] j
    | Sum.inr j => Fin.elim0 j.1
  have hrel : ∀ w ∈ ({surfaceRelator 0} : Set (FreeGroup Gen)),
      FreeGroup.lift images w = 1 := by
    intro w hw
    rcases Set.mem_singleton_iff.mp hw with rfl
    norm_num [surfaceRelator, extraWord, bracket, images] <;> decide
  let φ : Pi →* DihedralGroup 4 := PresentedGroup.toGroup hrel
  have hg : ∀ i, φ (generator 0 i) = images i := by
    intro i
    exact PresentedGroup.toGroup.of _
  have hrot : ∀ t : ZMod 4, ∃ x : Pi, φ x = DihedralGroup.r t := by
    intro t
    refine ⟨generator 0 (Sum.inl 2) ^ t.val, ?_⟩
    rw [map_pow, hg]
    change (DihedralGroup.r 1 : DihedralGroup 4) ^ t.val = DihedralGroup.r t
    rw [DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]
  have hsurj : Function.Surjective φ := by
    rintro (t | t)
    · exact hrot t
    · obtain ⟨x, hx⟩ := hrot t
      refine ⟨generator 0 (Sum.inl 1) * x, ?_⟩
      rw [map_mul, hg, hx]
      simp [images]
  let conjPhi : Pi →* DihedralGroup 4 :=
    { toFun := fun x => DihedralGroup.r 1 * φ x * (DihedralGroup.r 1)⁻¹
      map_one' := by simp
      map_mul' := by intro x y; rw [map_mul]; group }
  have ht : ∀ i, signedTwist 1 (generator 0 i) = twistImages 1 i := by
    intro i
    exact PresentedGroup.toGroup.of _
  have hwhole : φ.comp (signedTwist 1) = conjPhi := by
    apply PresentedGroup.ext
    intro i
    change φ (signedTwist 1 (generator 0 i)) =
      DihedralGroup.r 1 * φ (generator 0 i) * (DihedralGroup.r 1)⁻¹
    rw [ht]
    rcases i with i | i
    · fin_cases i <;> norm_num [twistImages, map_mul, map_zpow, hg, images] <;> decide
    · exact Fin.elim0 i.1
  have hfixed : ∃ z : DihedralGroup 4, ∀ x : Pi, φ (twist x) = z * φ x * z⁻¹ := by
    refine ⟨DihedralGroup.r 1, ?_⟩
    intro x
    change φ (signedTwist 1 x) = _
    exact congrArg (fun f : Pi →* DihedralGroup 4 => f x) hwhole
  have hbad := (hclaim (DihedralGroup 4) φ hsurj).mp hfixed
  rw [hg] at hbad
  change DihedralGroup.r (2 : ZMod 4) = DihedralGroup.r 0 at hbad
  have hzero := DihedralGroup.r.inj hbad
  exact (by decide : (2 : ZMod 4) ≠ 0) hzero

#print axioms result
end D5.S3.Observer.Dynamics.NonseparatingTwistStabilizerRefutation

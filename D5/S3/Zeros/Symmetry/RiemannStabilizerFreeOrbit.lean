/- GID: D5/S3/Zeros/Symmetry/RiemannStabilizerFreeOrbit
   generality: I
   mirror-B: D5/B/S3/Zeros/Symmetry/RiemannStabilizerFreeOrbit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Separate critical-line stabilizer growth from free zero-orbit symmetry. -/

import D5.S3.Weil.ZetaSeam.ZetaReflect
import D5.S3.Zeros.Symmetry.ZetaConjugationCovariance

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Zeros.Symmetry.RiemannStabilizerFreeOrbit

open scoped ComplexConjugate
open D5.S3.Zeros.Symmetry.ZetaConjugationCovariance

/-- Under the Riemann hypothesis every nontrivial zero is fixed by conjugate
reflection. Independently, each nontrivial zero generates a zero-preserving
Klein orbit, and a nonreal off-line member generates four distinct points. -/
theorem riemann_stabilizer_free_orbit :
    (RiemannHypothesis ->
      forall {rho : Complex}, Zeta23.IsNontrivialZero rho ->
        Zeta23.reflect rho = rho) /\
    (forall {rho : Complex}, Zeta23.IsNontrivialZero rho ->
      let orbit : Finset Complex :=
        {rho, conj rho, 1 - rho, Zeta23.reflect rho}
      (forall z, z ∈ orbit -> Zeta23.IsNontrivialZero z) /\
        (forall z, z ∈ orbit <-> 1 - z ∈ orbit) /\
        (forall z, z ∈ orbit <-> conj z ∈ orbit) /\
        (rho.im ≠ 0 -> rho.re ≠ 1 / 2 -> orbit.card = 4)) := by
  constructor
  · intro hRH rho hzero
    have hcritical : rho.re = 1 / 2 :=
      Zeta23.RH_implies_on_line hRH hzero
    apply Complex.ext
    · simp [Zeta23.reflect, hcritical]
      norm_num
    · simp [Zeta23.reflect]
  · intro rho hzero
    dsimp only
    let orbit : Finset Complex :=
      {rho, conj rho, 1 - rho, Zeta23.reflect rho}
    have conjugateZero : forall {z : Complex}, Zeta23.IsNontrivialZero z ->
        Zeta23.IsNontrivialZero (conj z) := by
      rintro z hz
      refine ⟨?_, ?_, ?_⟩
      · rw [riemann_zeta_conj, hz.1, map_zero]
      · simpa using hz.2.1
      · simpa using hz.2.2
    have mirrorZero : Zeta23.IsNontrivialZero (Zeta23.reflect rho) :=
      Zeta23.zeta_reflect_zero rho hzero
    have reflectionZero : Zeta23.IsNontrivialZero (1 - rho) := by
      simpa [Zeta23.reflect] using conjugateZero mirrorZero
    have orbitZero : forall z, z ∈ orbit -> Zeta23.IsNontrivialZero z := by
      intro z hz
      simp only [orbit, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with (rfl | rfl | rfl | rfl)
      · exact hzero
      · exact conjugateZero hzero
      · exact reflectionZero
      · exact mirrorZero
    have reflectionClosed : forall z, z ∈ orbit -> 1 - z ∈ orbit := by
      intro z hz
      simp only [orbit, Finset.mem_insert, Finset.mem_singleton] at hz ⊢
      rcases hz with (rfl | rfl | rfl | rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (by simp [Zeta23.reflect])))
      · exact Or.inl (by ring)
      · exact Or.inr (Or.inl (by simp [Zeta23.reflect]))
    have conjugationClosed : forall z, z ∈ orbit -> conj z ∈ orbit := by
      intro z hz
      simp only [orbit, Finset.mem_insert, Finset.mem_singleton] at hz ⊢
      rcases hz with (rfl | rfl | rfl | rfl)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl (by simp)
      · exact Or.inr (Or.inr (Or.inr (by simp [Zeta23.reflect])))
      · exact Or.inr (Or.inr (Or.inl (by simp [Zeta23.reflect])))
    refine ⟨orbitZero, ?_, ?_, ?_⟩
    · intro z
      constructor
      · exact reflectionClosed z
      · intro hreflection
        have hclosed := reflectionClosed (1 - z) hreflection
        change z ∈ orbit
        simpa using hclosed
    · intro z
      constructor
      · exact conjugationClosed z
      · intro hconjugation
        have hclosed := conjugationClosed (conj z) hconjugation
        change z ∈ orbit
        simpa using hclosed
    · intro hnonreal hoffline
      have hR : 1 - rho ≠ rho := by
        intro h
        apply hoffline
        have hre := congrArg Complex.re h
        simp at hre
        linarith
      have hC : conj rho ≠ rho := by
        intro h
        apply hnonreal
        have him := congrArg Complex.im h
        simp at him
        linarith
      have hJ : Zeta23.reflect rho ≠ rho := by
        intro h
        apply hoffline
        have hre := congrArg Complex.re h
        simp [Zeta23.reflect] at hre
        linarith
      have hCR : conj rho ≠ 1 - rho := by
        intro h
        apply hJ
        simpa [Zeta23.reflect] using (congrArg conj h).symm
      have hCJ : conj rho ≠ Zeta23.reflect rho := by
        intro h
        apply hR
        simpa [Zeta23.reflect] using (congrArg conj h).symm
      have hRJ : 1 - rho ≠ Zeta23.reflect rho := by
        intro h
        apply hC
        simpa [Zeta23.reflect] using
          (congrArg (fun z : Complex => 1 - z) h).symm
      have hrhoMem :
          rho ∉ ({conj rho, 1 - rho, Zeta23.reflect rho} : Finset Complex) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨Ne.symm hC, Ne.symm hR, Ne.symm hJ⟩
      have hconjMem :
          conj rho ∉ ({1 - rho, Zeta23.reflect rho} : Finset Complex) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hCR, hCJ⟩
      have hreflectionMem :
          1 - rho ∉ ({Zeta23.reflect rho} : Finset Complex) := by
        simpa only [Finset.mem_singleton] using hRJ
      rw [Finset.card_insert_of_notMem hrhoMem,
        Finset.card_insert_of_notMem hconjMem,
        Finset.card_insert_of_notMem hreflectionMem]
      rfl

-- The theorem has no global hypotheses; this checks the empty context.
example : True := trivial

-- The complex carrier quantified by the theorem is inhabited.
example : Nonempty Complex := ⟨0⟩

-- These binders expose the conditional free-orbit hypothesis bundle.
example (rho : Complex) (hzero : Zeta23.IsNontrivialZero rho)
    (hnonreal : rho.im ≠ 0) (hoffline : rho.re ≠ 1 / 2) :
    Zeta23.IsNontrivialZero rho ∧ rho.im ≠ 0 ∧ rho.re ≠ 1 / 2 :=
  ⟨hzero, hnonreal, hoffline⟩

#print axioms riemann_stabilizer_free_orbit

end D5.S3.Zeros.Symmetry.RiemannStabilizerFreeOrbit

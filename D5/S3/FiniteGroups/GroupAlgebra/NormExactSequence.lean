/- GID: D5/S3/FiniteGroups/GroupAlgebra/NormExactSequence
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/NormExactSequence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RepresentationTheory.Coinvariants]
   utility: none
   digest: Native coinvariant norm bijectivity is extension-closed along an equivariant short exact sequence. -/

import D5.S3.FiniteGroups.GroupAlgebra.SemilinearKernelNorm

/-!
The actual unnormalized native coinvariant norm is extension-closed along a
short exact sequence of arbitrary representations. The proof lifts a norm
preimage at the quotient, uses the lifted difference-span exactness, and then
uses the kernel norm hypothesis. It makes no coefficient splitting or
projectivity choice, and does not assert extension closure for a trace-one
endomorphism.
-/

set_option autoImplicit false

universe uR uG uA uB uC

namespace D5.S3.FiniteGroups.GroupAlgebra.NormExactSequence

open Representation
open D5.S3.FiniteGroups.GroupAlgebra.SemilinearKernelNorm

variable {R : Type uR} {G : Type uG}
  {A : Type uA} {B : Type uB} {C : Type uC}
  [CommRing R] [Group G] [Fintype G]
  [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]
  {α : Representation R G A} {β : Representation R G B}
  {γ : Representation R G C}

/-- The actual finite-sum norm commutes with every native equivariant linear map. -/
theorem intertwiningMap_norm (f : IntertwiningMap α β) (a : A) :
    f (α.norm a) = β.norm (f a) := by
  classical
  simp only [Representation.norm, LinearMap.sum_apply, map_sum, f.isIntertwining]

/-- Equivariance sends the actual difference-span into the target difference-span. -/
theorem coinvariants_ker_map_le (f : IntertwiningMap α β) :
    (Coinvariants.ker α).map f.toLinearMap ≤ Coinvariants.ker β := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
  apply (Coinvariants.mk_eq_zero β).mp
  calc
    Coinvariants.mk β (f x) =
        Coinvariants.map α β f (Coinvariants.mk α x) :=
      (Coinvariants.map_mk f x).symm
    _ = 0 := by
      rw [(Coinvariants.mk_eq_zero α).mpr hx, map_zero]

/-- A surjective equivariant linear map covers the whole target difference-span.
The reverse inclusion lifts each generator, then uses the native span universal property. -/
theorem coinvariants_ker_map_eq_of_surjective
    (f : IntertwiningMap α β) (hf : Function.Surjective f) :
    (Coinvariants.ker α).map f.toLinearMap = Coinvariants.ker β := by
  apply le_antisymm (coinvariants_ker_map_le f)
  change Submodule.span R
      (Set.range fun gv : G × B => β gv.1 gv.2 - gv.2) ≤
    (Coinvariants.ker α).map f.toLinearMap
  apply Submodule.span_le.mpr
  rintro y ⟨⟨g, b⟩, rfl⟩
  obtain ⟨a, ha⟩ := hf b
  apply Submodule.mem_map.mpr
  refine ⟨α g a - a, Coinvariants.sub_mem_ker g a, ?_⟩
  change f (α g a - a) = β g b - b
  rw [map_sub, f.isIntertwining, ha]

/-- In a short exact sequence of representations, bijectivity of the actual
unnormalized coinvariant norms at both ends implies bijectivity in the middle.
The five type universes are independent. The group may be nonabelian and the
commutative coefficient ring is arbitrary; no module splitting is assumed. -/
theorem coinvariantsNorm_bijective_of_shortExact
    (i : IntertwiningMap α β) (q : IntertwiningMap β γ)
    (hi : Function.Injective i) (hq : Function.Surjective q)
    (hexact : LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap)
    (hα : Function.Bijective (coinvariantsNorm α))
    (hγ : Function.Bijective (coinvariantsNorm γ)) :
    Function.Bijective (coinvariantsNorm β) := by
  classical
  -- First recover the actual kernel statement on representatives in B.
  have hkerB (b : B) (hb : β.norm b = 0) : b ∈ Coinvariants.ker β := by
    have hqnorm : γ.norm (q b) = 0 := by
      rw [← intertwiningMap_norm q b, hb, map_zero]
    have hqmk : Coinvariants.mk γ (q b) = 0 := by
      apply hγ.1
      apply Subtype.ext
      simpa using hqnorm
    have hqDelta : q b ∈ (Coinvariants.ker β).map q.toLinearMap := by
      rw [coinvariants_ker_map_eq_of_surjective q hq]
      exact (Coinvariants.mk_eq_zero γ).mp hqmk
    obtain ⟨z, hz, hqz⟩ := Submodule.mem_map.mp hqDelta
    change q z = q b at hqz
    have hqdiff : q (b - z) = 0 := by
      rw [map_sub, hqz, sub_self]
    have hdiffRange : b - z ∈ LinearMap.range i.toLinearMap := by
      rw [hexact]
      exact LinearMap.mem_ker.mpr hqdiff
    obtain ⟨a, ha⟩ := LinearMap.mem_range.mp hdiffRange
    change i a = b - z at ha
    -- Norm kills z because it factors through this very quotient.
    have hzbar : coinvariantsNorm β (Coinvariants.mk β z) = 0 := by
      rw [(Coinvariants.mk_eq_zero β).mpr hz, map_zero]
    have hzN : β.norm z = 0 := by
      simpa using
        congrArg (fun w : β.invariants => (w : B)) hzbar
    have haN : α.norm a = 0 := by
      apply hi
      calc
        i (α.norm a) = β.norm (i a) := intertwiningMap_norm i a
        _ = β.norm (b - z) := congrArg β.norm ha
        _ = 0 := by rw [map_sub, hb, hzN, sub_self]
        _ = i 0 := (map_zero i).symm
    have hamk : Coinvariants.mk α a = 0 := by
      apply hα.1
      apply Subtype.ext
      simpa using haN
    have haDelta : a ∈ Coinvariants.ker α :=
      (Coinvariants.mk_eq_zero α).mp hamk
    have hiaDelta : i a ∈ Coinvariants.ker β :=
      coinvariants_ker_map_le i (Submodule.mem_map.mpr ⟨a, haDelta, rfl⟩)
    rw [ha] at hiaDelta
    have hsum := (Coinvariants.ker β).add_mem hiaDelta hz
    simpa only [sub_add_cancel] using hsum
  constructor
  · -- Apply the representative kernel statement to the difference of two classes.
    intro x y hxy
    obtain ⟨b, hb⟩ := Coinvariants.mk_surjective β (x - y)
    have hbar : coinvariantsNorm β (Coinvariants.mk β b) = 0 := by
      rw [hb, map_sub, hxy, sub_self]
    have hNb : β.norm b = 0 := by
      simpa using
        congrArg (fun w : β.invariants => (w : B)) hbar
    apply sub_eq_zero.mp
    calc
      x - y = Coinvariants.mk β b := hb.symm
      _ = 0 := (Coinvariants.mk_eq_zero β).mpr (hkerB b hNb)
  · -- Lift a norm preimage in C, rather than an invariant value in C.
    intro b
    have hqfixed : q (b : B) ∈ γ.invariants := by
      apply (mem_invariants γ _).mpr
      intro g
      calc
        γ g (q (b : B)) = q (β g (b : B)) :=
          (Representation.IntertwiningMap.isIntertwining β γ q g (b : B)).symm
        _ = q (b : B) :=
          congrArg q ((mem_invariants β (b : B)).mp b.property g)
    let c : γ.invariants := ⟨q (b : B), hqfixed⟩
    obtain ⟨cbar, hcbar⟩ := hγ.2 c
    obtain ⟨c0, hc0⟩ := Coinvariants.mk_surjective γ cbar
    have hNc0 : γ.norm c0 = q (b : B) := by
      have h : coinvariantsNorm γ (Coinvariants.mk γ c0) = c := by
        rw [hc0]
        exact hcbar
      simpa only [coinvariantsNorm_mk] using
        congrArg (fun w : γ.invariants => (w : C)) h
    obtain ⟨b0, hb0⟩ := hq c0
    have hqdiff : q ((b : B) - β.norm b0) = 0 := by
      rw [map_sub, intertwiningMap_norm q b0, hb0, hNc0, sub_self]
    have hdiffRange : (b : B) - β.norm b0 ∈ LinearMap.range i.toLinearMap := by
      rw [hexact]
      exact LinearMap.mem_ker.mpr hqdiff
    obtain ⟨a, ha⟩ := LinearMap.mem_range.mp hdiffRange
    change i a = (b : B) - β.norm b0 at ha
    have hafixed : a ∈ α.invariants := by
      apply (mem_invariants α a).mpr
      intro g
      apply hi
      calc
        i (α g a) = β g (i a) :=
          Representation.IntertwiningMap.isIntertwining α β i g a
        _ = β g ((b : B) - β.norm b0) := congrArg (β g) ha
        _ = (b : B) - β.norm b0 := by
          rw [map_sub, (mem_invariants β (b : B)).mp b.property g,
            self_norm_apply β g b0]
        _ = i a := ha.symm
    let afixed : α.invariants := ⟨a, hafixed⟩
    obtain ⟨abar, habar⟩ := hα.2 afixed
    obtain ⟨a0, ha0⟩ := Coinvariants.mk_surjective α abar
    have hNa0 : α.norm a0 = a := by
      have h : coinvariantsNorm α (Coinvariants.mk α a0) = afixed := by
        rw [ha0]
        exact habar
      simpa only [coinvariantsNorm_mk] using
        congrArg (fun w : α.invariants => (w : A)) h
    refine ⟨Coinvariants.mk β (b0 + i a0), ?_⟩
    apply Subtype.ext
    simp only [coinvariantsNorm_mk]
    calc
      β.norm (b0 + i a0) = β.norm b0 + i (α.norm a0) := by
        rw [map_add, ← intertwiningMap_norm i a0]
      _ = β.norm b0 + i a := by rw [hNa0]
      _ = i a + β.norm b0 := add_comm _ _
      _ = (b : B) := (eq_sub_iff_add_eq).mp ha

end D5.S3.FiniteGroups.GroupAlgebra.NormExactSequence

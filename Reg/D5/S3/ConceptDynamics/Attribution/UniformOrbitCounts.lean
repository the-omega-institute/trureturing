import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Attribution.UniformOrbitCounts
import Reg.Support.DependentFamily

/-! Translating the event tests changes the integer count equations. -/

namespace Reg.D5.S3.ConceptDynamics.Attribution.UniformOrbitCounts

open Finset
open _root_.D5.S3.ConceptDynamics.Attribution.UniformOrbitCounts
open _root_.D5.S3.ConceptDynamics.Attribution.UniformTableCalibration (Orbit orbit orbitCount)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u v w

noncomputable section

abbrev signature : Signature where
  Params := Σ T : Type v, Fintype T
  State T := Finset T.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ T := Finset T.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize signature (fun _ _ A => A) (fun e => nomatch e)

def full : Realization signature.{v} :=
  realize signature (fun _ T _ => @Finset.univ T.1 T.2) (fun e => nomatch e)

open Classical in
abbrev replicateArena : Arena where
  signature := signature.{v}
  Law R :=
    ∀ {G : Type u} {T : Type v} [Group G] [ft : Fintype T] [MulAction G T]
      [Fintype (Orbit G T)] (n : Orbit G T → ℕ),
      ∃ (S : Type v) (_ : Fintype S) (_ : MulAction G S) (f : S → T),
        (∀ (g : G) s, f (g • s) = g • f s) ∧
        (∀ (H : Subgroup G) s, (∀ h : H, (h : G) • s = s) ↔
          ∀ h : H, (h : G) • f s = f s) ∧
        ∀ A : Finset T, (∑ s : S, if f s ∈ A then (1 : ℕ) else 0) =
          ∑ o : Orbit G T, orbitCount (R.readout () ⟨T, ft⟩ A) o * n o

open Classical in
abbrev fiberArena : Arena where
  signature := signature.{v}
  Law R :=
    ∀ {G : Type u} {T : Type v} {S : Type w}
      [Group G] [ft : Fintype T] [MulAction G T] [Fintype (Orbit G T)]
      [Fintype S] [MulAction G S] (f : S → T),
      (∀ (g : G) s, f (g • s) = g • f s) →
      ∃ n : Orbit G T → ℕ, ∀ A : Finset T,
        (∑ s : S, if f s ∈ R.readout () ⟨T, ft⟩ A then (1 : ℕ) else 0) =
          ∑ o, orbitCount A o * n o

private theorem full_replicate_fails : ¬ replicateArena.{u,v}.Law full := by
  classical
  intro law
  let G := PUnit.{u+1}
  let T := PUnit.{v+1}
  letI : Group G := inferInstanceAs (Group PUnit)
  letI : MulAction G T := MulAction.trivial G T
  letI : Fintype T := inferInstanceAs (Fintype PUnit)
  letI : Fintype (Orbit G T) := Fintype.ofFinite _
  obtain ⟨S, _, _, f, _, _, counts⟩ := law (G := G) (T := T) (fun _ => 1)
  have impossible := counts ∅
  change (∑ s : S, if f s ∈ (∅ : Finset T) then 1 else 0) =
    ∑ o : Orbit G T, orbitCount univ o * 1 at impossible
  have positive : 0 < ∑ o : Orbit G T, orbitCount (univ : Finset T) o * 1 := by
    apply Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _ ) |>.mpr
    refine ⟨orbit (G := G) PUnit.unit, mem_univ _, ?_⟩
    rw [Nat.mul_one, orbitCount]
    exact Finset.card_pos.mpr ⟨PUnit.unit, mem_filter.mpr ⟨mem_univ _, rfl⟩⟩
  simp only [notMem_empty, ↓reduceIte, sum_const_zero] at impossible
  exact positive.ne' impossible.symm

private theorem full_fibers_fail : ¬ fiberArena.{u,v,w}.Law full := by
  classical
  intro law
  let G := PUnit.{u+1}
  let T := PUnit.{v+1}
  let S := PUnit.{w+1}
  letI : Group G := inferInstanceAs (Group PUnit)
  letI : MulAction G T := MulAction.trivial G T
  letI : MulAction G S := MulAction.trivial G S
  letI : Fintype T := inferInstanceAs (Fintype PUnit)
  letI : Fintype S := inferInstanceAs (Fintype PUnit)
  letI : Fintype (Orbit G T) := Fintype.ofFinite _
  obtain ⟨n, counts⟩ := law (G := G) (S := S) (T := T) (fun _ => PUnit.unit) (fun _ _ => rfl)
  have impossible := counts ∅
  change (∑ _s : S, if PUnit.unit ∈ (univ : Finset T) then 1 else 0) =
    ∑ o : Orbit G T, orbitCount ∅ o * n o at impossible
  simp [orbitCount, S] at impossible

private theorem event_dependence : ∀ role : signature.{v}.Role,
    ∃ T : signature.{v}.Params, ∃ A B : signature.{v}.State T,
      actual.readout role T A ≠ actual.readout role T B := by
  intro _
  let T := PUnit.{v+1}
  refine ⟨⟨T, inferInstanceAs (Fintype PUnit)⟩, ∅, {PUnit.unit}, ?_⟩
  change (∅ : Finset T) ≠ {PUnit.unit}
  simp

def replicateFamily : Registration replicateArena.{u,v} (type_of% (@realize_orbit_copy_counts)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@realize_orbit_copy_counts, full, full_replicate_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨full, ?_, rfl, full_replicate_fails⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := event_dependence

def fiberFamily : Registration fiberArena.{u,v,w} (type_of% (@count_seed_fibers_by_orbit)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@count_seed_fibers_by_orbit, full, full_fibers_fail⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨full, ?_, rfl, full_fibers_fail⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := event_dependence

end
end Reg.D5.S3.ConceptDynamics.Attribution.UniformOrbitCounts

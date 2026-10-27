import D5.S3.QuadraticForms.EvolutionAlgebras.RationalHassePrinciple
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.QuadraticForms.EvolutionAlgebras.RationalHassePrinciple

open _root_.D5.S3.QuadraticForms.EvolutionAlgebras.RationalHassePrinciple
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Module

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- The complete source operands, including the common isomorphism and all its laws. -/
structure SourceState (n : ℕ) where
  μ : Product K V
  ν : Product K W
  b : Basis (Fin n) K V
  c : Basis (Fin n) K W
  hb : Natural μ b
  hc : Natural ν c
  hp : Perfect ν
  f : V ≃ₗ[K] W
  hf : ∀ x y, f (μ x y) = ν (f x) (f y)

abbrev signature : Signature where
  Params := ℕ
  State n := SourceState (K := K) (V := V) (W := W) n
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Fin n → Fin n → K
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization (signature (K := K) (V := V) (W := W)) :=
  realize signature (fun _ _ s i j => s.c.equivFun (s.f (s.b j)) i)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature (K := K) (V := V) (W := W)
  Law R := ∀ {n : ℕ} (μ : Product K V) (ν : Product K W)
    (b : Basis (Fin n) K V) (c : Basis (Fin n) K W)
    (hb : Natural μ b) (hc : Natural ν c) (hp : Perfect ν)
    (f : V ≃ₗ[K] W) (hf : ∀ x y, f (μ x y) = ν (f x) (f y)),
      ∃ σ : Equiv.Perm (Fin n), ∃ t : Fin n → K,
        (∀ i, t i ≠ 0) ∧
        (∀ i j, R.readout () n ⟨μ, ν, b, c, hb, hc, hp, f, hf⟩ i j =
          if σ i = j then t i else 0)

theorem actual_law : (arena (K := K) (V := V) (W := W)).Law actual := by
  intro n μ ν b c hb hc hp f hf
  exact isomorphism_monomial μ ν b c hb hc hp f hf

/-- The fixed-carrier arena cannot satisfy actual dependence for zero carriers.
A source registration for every carrier must place carriers in its parameter family. -/
theorem fixed_carrier_obstruction [Subsingleton W] :
    ¬ ObservationalDependence (signature (K := K) (V := V) (W := W)) actual := by
  intro h
  obtain ⟨n, x, y, hxy⟩ := h ()
  have hn : n = 0 := by
    by_contra hn
    let i : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
    exact x.c.linearIndependent.ne_zero i (Subsingleton.elim _ _)
  subst n
  exact hxy (Subsingleton.elim _ _)

end Reg.D5.S3.QuadraticForms.EvolutionAlgebras.RationalHassePrinciple

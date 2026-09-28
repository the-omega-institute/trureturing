import D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier
import Reg.Support.DependentFamily
import Mathlib.Algebra.Ring.ULift
import Mathlib.Algebra.BigOperators.Fin

open _root_.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier

universe u v

abbrev chainZeroSignature : Signature where
  Params := Nat
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def chainZeroActual : Realization chainZeroSignature :=
  realize chainZeroSignature (fun _ L j => j + L) (fun e => nomatch e)

def chainZeroRejected : Realization chainZeroSignature :=
  realize chainZeroSignature (fun _ _ _ => 0) (fun e => nomatch e)

def chainZeroArena : Arena where
  signature := chainZeroSignature
  Law r := ∀ {R : Type u} [Semiring R] {n m : ℕ} {A : Mat R n n} {B : Mat R m m} {L : ℕ}
    (c : ExchangeChain R A B L), ∀ j : ℕ, B ^ j = 0 →
      A ^ (r.readout () L j) = 0

theorem chainZeroRejectedLaw : ¬ chainZeroArena.{u}.Law chainZeroRejected := by
  intro h
  let Z : Mat (ULift.{u} Nat) 1 1 := 0
  let c : ExchangeChain (ULift.{u} Nat) Z Z 0 := ExchangeChain.nil Z
  have hz := h c 1 (by simp [Z])
  have hentry := congrArg (fun M : Mat (ULift.{u} Nat) 1 1 => M 0 0) hz
  simp [Z, chainZeroRejected, realize] at hentry

def chainZeroRegistration : Registration chainZeroArena (chainZeroArena.Law chainZeroActual) where
  actual := chainZeroActual
  bridge := Iff.rfl
  variation := ⟨by
    intro R _ n m A B L c j hj
    simpa [chainZeroActual, realize] using chain_zero_power c j hj,
    chainZeroRejected, chainZeroRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨chainZeroRejected, ?_, rfl, chainZeroRejectedLaw⟩
      intro j hji
      cases i
      cases j
      exact (hji rfl).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨(0 : Nat), (0 : Nat), (1 : Nat), ?_⟩
    change (0 : Nat) ≠ 1
    exact Nat.zero_ne_one

register_information_theorem chain_zero_power in chainZeroArena
  readout via (realize chainZeroSignature (fun _ L j => j + L) (fun e => nomatch e))
  realizes chainZeroRegistration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier
    coordinates := #[6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "arg", "arg"]
      stateBinder := 8 }] })
  escape continues (open)

#print axioms chainZeroRegistration

abbrev chainDepthSignature : Signature where
  Params := Unit
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def chainDepthActual : Realization chainDepthSignature :=
  realize chainDepthSignature (fun _ _ a => a) (fun e => nomatch e)

def chainDepthRejected : Realization chainDepthSignature :=
  realize chainDepthSignature (fun _ _ a => a + 1) (fun e => nomatch e)

def chainDepthArena : Arena where
  signature := chainDepthSignature
  Law r := ∀ {R : Type u} [Semiring R] {n m : ℕ}
    {A : Mat R n n} {B : Mat R m m} {a b L : ℕ}
    (c : ExchangeChain R A B L) (ha : ExactDepth A a) (hb : ExactDepth B b),
    r.readout () () a ≤ b + L ∧ b ≤ a + L

theorem chainDepthRejectedLaw : ¬ chainDepthArena.{u}.Law chainDepthRejected := by
  intro h
  let Z : Mat (ULift.{u} Nat) 1 1 := 0
  let c : ExchangeChain (ULift.{u} Nat) Z Z 0 := ExchangeChain.nil Z
  have hz : ExactDepth Z 1 := by
    refine ⟨by decide, ?_, ?_⟩
    · simp [Z]
    · intro j hj hlt
      omega
  have hb := h c hz hz
  have hbad := hb.1
  norm_num [chainDepthRejected, realize] at hbad

def chainDepthRegistration : Registration chainDepthArena (chainDepthArena.Law chainDepthActual) where
  actual := chainDepthActual
  bridge := Iff.rfl
  variation := ⟨by
    intro R _ n m A B a b L c ha hb
    simpa [chainDepthActual, realize] using chain_depth_barrier c ha hb,
    chainDepthRejected, chainDepthRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨chainDepthRejected, ?_, rfl, chainDepthRejectedLaw⟩
      intro j hji
      cases i
      cases j
      exact (hji rfl).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨(), (0 : Nat), (1 : Nat), ?_⟩
    change (0 : Nat) ≠ 1
    exact Nat.zero_ne_one

register_information_theorem chain_depth_barrier in chainDepthArena
  readout via (realize chainDepthSignature (fun _ _ a => a) (fun e => nomatch e))
  realizes chainDepthRegistration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 6 }] })
  escape continues (open)

abbrev chainReverseSignature : Signature where
  Params := Nat
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def chainReverseActual : Realization chainReverseSignature :=
  realize chainReverseSignature (fun _ L j => j + L) (fun e => nomatch e)

def chainReverseRejected : Realization chainReverseSignature :=
  realize chainReverseSignature (fun _ _ _ => 0) (fun e => nomatch e)

def chainReverseArena : Arena where
  signature := chainReverseSignature
  Law r := ∀ {R : Type u} [Semiring R] {n m : ℕ} {A : Mat R n n} {B : Mat R m m} {L : ℕ}
    (c : ExchangeChain R A B L), ∀ j : ℕ, A ^ j = 0 →
      B ^ (r.readout () L j) = 0

theorem chainReverseRejectedLaw : ¬ chainReverseArena.{u}.Law chainReverseRejected := by
  intro h
  let Z : Mat (ULift.{u} Nat) 1 1 := 0
  let c : ExchangeChain (ULift.{u} Nat) Z Z 0 := ExchangeChain.nil Z
  have hz := h c 1 (by simp [Z])
  have hentry := congrArg (fun M : Mat (ULift.{u} Nat) 1 1 => M 0 0) hz
  simp [Z, chainReverseRejected, realize] at hentry

def chainReverseRegistration : Registration chainReverseArena (chainReverseArena.Law chainReverseActual) where
  actual := chainReverseActual
  bridge := Iff.rfl
  variation := ⟨by
    intro R _ n m A B L c j hj
    simpa [chainReverseActual, realize] using chain_zero_power_reverse c j hj,
    chainReverseRejected, chainReverseRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨chainReverseRejected, ?_, rfl, chainReverseRejectedLaw⟩
      intro j hji
      cases i
      cases j
      exact (hji rfl).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨(0 : Nat), (0 : Nat), (1 : Nat), ?_⟩
    change (0 : Nat) ≠ 1
    exact Nat.zero_ne_one

register_information_theorem chain_zero_power_reverse in chainReverseArena
  readout via (realize chainReverseSignature (fun _ L j => j + L) (fun e => nomatch e))
  realizes chainReverseRegistration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier
    coordinates := #[6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "arg", "arg"]
      stateBinder := 8 }] })
  escape continues (open)

abbrev rectangularSignature : Signature where
  Params := Unit
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def rectangularActual : Realization rectangularSignature :=
  realize rectangularSignature (fun _ _ j => j + 1) (fun e => nomatch e)

def rectangularRejected : Realization rectangularSignature :=
  realize rectangularSignature (fun _ _ _ => 0) (fun e => nomatch e)

def rectangularArena : Arena where
  signature := rectangularSignature
  Law r := ∀ {R : Type u} [Semiring R] {n m : ℕ}
    (U : Mat R n m) (V : Mat R m n) (j : ℕ),
    (U * V) ^ (r.readout () () j) = U * (V * U) ^ j * V

theorem rectangularRejectedLaw : ¬ rectangularArena.{u}.Law rectangularRejected := by
  intro h
  let Z : Mat (ULift.{u} Nat) 1 1 := 0
  have hz := h Z Z 0
  have hentry := congrArg (fun M : Mat (ULift.{u} Nat) 1 1 => M 0 0) hz
  simp [Z, rectangularRejected, realize] at hentry

def rectangularRegistration : Registration rectangularArena (rectangularArena.Law rectangularActual) where
  actual := rectangularActual
  bridge := Iff.rfl
  variation := ⟨by
    intro R _ n m U V j
    simpa [rectangularActual, realize] using rectangular_exchange_power U V j,
    rectangularRejected, rectangularRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rectangularRejected, ?_, rfl, rectangularRejectedLaw⟩
      intro j hji
      cases i
      cases j
      exact (hji rfl).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨(), (0 : Nat), (1 : Nat), ?_⟩
    change (1 : Nat) ≠ 2
    decide

register_information_theorem rectangular_exchange_power in rectangularArena
  readout via (realize rectangularSignature (fun _ _ j => j + 1) (fun e => nomatch e))
  realizes rectangularRegistration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 6 }] })
  escape continues (open)

abbrev mapSignature : Signature where
  Params := Unit
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def mapActual : Realization mapSignature :=
  realize mapSignature (fun _ _ L => L) (fun e => nomatch e)

def mapRejected : Realization mapSignature :=
  realize mapSignature (fun _ _ _ => 0) (fun e => nomatch e)

def mapArena : Arena where
  signature := mapSignature
  Law r := ∀ {R : Type u} {S : Type v} [Semiring R] [Semiring S]
    (f : R →ₙ+* S) {n m L : ℕ} {A : Mat R n n} {B : Mat R m m}
    (c : ExchangeChain R A B L),
    ExchangeChain S (A.map f) (B.map f) (r.readout () () L)

theorem mapRejectedLaw : ¬ mapArena.{u,v}.Law mapRejected := by
  intro h
  let R := ULift.{u} Nat
  let S := ULift.{v} Nat
  let f : R →ₙ+* S := {
    toFun := fun x => ⟨x.down⟩
    map_zero' := by rfl
    map_add' := by intro x y; rfl
    map_mul' := by intro x y; rfl }
  let U : Mat R 2 2 := Matrix.diagonal (fun i => if i = 0 then 1 else 0)
  let V : Mat R 2 2 := fun i j => if i = 0 ∧ j = 1 then 1 else 0
  let A : Mat R 2 2 := U * V
  let B : Mat R 2 2 := V * U
  let c : ExchangeChain R A B 1 := ExchangeChain.cons U V (ExchangeChain.nil B)
  have hc := h f c
  have chain_zero_eq {X Y : Mat S 2 2} (hxy : ExchangeChain S X Y 0) : X = Y := by
    cases hxy
    rfl
  have heq : A.map f = B.map f := chain_zero_eq hc
  have hentry := congrFun (congrFun heq (0 : Fin 2)) (1 : Fin 2)
  have hA : A 0 1 = (1 : R) := by
    change (Matrix.diagonal (fun i : Fin 2 => if i = 0 then (1 : ULift.{u} Nat) else 0) * V) 0 1 = 1
    rw [Matrix.diagonal_mul]
    simp [V]
  have hB : B 0 1 = (0 : R) := by
    change (V * Matrix.diagonal (fun i : Fin 2 => if i = 0 then (1 : ULift.{u} Nat) else 0)) 0 1 = 0
    rw [Matrix.mul_diagonal]
    simp [V]
  change f (A 0 1) = f (B 0 1) at hentry
  rw [hA, hB] at hentry
  have hdown := congrArg ULift.down hentry
  exact Nat.noConfusion hdown

def mapRegistration : Registration mapArena (mapArena.Law mapActual) where
  actual := mapActual
  bridge := Iff.rfl
  variation := ⟨by
    intro R S _ _ f n m L A B c
    simpa [mapActual, realize] using map_exchange_chain f c,
    mapRejected, mapRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨mapRejected, ?_, rfl, mapRejectedLaw⟩
      intro j hji
      cases i
      cases j
      exact (hji rfl).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨(), (0 : Nat), (1 : Nat), ?_⟩
    change (0 : Nat) ≠ 1
    exact Nat.zero_ne_one

register_information_theorem map_exchange_chain in mapArena
  readout via (realize mapSignature (fun _ _ L => L) (fun e => nomatch e))
  realizes mapRegistration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg"]
      stateBinder := 7 }] })
  escape continues (open)

end Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier

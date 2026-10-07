import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Multiset.Defs
import Mathlib.Data.Multiset.Pi
import Mathlib.Data.Multiset.ZeroCons
import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation

namespace Reg.Catalogs.InformationRoot.SealedCatalog
open LeanInformationAudit

noncomputable def state_34 : D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM :=
  { direction := D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.CausalDirection.xCausesY,
    root := fun a =>
      @Decidable.rec (@Eq Bool a Bool.true) (fun x => (fun a => Bool) a)
        (fun h =>
          @Decidable.rec (@Eq Bool a Bool.false) (fun x => (fun a => Bool) a)
            (fun h_1 =>
              False.rec
                (fun x =>
                  (fun a a_1 => (fun a => Bool) a) a
                    (@Multiset.Pi.cons._proof_1 Bool (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool))
                      Bool.false a
                      (@Multiset.Pi.cons._proof_1 Bool
                        (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.cons Bool Bool.false (@List.nil Bool)))
                        Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                      h_1))
                (@List.Mem.casesOn Bool a
                  (fun a_1 x =>
                    @Eq (List Bool) (@List.nil Bool) a_1 →
                      @HEq
                          (@Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
                            (@OfNat.ofNat (Multiset Bool) (nat_lit 0)
                              (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool)))
                            a)
                          (@Multiset.Pi.cons._proof_1 Bool
                            (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool)) Bool.false a
                            (@Multiset.Pi.cons._proof_1 Bool
                              (@Quotient.mk (List Bool) (List.isSetoid Bool)
                                (@List.cons Bool Bool.false (@List.nil Bool)))
                              Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                            h_1)
                          (@List.Mem Bool a a_1) x →
                        False)
                  (@List.nil Bool)
                  (@Multiset.Pi.cons._proof_1 Bool (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool))
                    Bool.false a
                    (@Multiset.Pi.cons._proof_1 Bool
                      (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.cons Bool Bool.false (@List.nil Bool)))
                      Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                    h_1)
                  (fun as h_2 =>
                    @False.elim
                      (@HEq
                          (@Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
                            (@OfNat.ofNat (Multiset Bool) (nat_lit 0)
                              (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool)))
                            a)
                          (@Multiset.Pi.cons._proof_1 Bool
                            (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool)) Bool.false a
                            (@Multiset.Pi.cons._proof_1 Bool
                              (@Quotient.mk (List Bool) (List.isSetoid Bool)
                                (@List.cons Bool Bool.false (@List.nil Bool)))
                              Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                            h_1)
                          (@List.Mem Bool a (@List.cons Bool a as)) (@List.Mem.head Bool a as) →
                        False)
                      (@noConfusion_of_Nat (List Bool) (@List.ctorIdx Bool) (@List.nil Bool) (@List.cons Bool a as) h_2))
                  (fun b {as} a_1 h_2 =>
                    @False.elim
                      (@HEq
                          (@Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
                            (@OfNat.ofNat (Multiset Bool) (nat_lit 0)
                              (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool)))
                            a)
                          (@Multiset.Pi.cons._proof_1 Bool
                            (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool)) Bool.false a
                            (@Multiset.Pi.cons._proof_1 Bool
                              (@Quotient.mk (List Bool) (List.isSetoid Bool)
                                (@List.cons Bool Bool.false (@List.nil Bool)))
                              Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                            h_1)
                          (@List.Mem Bool a (@List.cons Bool b as)) (@List.Mem.tail Bool a b as a_1) →
                        False)
                      (@noConfusion_of_Nat (List Bool) (@List.ctorIdx Bool) (@List.nil Bool) (@List.cons Bool b as) h_2))
                  (@Eq.refl (List Bool) (@List.nil Bool))
                  (@HEq.refl
                    (@Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
                      (@OfNat.ofNat (Multiset Bool) (nat_lit 0)
                        (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool)))
                      a)
                    (@Multiset.Pi.cons._proof_1 Bool (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool))
                      Bool.false a
                      (@Multiset.Pi.cons._proof_1 Bool
                        (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.cons Bool Bool.false (@List.nil Bool)))
                        Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                      h_1))))
            (fun h =>
              @Eq.rec Bool Bool.false (fun x x_1 => (fun a => Bool) x) Bool.false a (@Eq.symm Bool a Bool.false h))
            (@Bool.rec (fun x => (fun a b => Decidable (@Eq Bool a b)) x Bool.false)
              (@Decidable.isTrue (@Eq Bool Bool.false Bool.false) (@rfl Bool Bool.false))
              (@Decidable.isFalse (@Eq Bool Bool.true Bool.false) fun h => @Bool.noConfusion False Bool.true Bool.false h)
              a))
        (fun h => @Eq.rec Bool Bool.true (fun x x_1 => (fun a => Bool) x) Bool.true a (@Eq.symm Bool a Bool.true h))
        (@Bool.rec (fun x => (fun a b => Decidable (@Eq Bool a b)) x Bool.true)
          (@Decidable.isFalse (@Eq Bool Bool.false Bool.true) fun h => @Bool.noConfusion False Bool.false Bool.true h)
          (@Decidable.isTrue (@Eq Bool Bool.true Bool.true) (@rfl Bool Bool.true)) a),
    child := fun a =>
      @Decidable.rec (@Eq Bool a Bool.true) (fun x => (fun a => Bool) a)
        (fun h =>
          @Decidable.rec (@Eq Bool a Bool.false) (fun x => (fun a => Bool) a)
            (fun h_1 =>
              False.rec
                (fun x =>
                  (fun a a_1 => (fun a => Bool) a) a
                    (@Multiset.Pi.cons._proof_1 Bool (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool))
                      Bool.false a
                      (@Multiset.Pi.cons._proof_1 Bool
                        (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.cons Bool Bool.false (@List.nil Bool)))
                        Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                      h_1))
                (@List.Mem.casesOn Bool a
                  (fun a_1 x =>
                    @Eq (List Bool) (@List.nil Bool) a_1 →
                      @HEq
                          (@Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
                            (@OfNat.ofNat (Multiset Bool) (nat_lit 0)
                              (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool)))
                            a)
                          (@Multiset.Pi.cons._proof_1 Bool
                            (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool)) Bool.false a
                            (@Multiset.Pi.cons._proof_1 Bool
                              (@Quotient.mk (List Bool) (List.isSetoid Bool)
                                (@List.cons Bool Bool.false (@List.nil Bool)))
                              Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                            h_1)
                          (@List.Mem Bool a a_1) x →
                        False)
                  (@List.nil Bool)
                  (@Multiset.Pi.cons._proof_1 Bool (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool))
                    Bool.false a
                    (@Multiset.Pi.cons._proof_1 Bool
                      (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.cons Bool Bool.false (@List.nil Bool)))
                      Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                    h_1)
                  (fun as h_2 =>
                    @False.elim
                      (@HEq
                          (@Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
                            (@OfNat.ofNat (Multiset Bool) (nat_lit 0)
                              (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool)))
                            a)
                          (@Multiset.Pi.cons._proof_1 Bool
                            (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool)) Bool.false a
                            (@Multiset.Pi.cons._proof_1 Bool
                              (@Quotient.mk (List Bool) (List.isSetoid Bool)
                                (@List.cons Bool Bool.false (@List.nil Bool)))
                              Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                            h_1)
                          (@List.Mem Bool a (@List.cons Bool a as)) (@List.Mem.head Bool a as) →
                        False)
                      (@noConfusion_of_Nat (List Bool) (@List.ctorIdx Bool) (@List.nil Bool) (@List.cons Bool a as) h_2))
                  (fun b {as} a_1 h_2 =>
                    @False.elim
                      (@HEq
                          (@Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
                            (@OfNat.ofNat (Multiset Bool) (nat_lit 0)
                              (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool)))
                            a)
                          (@Multiset.Pi.cons._proof_1 Bool
                            (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool)) Bool.false a
                            (@Multiset.Pi.cons._proof_1 Bool
                              (@Quotient.mk (List Bool) (List.isSetoid Bool)
                                (@List.cons Bool Bool.false (@List.nil Bool)))
                              Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                            h_1)
                          (@List.Mem Bool a (@List.cons Bool b as)) (@List.Mem.tail Bool a b as a_1) →
                        False)
                      (@noConfusion_of_Nat (List Bool) (@List.ctorIdx Bool) (@List.nil Bool) (@List.cons Bool b as) h_2))
                  (@Eq.refl (List Bool) (@List.nil Bool))
                  (@HEq.refl
                    (@Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
                      (@OfNat.ofNat (Multiset Bool) (nat_lit 0)
                        (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool)))
                      a)
                    (@Multiset.Pi.cons._proof_1 Bool (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool))
                      Bool.false a
                      (@Multiset.Pi.cons._proof_1 Bool
                        (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.cons Bool Bool.false (@List.nil Bool)))
                        Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                      h_1))))
            (fun h =>
              @Eq.rec Bool Bool.false (fun x x_1 => (fun a => Bool) x) Bool.false a (@Eq.symm Bool a Bool.false h))
            (@Bool.rec (fun x => (fun a b => Decidable (@Eq Bool a b)) x Bool.false)
              (@Decidable.isTrue (@Eq Bool Bool.false Bool.false) (@rfl Bool Bool.false))
              (@Decidable.isFalse (@Eq Bool Bool.true Bool.false) fun h => @Bool.noConfusion False Bool.true Bool.false h)
              a))
        (fun h => @Eq.rec Bool Bool.true (fun x x_1 => (fun a => Bool) x) Bool.false a (@Eq.symm Bool a Bool.true h))
        (@Bool.rec (fun x => (fun a b => Decidable (@Eq Bool a b)) x Bool.true)
          (@Decidable.isFalse (@Eq Bool Bool.false Bool.true) fun h => @Bool.noConfusion False Bool.false Bool.true h)
          (@Decidable.isTrue (@Eq Bool Bool.true Bool.true) (@rfl Bool Bool.true)) a) }

noncomputable def state_35 : D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM :=
  { direction := D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.CausalDirection.xCausesY,
    root := fun a =>
      @Decidable.rec (@Eq Bool a Bool.true) (fun x => (fun a => Bool) a)
        (fun h =>
          @Decidable.rec (@Eq Bool a Bool.false) (fun x => (fun a => Bool) a)
            (fun h_1 =>
              False.rec
                (fun x =>
                  (fun a a_1 => (fun a => Bool) a) a
                    (@Multiset.Pi.cons._proof_1 Bool (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool))
                      Bool.false a
                      (@Multiset.Pi.cons._proof_1 Bool
                        (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.cons Bool Bool.false (@List.nil Bool)))
                        Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                      h_1))
                (@List.Mem.casesOn Bool a
                  (fun a_1 x =>
                    @Eq (List Bool) (@List.nil Bool) a_1 →
                      @HEq
                          (@Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
                            (@OfNat.ofNat (Multiset Bool) (nat_lit 0)
                              (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool)))
                            a)
                          (@Multiset.Pi.cons._proof_1 Bool
                            (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool)) Bool.false a
                            (@Multiset.Pi.cons._proof_1 Bool
                              (@Quotient.mk (List Bool) (List.isSetoid Bool)
                                (@List.cons Bool Bool.false (@List.nil Bool)))
                              Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                            h_1)
                          (@List.Mem Bool a a_1) x →
                        False)
                  (@List.nil Bool)
                  (@Multiset.Pi.cons._proof_1 Bool (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool))
                    Bool.false a
                    (@Multiset.Pi.cons._proof_1 Bool
                      (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.cons Bool Bool.false (@List.nil Bool)))
                      Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                    h_1)
                  (fun as h_2 =>
                    @False.elim
                      (@HEq
                          (@Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
                            (@OfNat.ofNat (Multiset Bool) (nat_lit 0)
                              (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool)))
                            a)
                          (@Multiset.Pi.cons._proof_1 Bool
                            (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool)) Bool.false a
                            (@Multiset.Pi.cons._proof_1 Bool
                              (@Quotient.mk (List Bool) (List.isSetoid Bool)
                                (@List.cons Bool Bool.false (@List.nil Bool)))
                              Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                            h_1)
                          (@List.Mem Bool a (@List.cons Bool a as)) (@List.Mem.head Bool a as) →
                        False)
                      (@noConfusion_of_Nat (List Bool) (@List.ctorIdx Bool) (@List.nil Bool) (@List.cons Bool a as) h_2))
                  (fun b {as} a_1 h_2 =>
                    @False.elim
                      (@HEq
                          (@Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
                            (@OfNat.ofNat (Multiset Bool) (nat_lit 0)
                              (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool)))
                            a)
                          (@Multiset.Pi.cons._proof_1 Bool
                            (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool)) Bool.false a
                            (@Multiset.Pi.cons._proof_1 Bool
                              (@Quotient.mk (List Bool) (List.isSetoid Bool)
                                (@List.cons Bool Bool.false (@List.nil Bool)))
                              Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                            h_1)
                          (@List.Mem Bool a (@List.cons Bool b as)) (@List.Mem.tail Bool a b as a_1) →
                        False)
                      (@noConfusion_of_Nat (List Bool) (@List.ctorIdx Bool) (@List.nil Bool) (@List.cons Bool b as) h_2))
                  (@Eq.refl (List Bool) (@List.nil Bool))
                  (@HEq.refl
                    (@Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
                      (@OfNat.ofNat (Multiset Bool) (nat_lit 0)
                        (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool)))
                      a)
                    (@Multiset.Pi.cons._proof_1 Bool (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool))
                      Bool.false a
                      (@Multiset.Pi.cons._proof_1 Bool
                        (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.cons Bool Bool.false (@List.nil Bool)))
                        Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                      h_1))))
            (fun h => @Eq.rec Bool Bool.false (fun x x_1 => (fun a => Bool) x) Bool.true a (@Eq.symm Bool a Bool.false h))
            (@Bool.rec (fun x => (fun a b => Decidable (@Eq Bool a b)) x Bool.false)
              (@Decidable.isTrue (@Eq Bool Bool.false Bool.false) (@rfl Bool Bool.false))
              (@Decidable.isFalse (@Eq Bool Bool.true Bool.false) fun h => @Bool.noConfusion False Bool.true Bool.false h)
              a))
        (fun h => @Eq.rec Bool Bool.true (fun x x_1 => (fun a => Bool) x) Bool.false a (@Eq.symm Bool a Bool.true h))
        (@Bool.rec (fun x => (fun a b => Decidable (@Eq Bool a b)) x Bool.true)
          (@Decidable.isFalse (@Eq Bool Bool.false Bool.true) fun h => @Bool.noConfusion False Bool.false Bool.true h)
          (@Decidable.isTrue (@Eq Bool Bool.true Bool.true) (@rfl Bool Bool.true)) a),
    child := fun a =>
      @Decidable.rec (@Eq Bool a Bool.true) (fun x => (fun a => Bool) a)
        (fun h =>
          @Decidable.rec (@Eq Bool a Bool.false) (fun x => (fun a => Bool) a)
            (fun h_1 =>
              False.rec
                (fun x =>
                  (fun a a_1 => (fun a => Bool) a) a
                    (@Multiset.Pi.cons._proof_1 Bool (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool))
                      Bool.false a
                      (@Multiset.Pi.cons._proof_1 Bool
                        (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.cons Bool Bool.false (@List.nil Bool)))
                        Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                      h_1))
                (@List.Mem.casesOn Bool a
                  (fun a_1 x =>
                    @Eq (List Bool) (@List.nil Bool) a_1 →
                      @HEq
                          (@Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
                            (@OfNat.ofNat (Multiset Bool) (nat_lit 0)
                              (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool)))
                            a)
                          (@Multiset.Pi.cons._proof_1 Bool
                            (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool)) Bool.false a
                            (@Multiset.Pi.cons._proof_1 Bool
                              (@Quotient.mk (List Bool) (List.isSetoid Bool)
                                (@List.cons Bool Bool.false (@List.nil Bool)))
                              Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                            h_1)
                          (@List.Mem Bool a a_1) x →
                        False)
                  (@List.nil Bool)
                  (@Multiset.Pi.cons._proof_1 Bool (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool))
                    Bool.false a
                    (@Multiset.Pi.cons._proof_1 Bool
                      (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.cons Bool Bool.false (@List.nil Bool)))
                      Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                    h_1)
                  (fun as h_2 =>
                    @False.elim
                      (@HEq
                          (@Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
                            (@OfNat.ofNat (Multiset Bool) (nat_lit 0)
                              (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool)))
                            a)
                          (@Multiset.Pi.cons._proof_1 Bool
                            (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool)) Bool.false a
                            (@Multiset.Pi.cons._proof_1 Bool
                              (@Quotient.mk (List Bool) (List.isSetoid Bool)
                                (@List.cons Bool Bool.false (@List.nil Bool)))
                              Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                            h_1)
                          (@List.Mem Bool a (@List.cons Bool a as)) (@List.Mem.head Bool a as) →
                        False)
                      (@noConfusion_of_Nat (List Bool) (@List.ctorIdx Bool) (@List.nil Bool) (@List.cons Bool a as) h_2))
                  (fun b {as} a_1 h_2 =>
                    @False.elim
                      (@HEq
                          (@Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
                            (@OfNat.ofNat (Multiset Bool) (nat_lit 0)
                              (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool)))
                            a)
                          (@Multiset.Pi.cons._proof_1 Bool
                            (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool)) Bool.false a
                            (@Multiset.Pi.cons._proof_1 Bool
                              (@Quotient.mk (List Bool) (List.isSetoid Bool)
                                (@List.cons Bool Bool.false (@List.nil Bool)))
                              Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                            h_1)
                          (@List.Mem Bool a (@List.cons Bool b as)) (@List.Mem.tail Bool a b as a_1) →
                        False)
                      (@noConfusion_of_Nat (List Bool) (@List.ctorIdx Bool) (@List.nil Bool) (@List.cons Bool b as) h_2))
                  (@Eq.refl (List Bool) (@List.nil Bool))
                  (@HEq.refl
                    (@Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
                      (@OfNat.ofNat (Multiset Bool) (nat_lit 0)
                        (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool)))
                      a)
                    (@Multiset.Pi.cons._proof_1 Bool (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool))
                      Bool.false a
                      (@Multiset.Pi.cons._proof_1 Bool
                        (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.cons Bool Bool.false (@List.nil Bool)))
                        Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                      h_1))))
            (fun h => @Eq.rec Bool Bool.false (fun x x_1 => (fun a => Bool) x) Bool.true a (@Eq.symm Bool a Bool.false h))
            (@Bool.rec (fun x => (fun a b => Decidable (@Eq Bool a b)) x Bool.false)
              (@Decidable.isTrue (@Eq Bool Bool.false Bool.false) (@rfl Bool Bool.false))
              (@Decidable.isFalse (@Eq Bool Bool.true Bool.false) fun h => @Bool.noConfusion False Bool.true Bool.false h)
              a))
        (fun h => @Eq.rec Bool Bool.true (fun x x_1 => (fun a => Bool) x) Bool.true a (@Eq.symm Bool a Bool.true h))
        (@Bool.rec (fun x => (fun a b => Decidable (@Eq Bool a b)) x Bool.true)
          (@Decidable.isFalse (@Eq Bool Bool.false Bool.true) fun h => @Bool.noConfusion False Bool.false Bool.true h)
          (@Decidable.isTrue (@Eq Bool Bool.true Bool.true) (@rfl Bool Bool.true)) a) }

noncomputable def state_36 : D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM :=
  { direction := D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.CausalDirection.xCausesY,
    root := fun a =>
      @Decidable.rec (@Eq Bool a Bool.true) (fun x => (fun a => Bool) a)
        (fun h =>
          @Decidable.rec (@Eq Bool a Bool.false) (fun x => (fun a => Bool) a)
            (fun h_1 =>
              False.rec
                (fun x =>
                  (fun a a_1 => (fun a => Bool) a) a
                    (@Multiset.Pi.cons._proof_1 Bool (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool))
                      Bool.false a
                      (@Multiset.Pi.cons._proof_1 Bool
                        (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.cons Bool Bool.false (@List.nil Bool)))
                        Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                      h_1))
                (@List.Mem.casesOn Bool a
                  (fun a_1 x =>
                    @Eq (List Bool) (@List.nil Bool) a_1 →
                      @HEq
                          (@Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
                            (@OfNat.ofNat (Multiset Bool) (nat_lit 0)
                              (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool)))
                            a)
                          (@Multiset.Pi.cons._proof_1 Bool
                            (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool)) Bool.false a
                            (@Multiset.Pi.cons._proof_1 Bool
                              (@Quotient.mk (List Bool) (List.isSetoid Bool)
                                (@List.cons Bool Bool.false (@List.nil Bool)))
                              Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                            h_1)
                          (@List.Mem Bool a a_1) x →
                        False)
                  (@List.nil Bool)
                  (@Multiset.Pi.cons._proof_1 Bool (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool))
                    Bool.false a
                    (@Multiset.Pi.cons._proof_1 Bool
                      (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.cons Bool Bool.false (@List.nil Bool)))
                      Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                    h_1)
                  (fun as h_2 =>
                    @False.elim
                      (@HEq
                          (@Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
                            (@OfNat.ofNat (Multiset Bool) (nat_lit 0)
                              (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool)))
                            a)
                          (@Multiset.Pi.cons._proof_1 Bool
                            (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool)) Bool.false a
                            (@Multiset.Pi.cons._proof_1 Bool
                              (@Quotient.mk (List Bool) (List.isSetoid Bool)
                                (@List.cons Bool Bool.false (@List.nil Bool)))
                              Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                            h_1)
                          (@List.Mem Bool a (@List.cons Bool a as)) (@List.Mem.head Bool a as) →
                        False)
                      (@noConfusion_of_Nat (List Bool) (@List.ctorIdx Bool) (@List.nil Bool) (@List.cons Bool a as) h_2))
                  (fun b {as} a_1 h_2 =>
                    @False.elim
                      (@HEq
                          (@Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
                            (@OfNat.ofNat (Multiset Bool) (nat_lit 0)
                              (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool)))
                            a)
                          (@Multiset.Pi.cons._proof_1 Bool
                            (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool)) Bool.false a
                            (@Multiset.Pi.cons._proof_1 Bool
                              (@Quotient.mk (List Bool) (List.isSetoid Bool)
                                (@List.cons Bool Bool.false (@List.nil Bool)))
                              Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                            h_1)
                          (@List.Mem Bool a (@List.cons Bool b as)) (@List.Mem.tail Bool a b as a_1) →
                        False)
                      (@noConfusion_of_Nat (List Bool) (@List.ctorIdx Bool) (@List.nil Bool) (@List.cons Bool b as) h_2))
                  (@Eq.refl (List Bool) (@List.nil Bool))
                  (@HEq.refl
                    (@Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
                      (@OfNat.ofNat (Multiset Bool) (nat_lit 0)
                        (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool)))
                      a)
                    (@Multiset.Pi.cons._proof_1 Bool (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool))
                      Bool.false a
                      (@Multiset.Pi.cons._proof_1 Bool
                        (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.cons Bool Bool.false (@List.nil Bool)))
                        Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                      h_1))))
            (fun h => @Eq.rec Bool Bool.false (fun x x_1 => (fun a => Bool) x) Bool.true a (@Eq.symm Bool a Bool.false h))
            (@Bool.rec (fun x => (fun a b => Decidable (@Eq Bool a b)) x Bool.false)
              (@Decidable.isTrue (@Eq Bool Bool.false Bool.false) (@rfl Bool Bool.false))
              (@Decidable.isFalse (@Eq Bool Bool.true Bool.false) fun h => @Bool.noConfusion False Bool.true Bool.false h)
              a))
        (fun h => @Eq.rec Bool Bool.true (fun x x_1 => (fun a => Bool) x) Bool.false a (@Eq.symm Bool a Bool.true h))
        (@Bool.rec (fun x => (fun a b => Decidable (@Eq Bool a b)) x Bool.true)
          (@Decidable.isFalse (@Eq Bool Bool.false Bool.true) fun h => @Bool.noConfusion False Bool.false Bool.true h)
          (@Decidable.isTrue (@Eq Bool Bool.true Bool.true) (@rfl Bool Bool.true)) a),
    child := fun a =>
      @Decidable.rec (@Eq Bool a Bool.true) (fun x => (fun a => Bool) a)
        (fun h =>
          @Decidable.rec (@Eq Bool a Bool.false) (fun x => (fun a => Bool) a)
            (fun h_1 =>
              False.rec
                (fun x =>
                  (fun a a_1 => (fun a => Bool) a) a
                    (@Multiset.Pi.cons._proof_1 Bool (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool))
                      Bool.false a
                      (@Multiset.Pi.cons._proof_1 Bool
                        (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.cons Bool Bool.false (@List.nil Bool)))
                        Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                      h_1))
                (@List.Mem.casesOn Bool a
                  (fun a_1 x =>
                    @Eq (List Bool) (@List.nil Bool) a_1 →
                      @HEq
                          (@Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
                            (@OfNat.ofNat (Multiset Bool) (nat_lit 0)
                              (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool)))
                            a)
                          (@Multiset.Pi.cons._proof_1 Bool
                            (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool)) Bool.false a
                            (@Multiset.Pi.cons._proof_1 Bool
                              (@Quotient.mk (List Bool) (List.isSetoid Bool)
                                (@List.cons Bool Bool.false (@List.nil Bool)))
                              Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                            h_1)
                          (@List.Mem Bool a a_1) x →
                        False)
                  (@List.nil Bool)
                  (@Multiset.Pi.cons._proof_1 Bool (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool))
                    Bool.false a
                    (@Multiset.Pi.cons._proof_1 Bool
                      (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.cons Bool Bool.false (@List.nil Bool)))
                      Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                    h_1)
                  (fun as h_2 =>
                    @False.elim
                      (@HEq
                          (@Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
                            (@OfNat.ofNat (Multiset Bool) (nat_lit 0)
                              (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool)))
                            a)
                          (@Multiset.Pi.cons._proof_1 Bool
                            (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool)) Bool.false a
                            (@Multiset.Pi.cons._proof_1 Bool
                              (@Quotient.mk (List Bool) (List.isSetoid Bool)
                                (@List.cons Bool Bool.false (@List.nil Bool)))
                              Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                            h_1)
                          (@List.Mem Bool a (@List.cons Bool a as)) (@List.Mem.head Bool a as) →
                        False)
                      (@noConfusion_of_Nat (List Bool) (@List.ctorIdx Bool) (@List.nil Bool) (@List.cons Bool a as) h_2))
                  (fun b {as} a_1 h_2 =>
                    @False.elim
                      (@HEq
                          (@Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
                            (@OfNat.ofNat (Multiset Bool) (nat_lit 0)
                              (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool)))
                            a)
                          (@Multiset.Pi.cons._proof_1 Bool
                            (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool)) Bool.false a
                            (@Multiset.Pi.cons._proof_1 Bool
                              (@Quotient.mk (List Bool) (List.isSetoid Bool)
                                (@List.cons Bool Bool.false (@List.nil Bool)))
                              Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                            h_1)
                          (@List.Mem Bool a (@List.cons Bool b as)) (@List.Mem.tail Bool a b as a_1) →
                        False)
                      (@noConfusion_of_Nat (List Bool) (@List.ctorIdx Bool) (@List.nil Bool) (@List.cons Bool b as) h_2))
                  (@Eq.refl (List Bool) (@List.nil Bool))
                  (@HEq.refl
                    (@Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
                      (@OfNat.ofNat (Multiset Bool) (nat_lit 0)
                        (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool)))
                      a)
                    (@Multiset.Pi.cons._proof_1 Bool (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool))
                      Bool.false a
                      (@Multiset.Pi.cons._proof_1 Bool
                        (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.cons Bool Bool.false (@List.nil Bool)))
                        Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                      h_1))))
            (fun h =>
              @Eq.rec Bool Bool.false (fun x x_1 => (fun a => Bool) x) Bool.false a (@Eq.symm Bool a Bool.false h))
            (@Bool.rec (fun x => (fun a b => Decidable (@Eq Bool a b)) x Bool.false)
              (@Decidable.isTrue (@Eq Bool Bool.false Bool.false) (@rfl Bool Bool.false))
              (@Decidable.isFalse (@Eq Bool Bool.true Bool.false) fun h => @Bool.noConfusion False Bool.true Bool.false h)
              a))
        (fun h => @Eq.rec Bool Bool.true (fun x x_1 => (fun a => Bool) x) Bool.true a (@Eq.symm Bool a Bool.true h))
        (@Bool.rec (fun x => (fun a b => Decidable (@Eq Bool a b)) x Bool.true)
          (@Decidable.isFalse (@Eq Bool Bool.false Bool.true) fun h => @Bool.noConfusion False Bool.false Bool.true h)
          (@Decidable.isTrue (@Eq Bool Bool.true Bool.true) (@rfl Bool Bool.true)) a) }

noncomputable def state_37 : D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM :=
  { direction := D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.CausalDirection.xCausesY,
    root := fun a =>
      @Decidable.rec (@Eq Bool a Bool.true) (fun x => (fun a => Bool) a)
        (fun h =>
          @Decidable.rec (@Eq Bool a Bool.false) (fun x => (fun a => Bool) a)
            (fun h_1 =>
              False.rec
                (fun x =>
                  (fun a a_1 => (fun a => Bool) a) a
                    (@Multiset.Pi.cons._proof_1 Bool (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool))
                      Bool.false a
                      (@Multiset.Pi.cons._proof_1 Bool
                        (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.cons Bool Bool.false (@List.nil Bool)))
                        Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                      h_1))
                (@List.Mem.casesOn Bool a
                  (fun a_1 x =>
                    @Eq (List Bool) (@List.nil Bool) a_1 →
                      @HEq
                          (@Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
                            (@OfNat.ofNat (Multiset Bool) (nat_lit 0)
                              (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool)))
                            a)
                          (@Multiset.Pi.cons._proof_1 Bool
                            (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool)) Bool.false a
                            (@Multiset.Pi.cons._proof_1 Bool
                              (@Quotient.mk (List Bool) (List.isSetoid Bool)
                                (@List.cons Bool Bool.false (@List.nil Bool)))
                              Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                            h_1)
                          (@List.Mem Bool a a_1) x →
                        False)
                  (@List.nil Bool)
                  (@Multiset.Pi.cons._proof_1 Bool (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool))
                    Bool.false a
                    (@Multiset.Pi.cons._proof_1 Bool
                      (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.cons Bool Bool.false (@List.nil Bool)))
                      Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                    h_1)
                  (fun as h_2 =>
                    @False.elim
                      (@HEq
                          (@Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
                            (@OfNat.ofNat (Multiset Bool) (nat_lit 0)
                              (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool)))
                            a)
                          (@Multiset.Pi.cons._proof_1 Bool
                            (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool)) Bool.false a
                            (@Multiset.Pi.cons._proof_1 Bool
                              (@Quotient.mk (List Bool) (List.isSetoid Bool)
                                (@List.cons Bool Bool.false (@List.nil Bool)))
                              Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                            h_1)
                          (@List.Mem Bool a (@List.cons Bool a as)) (@List.Mem.head Bool a as) →
                        False)
                      (@noConfusion_of_Nat (List Bool) (@List.ctorIdx Bool) (@List.nil Bool) (@List.cons Bool a as) h_2))
                  (fun b {as} a_1 h_2 =>
                    @False.elim
                      (@HEq
                          (@Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
                            (@OfNat.ofNat (Multiset Bool) (nat_lit 0)
                              (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool)))
                            a)
                          (@Multiset.Pi.cons._proof_1 Bool
                            (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool)) Bool.false a
                            (@Multiset.Pi.cons._proof_1 Bool
                              (@Quotient.mk (List Bool) (List.isSetoid Bool)
                                (@List.cons Bool Bool.false (@List.nil Bool)))
                              Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                            h_1)
                          (@List.Mem Bool a (@List.cons Bool b as)) (@List.Mem.tail Bool a b as a_1) →
                        False)
                      (@noConfusion_of_Nat (List Bool) (@List.ctorIdx Bool) (@List.nil Bool) (@List.cons Bool b as) h_2))
                  (@Eq.refl (List Bool) (@List.nil Bool))
                  (@HEq.refl
                    (@Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
                      (@OfNat.ofNat (Multiset Bool) (nat_lit 0)
                        (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool)))
                      a)
                    (@Multiset.Pi.cons._proof_1 Bool (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool))
                      Bool.false a
                      (@Multiset.Pi.cons._proof_1 Bool
                        (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.cons Bool Bool.false (@List.nil Bool)))
                        Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                      h_1))))
            (fun h => @Eq.rec Bool Bool.false (fun x x_1 => (fun a => Bool) x) Bool.true a (@Eq.symm Bool a Bool.false h))
            (@Bool.rec (fun x => (fun a b => Decidable (@Eq Bool a b)) x Bool.false)
              (@Decidable.isTrue (@Eq Bool Bool.false Bool.false) (@rfl Bool Bool.false))
              (@Decidable.isFalse (@Eq Bool Bool.true Bool.false) fun h => @Bool.noConfusion False Bool.true Bool.false h)
              a))
        (fun h => @Eq.rec Bool Bool.true (fun x x_1 => (fun a => Bool) x) Bool.false a (@Eq.symm Bool a Bool.true h))
        (@Bool.rec (fun x => (fun a b => Decidable (@Eq Bool a b)) x Bool.true)
          (@Decidable.isFalse (@Eq Bool Bool.false Bool.true) fun h => @Bool.noConfusion False Bool.false Bool.true h)
          (@Decidable.isTrue (@Eq Bool Bool.true Bool.true) (@rfl Bool Bool.true)) a),
    child := fun a =>
      @Decidable.rec (@Eq Bool a Bool.true) (fun x => (fun a => Bool) a)
        (fun h =>
          @Decidable.rec (@Eq Bool a Bool.false) (fun x => (fun a => Bool) a)
            (fun h_1 =>
              False.rec
                (fun x =>
                  (fun a a_1 => (fun a => Bool) a) a
                    (@Multiset.Pi.cons._proof_1 Bool (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool))
                      Bool.false a
                      (@Multiset.Pi.cons._proof_1 Bool
                        (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.cons Bool Bool.false (@List.nil Bool)))
                        Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                      h_1))
                (@List.Mem.casesOn Bool a
                  (fun a_1 x =>
                    @Eq (List Bool) (@List.nil Bool) a_1 →
                      @HEq
                          (@Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
                            (@OfNat.ofNat (Multiset Bool) (nat_lit 0)
                              (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool)))
                            a)
                          (@Multiset.Pi.cons._proof_1 Bool
                            (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool)) Bool.false a
                            (@Multiset.Pi.cons._proof_1 Bool
                              (@Quotient.mk (List Bool) (List.isSetoid Bool)
                                (@List.cons Bool Bool.false (@List.nil Bool)))
                              Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                            h_1)
                          (@List.Mem Bool a a_1) x →
                        False)
                  (@List.nil Bool)
                  (@Multiset.Pi.cons._proof_1 Bool (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool))
                    Bool.false a
                    (@Multiset.Pi.cons._proof_1 Bool
                      (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.cons Bool Bool.false (@List.nil Bool)))
                      Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                    h_1)
                  (fun as h_2 =>
                    @False.elim
                      (@HEq
                          (@Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
                            (@OfNat.ofNat (Multiset Bool) (nat_lit 0)
                              (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool)))
                            a)
                          (@Multiset.Pi.cons._proof_1 Bool
                            (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool)) Bool.false a
                            (@Multiset.Pi.cons._proof_1 Bool
                              (@Quotient.mk (List Bool) (List.isSetoid Bool)
                                (@List.cons Bool Bool.false (@List.nil Bool)))
                              Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                            h_1)
                          (@List.Mem Bool a (@List.cons Bool a as)) (@List.Mem.head Bool a as) →
                        False)
                      (@noConfusion_of_Nat (List Bool) (@List.ctorIdx Bool) (@List.nil Bool) (@List.cons Bool a as) h_2))
                  (fun b {as} a_1 h_2 =>
                    @False.elim
                      (@HEq
                          (@Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
                            (@OfNat.ofNat (Multiset Bool) (nat_lit 0)
                              (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool)))
                            a)
                          (@Multiset.Pi.cons._proof_1 Bool
                            (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool)) Bool.false a
                            (@Multiset.Pi.cons._proof_1 Bool
                              (@Quotient.mk (List Bool) (List.isSetoid Bool)
                                (@List.cons Bool Bool.false (@List.nil Bool)))
                              Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                            h_1)
                          (@List.Mem Bool a (@List.cons Bool b as)) (@List.Mem.tail Bool a b as a_1) →
                        False)
                      (@noConfusion_of_Nat (List Bool) (@List.ctorIdx Bool) (@List.nil Bool) (@List.cons Bool b as) h_2))
                  (@Eq.refl (List Bool) (@List.nil Bool))
                  (@HEq.refl
                    (@Membership.mem Bool (Multiset Bool) (@Multiset.instMembership Bool)
                      (@OfNat.ofNat (Multiset Bool) (nat_lit 0)
                        (@Zero.toOfNat0 (Multiset Bool) (@Multiset.instZero Bool)))
                      a)
                    (@Multiset.Pi.cons._proof_1 Bool (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.nil Bool))
                      Bool.false a
                      (@Multiset.Pi.cons._proof_1 Bool
                        (@Quotient.mk (List Bool) (List.isSetoid Bool) (@List.cons Bool Bool.false (@List.nil Bool)))
                        Bool.true a (@Finset.mem_univ Bool Bool.fintype a) h)
                      h_1))))
            (fun h => @Eq.rec Bool Bool.false (fun x x_1 => (fun a => Bool) x) Bool.true a (@Eq.symm Bool a Bool.false h))
            (@Bool.rec (fun x => (fun a b => Decidable (@Eq Bool a b)) x Bool.false)
              (@Decidable.isTrue (@Eq Bool Bool.false Bool.false) (@rfl Bool Bool.false))
              (@Decidable.isFalse (@Eq Bool Bool.true Bool.false) fun h => @Bool.noConfusion False Bool.true Bool.false h)
              a))
        (fun h => @Eq.rec Bool Bool.true (fun x x_1 => (fun a => Bool) x) Bool.false a (@Eq.symm Bool a Bool.true h))
        (@Bool.rec (fun x => (fun a b => Decidable (@Eq Bool a b)) x Bool.true)
          (@Decidable.isFalse (@Eq Bool Bool.false Bool.true) fun h => @Bool.noConfusion False Bool.false Bool.true h)
          (@Decidable.isTrue (@Eq Bool Bool.true Bool.true) (@rfl Bool Bool.true)) a) }

end Reg.Catalogs.InformationRoot.SealedCatalog

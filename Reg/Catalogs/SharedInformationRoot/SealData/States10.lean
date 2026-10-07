import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Multiset.Defs
import Mathlib.Data.Multiset.Pi
import Mathlib.Data.Multiset.ZeroCons
import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause

set_option backward.isDefEq.respectTransparency.types false

namespace Reg.Catalogs.SharedInformationRoot.SealedCatalog
open LeanInformationAudit

noncomputable def state_92 : Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
  Option D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.Mechanism :=
  fun a =>
    @Decidable.rec
      (@Eq (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) a
        ((fun i => i)
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 0)
            (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
      (fun x => (fun a => Option D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.Mechanism) a)
      (fun h =>
        @Decidable.rec
          (@Eq (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) a
            ((fun i => i)
              (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 1)
                (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
          (fun x => (fun a => Option D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.Mechanism) a)
          (fun h_1 =>
            False.rec
              (fun x =>
                (fun a a_1 =>
                    (fun a => Option D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.Mechanism) a)
                  a
                  (@Multiset.Pi.cons._proof_1 (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@Quotient.mk (List (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (List.isSetoid (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@List.nil (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                    ((fun i => i)
                      (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 1)
                        (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                    a
                    (@Multiset.Pi.cons._proof_1 (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@Quotient.mk (List (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        (List.isSetoid (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        ((fun x1 x2 =>
                            @List.cons (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) ((fun i => i) x1)
                              x2)
                          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 1)
                            (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          (@List.nil (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                      ((fun i => i)
                        (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 0)
                          (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                      a
                      (@Finset.mem_univ (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) a)
                      h)
                    h_1))
              (@List.Mem.casesOn (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) a
                (fun a_1 x =>
                  @Eq (List (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@List.nil (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) a_1 →
                    @HEq
                        (@Membership.mem (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (Multiset (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          (@Multiset.instMembership (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          (@OfNat.ofNat (Multiset (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                            (nat_lit 0)
                            (@Zero.toOfNat0 (Multiset (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                              (@Multiset.instZero (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                          a)
                        (@Multiset.Pi.cons._proof_1 (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@Quotient.mk (List (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                            (List.isSetoid (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                            (@List.nil (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                          ((fun i => i)
                            (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 1)
                              (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                          a
                          (@Multiset.Pi.cons._proof_1 (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@Quotient.mk (List (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                              (List.isSetoid (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                              ((fun x1 x2 =>
                                  @List.cons (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    ((fun i => i) x1) x2)
                                (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 1)
                                  (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                (@List.nil (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                            ((fun i => i)
                              (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 0)
                                (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                  (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                            a
                            (@Finset.mem_univ (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) a)
                            h)
                          h_1)
                        (@List.Mem (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) a a_1) x →
                      False)
                (@List.nil (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (@Multiset.Pi.cons._proof_1 (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@Quotient.mk (List (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (List.isSetoid (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@List.nil (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                  ((fun i => i)
                    (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 1)
                      (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                  a
                  (@Multiset.Pi.cons._proof_1 (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@Quotient.mk (List (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (List.isSetoid (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      ((fun x1 x2 =>
                          @List.cons (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) ((fun i => i) x1) x2)
                        (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 1)
                          (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        (@List.nil (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                    ((fun i => i)
                      (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 0)
                        (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                          (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                    a
                    (@Finset.mem_univ (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) a)
                    h)
                  h_1)
                (fun as h_2 =>
                  @False.elim
                    (@HEq
                        (@Membership.mem (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (Multiset (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          (@Multiset.instMembership (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          (@OfNat.ofNat (Multiset (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                            (nat_lit 0)
                            (@Zero.toOfNat0 (Multiset (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                              (@Multiset.instZero (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                          a)
                        (@Multiset.Pi.cons._proof_1 (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@Quotient.mk (List (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                            (List.isSetoid (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                            (@List.nil (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                          ((fun i => i)
                            (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 1)
                              (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                          a
                          (@Multiset.Pi.cons._proof_1 (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@Quotient.mk (List (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                              (List.isSetoid (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                              ((fun x1 x2 =>
                                  @List.cons (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    ((fun i => i) x1) x2)
                                (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 1)
                                  (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                (@List.nil (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                            ((fun i => i)
                              (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 0)
                                (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                  (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                            a
                            (@Finset.mem_univ (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) a)
                            h)
                          h_1)
                        (@List.Mem (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) a
                          (@List.cons (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) a as))
                        (@List.Mem.head (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) a as) →
                      False)
                    (@noConfusion_of_Nat (List (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@List.ctorIdx (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@List.nil (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@List.cons (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) a as) h_2))
                (fun b {as} a_1 h_2 =>
                  @False.elim
                    (@HEq
                        (@Membership.mem (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (Multiset (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          (@Multiset.instMembership (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          (@OfNat.ofNat (Multiset (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                            (nat_lit 0)
                            (@Zero.toOfNat0 (Multiset (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                              (@Multiset.instZero (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                          a)
                        (@Multiset.Pi.cons._proof_1 (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@Quotient.mk (List (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                            (List.isSetoid (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                            (@List.nil (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                          ((fun i => i)
                            (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 1)
                              (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                          a
                          (@Multiset.Pi.cons._proof_1 (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@Quotient.mk (List (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                              (List.isSetoid (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                              ((fun x1 x2 =>
                                  @List.cons (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    ((fun i => i) x1) x2)
                                (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 1)
                                  (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                (@List.nil (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                            ((fun i => i)
                              (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 0)
                                (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                  (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                            a
                            (@Finset.mem_univ (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) a)
                            h)
                          h_1)
                        (@List.Mem (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) a
                          (@List.cons (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) b as))
                        (@List.Mem.tail (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) a b as a_1) →
                      False)
                    (@noConfusion_of_Nat (List (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@List.ctorIdx (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@List.nil (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@List.cons (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) b as) h_2))
                (@Eq.refl (List (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@List.nil (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                (@HEq.refl
                  (@Membership.mem (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Multiset (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@Multiset.instMembership (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@OfNat.ofNat (Multiset (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (nat_lit 0)
                      (@Zero.toOfNat0 (Multiset (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        (@Multiset.instZero (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                    a)
                  (@Multiset.Pi.cons._proof_1 (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@Quotient.mk (List (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (List.isSetoid (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@List.nil (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                    ((fun i => i)
                      (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 1)
                        (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                    a
                    (@Multiset.Pi.cons._proof_1 (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@Quotient.mk (List (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        (List.isSetoid (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        ((fun x1 x2 =>
                            @List.cons (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) ((fun i => i) x1)
                              x2)
                          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 1)
                            (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          (@List.nil (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                      ((fun i => i)
                        (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 0)
                          (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                      a
                      (@Finset.mem_univ (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) a)
                      h)
                    h_1))))
          (fun h =>
            @Eq.rec (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              ((fun i => i)
                (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 1)
                  (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
              (fun x x_1 => (fun a => Option D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.Mechanism) x)
              (@Option.some D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.Mechanism
                D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.Mechanism.shooterB)
              a
              (@Eq.symm (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) a
                ((fun i => i)
                  (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 1)
                    (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                h))
          (@Decidable.rec
            (@Eq Nat (@Fin.val (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
              (@Fin.val (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                ((fun i => i)
                  (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 1)
                    (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
            (fun x =>
              (fun x =>
                  Decidable
                    (@Eq (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) a
                      ((fun i => i)
                        (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 1)
                          (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
                x)
            (fun h =>
              @Decidable.isFalse
                (@Eq (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) a
                  ((fun i => i)
                    (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 1)
                      (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                (instDecidableEqFin._proof_1 (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a
                  ((fun i => i)
                    (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 1)
                      (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                  h))
            (fun h =>
              @Decidable.isTrue
                (@Eq (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) a
                  ((fun i => i)
                    (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 1)
                      (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                (@Fin.eq_of_val_eq (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a
                  ((fun i => i)
                    (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 1)
                      (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                  h))
            (@Bool.rec
              (fun x =>
                @Eq Bool
                    ((@Fin.val (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a).beq
                      (@Fin.val (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        ((fun i => i)
                          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 1)
                            (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
                    x →
                  (fun x =>
                      Decidable
                        (@Eq Nat (@Fin.val (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                          (@Fin.val (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            ((fun i => i)
                              (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 1)
                                (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                    x)
              (fun h =>
                @Decidable.isFalse
                  (@Eq Nat (@Fin.val (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                    (@Fin.val (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                      ((fun i => i)
                        (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 1)
                          (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
                  (@Nat.ne_of_beq_eq_false (@Fin.val (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                    (@Fin.val (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                      ((fun i => i)
                        (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 1)
                          (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                    h))
              (fun h =>
                @Decidable.isTrue
                  (@Eq Nat (@Fin.val (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                    (@Fin.val (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                      ((fun i => i)
                        (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 1)
                          (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
                  (@Nat.eq_of_beq_eq_true (@Fin.val (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                    (@Fin.val (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                      ((fun i => i)
                        (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 1)
                          (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                    h))
              (a.1.beq (nat_lit 1))
              (@Eq.refl Bool
                ((@Fin.val (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a).beq
                  (@Fin.val (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    ((fun i => i)
                      (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 1)
                        (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))))
      (fun h =>
        @Eq.rec (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          ((fun i => i)
            (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 0)
              (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
          (fun x x_1 => (fun a => Option D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.Mechanism) x)
          (@Option.none D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.Mechanism) a
          (@Eq.symm (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) a
            ((fun i => i)
              (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 0)
                (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
            h))
      (@Decidable.rec
        (@Eq Nat (@Fin.val (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
          (@Fin.val (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            ((fun i => i)
              (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 0)
                (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
        (fun x =>
          (fun x =>
              Decidable
                (@Eq (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) a
                  ((fun i => i)
                    (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 0)
                      (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
            x)
        (fun h =>
          @Decidable.isFalse
            (@Eq (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) a
              ((fun i => i)
                (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 0)
                  (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
            (instDecidableEqFin._proof_1 (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a
              ((fun i => i)
                (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 0)
                  (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
              h))
        (fun h =>
          @Decidable.isTrue
            (@Eq (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) a
              ((fun i => i)
                (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 0)
                  (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
            (@Fin.eq_of_val_eq (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a
              ((fun i => i)
                (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 0)
                  (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
              h))
        (@Bool.rec
          (fun x =>
            @Eq Bool
                ((@Fin.val (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a).beq
                  (@Fin.val (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    ((fun i => i)
                      (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 0)
                        (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                          (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                x →
              (fun x =>
                  Decidable
                    (@Eq Nat (@Fin.val (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                      (@Fin.val (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        ((fun i => i)
                          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 0)
                            (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                              (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                x)
          (fun h =>
            @Decidable.isFalse
              (@Eq Nat (@Fin.val (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                (@Fin.val (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  ((fun i => i)
                    (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 0)
                      (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
              (@Nat.ne_of_beq_eq_false (@Fin.val (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                (@Fin.val (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  ((fun i => i)
                    (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 0)
                      (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
                h))
          (fun h =>
            @Decidable.isTrue
              (@Eq Nat (@Fin.val (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                (@Fin.val (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  ((fun i => i)
                    (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 0)
                      (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
              (@Nat.eq_of_beq_eq_true (@Fin.val (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                (@Fin.val (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  ((fun i => i)
                    (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 0)
                      (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
                h))
          (a.1.beq (nat_lit 0))
          (@Eq.refl Bool
            ((@Fin.val (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a).beq
              (@Fin.val (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                ((fun i => i)
                  (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 0)
                    (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                      (Nat.le_refl (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))))

end Reg.Catalogs.SharedInformationRoot.SealedCatalog

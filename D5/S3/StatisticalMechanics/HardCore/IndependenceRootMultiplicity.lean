/- GID: D5/S3/StatisticalMechanics/HardCore/IndependenceRootMultiplicity
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/HardCore/IndependenceRootMultiplicity
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/StatisticalMechanics/HardCore/IndependenceRootMultiplicity.Conjecture58; result=D5/S3/StatisticalMechanics/HardCore/IndependenceRootMultiplicity.result; claim=D5/S3/StatisticalMechanics/HardCore/IndependenceRootMultiplicity.Conjecture58
   digest: A triangle with three leaves per center refutes the multiplicity bound. -/

/-
proof_shape:
  corona_connected: content (constructs reachability through a center).
  corona_factorization: content (actual configuration split and factorization).
  corona_rootMultiplicity: content (residual evaluation and exact multiplicity).
  result: content (the configuration split and residual computation are live in the
    specialized connected counterexample). The numerical comparisons are bind-only.
Private proof organization:
  leaf_partition, domain_erase, domain_closedComplement, partition_with_centers,
  domain_univ, corona_partition: content (finite domains and the deletion split).
  independencePolynomial_eq_of_deciders: bind-only (used by result).
  ceil_half, corona_order, witness_order, witness_connected, witness_bound,
  witness_multiplicity: bind-only (used in the bound and result).
escape_witness: partition_with_centers gives the actual split in the live proof path.
admission_basis: open-problem-resolution (#34354; Refuted)
Direct frozen dependencies:
  D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion
  statement_id: sha256:8014b9cde4f69ed8e5049e30e505073622cbf5d96e9707ac8cda86d3aa47ff93
  configurations, partition, closedComplement, partition_delete, independencePolynomial.
-/

import D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion

/-!
# Multiplicity at negative one in a clique corona

The actual independence polynomial of a clique with private leaves factors
explicitly. The triangle with three leaves per center refutes Question 5.8
of Bhardwaj et al.
-/


-- The machine-readable utility header is a single line.
set_option linter.style.longLine false
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.StatisticalMechanics.HardCore.IndependenceRootMultiplicity

open D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion
open Polynomial
open scoped BigOperators

/-- A center is indexed by `Fin t`. A leaf carries its center's index and one
of that center's `k` private leaf indices. -/
abbrev Vertex (t k : ℕ) := Fin t ⊕ (Fin t × Fin k)

private def coronaAdj {t k : ℕ} : Vertex t k → Vertex t k → Prop
  | .inl i, .inl j => i ≠ j
  | .inl i, .inr p => i = p.1
  | .inr p, .inl i => i = p.1
  | .inr _, .inr _ => False

/-- The clique corona with `t` centers and `k` private leaves at each center. -/
def corona (t k : ℕ) : SimpleGraph (Vertex t k) where
  Adj := coronaAdj
  symm := ⟨by
    intro a b h
    cases a <;> cases b
    · exact Ne.symm h
    · exact h
    · exact h
    · exact h⟩
  loopless := ⟨by
    intro a
    cases a <;> simp [coronaAdj]⟩

instance coronaDecidableAdj {t k : ℕ} : DecidableRel (corona t k).Adj := by
  intro a b
  cases a <;> cases b <;> unfold corona coronaAdj <;> infer_instance

theorem corona_connected {t k : ℕ} (ht : 0 < t) : (corona t k).Connected := by
  let center : Fin t := ⟨0, ht⟩
  refine (SimpleGraph.connected_iff_exists_forall_reachable (G := corona t k)).mpr
    ⟨.inl center, ?_⟩
  have toCenter (i : Fin t) : (corona t k).Reachable (.inl center) (.inl i) := by
    by_cases h : center = i
    · subst i
      exact SimpleGraph.Reachable.refl _
    · exact SimpleGraph.Adj.reachable (G := corona t k) h
  rintro (i | p)
  · exact toCenter i
  · exact (toCenter p.1).trans (SimpleGraph.Adj.reachable (G := corona t k) rfl)

/-- The allowed centers are `C` and the allowed leaves have owners in `L`. -/
private def domain {t k : ℕ} (C L : Finset (Fin t)) : Finset (Vertex t k) :=
  C.disjSum (L ×ˢ (Finset.univ : Finset (Fin k)))

private theorem leaf_partition {t k : ℕ} {R : Type*} [CommSemiring R]
    (L : Finset (Fin t)) (z : R) :
    partition (corona t k) (domain ∅ L) (fun _ => z) = (1 + z) ^ (L.card * k) := by
  have hconfigs : configurations (corona t k) (domain ∅ L) = (domain ∅ L).powerset := by
    apply Finset.filter_eq_self.mpr
    intro A hA
    have hsub := Finset.mem_powerset.mp hA
    change (A : Set (Vertex t k)).Pairwise (fun a b => ¬ (corona t k).Adj a b)
    intro a ha b hb _
    have ha' := hsub (Finset.mem_coe.mp ha)
    have hb' := hsub (Finset.mem_coe.mp hb)
    cases a <;> cases b <;> simp_all [domain, corona, coronaAdj]
  rw [partition, hconfigs, ← Finset.prod_one_add]
  simp [domain, Finset.card_product]

private theorem domain_erase {t k : ℕ} (C L : Finset (Fin t)) (i : Fin t) :
    (domain (k := k) C L).erase (.inl i) = domain (C.erase i) L := by
  ext v
  cases v <;> simp [domain, and_comm]

private theorem domain_closedComplement {t k : ℕ} (C L : Finset (Fin t)) (i : Fin t) :
    closedComplement (corona t k) (domain C L) (.inl i) = domain ∅ (L.erase i) := by
  rw [closedComplement, domain_erase]
  ext v
  rw [Finset.mem_filter]
  cases v with
  | inl j =>
      simp only [domain, Finset.inl_mem_disjSum, Finset.mem_erase, corona, coronaAdj,
        not_not, Finset.notMem_empty, iff_false]
      rintro ⟨⟨hne, _⟩, he⟩
      exact hne he.symm
  | inr p => simp [domain, corona, coronaAdj, eq_comm, and_comm]

/-- Repeatedly split on center occupancy using the frozen partition deletion theorem.
There are `t*k` free leaves if no center is used. Choosing a center removes all
other centers and exactly its own private leaves. -/
private theorem partition_with_centers {t k : ℕ} {R : Type*} [CommSemiring R]
    (C : Finset (Fin t)) (z : R) :
    partition (corona t k) (domain C Finset.univ) (fun _ => z) =
      (1 + z) ^ (t * k) + (C.card : R) * z * (1 + z) ^ ((t - 1) * k) := by
  induction C using Finset.induction_on with
  | empty => simp [leaf_partition]
  | insert i C hi ih =>
      have hmem : Sum.inl i ∈ domain (k := k) (insert i C) Finset.univ := by
        simp [domain]
      rw [partition_delete _ _ _ hmem, domain_erase, Finset.erase_insert hi,
        domain_closedComplement, leaf_partition, ih, Finset.card_insert_of_notMem hi,
        Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
        Nat.cast_add, Nat.cast_one]
      ring

private theorem domain_univ (t k : ℕ) :
    domain (t := t) (k := k) Finset.univ Finset.univ = Finset.univ := by
  ext v
  cases v <;> simp [domain]

/-- The constant-activity partition sum on the full corona vertex set. -/
private theorem corona_partition (t k : ℕ) {R : Type*} [CommSemiring R] (z : R) :
    partition (corona t k) Finset.univ (fun _ => z) =
      (1 + z) ^ (t * k) + (t : R) * z * (1 + z) ^ ((t - 1) * k) := by
  rw [← domain_univ t k, partition_with_centers]
  simp

theorem corona_factorization {t k : ℕ} (ht : 0 < t) :
    independencePolynomial (corona t k) Finset.univ =
      (1 + X) ^ ((t - 1) * k) * ((1 + X) ^ k + (t : Polynomial ℤ) * X) := by
  have htk : t * k = (t - 1) * k + k := by
    calc
      t * k = (t - 1 + 1) * k := congrArg (· * k) (Nat.sub_add_cancel ht).symm
      _ = (t - 1) * k + k := by rw [Nat.add_mul, one_mul]
  rw [independencePolynomial, corona_partition, htk, pow_add]
  ring

theorem corona_rootMultiplicity {t k : ℕ} (ht : 0 < t) (hk : 0 < k) :
    rootMultiplicity (-1 : ℤ) (independencePolynomial (corona t k) Finset.univ) =
      (t - 1) * k := by
  let q : Polynomial ℤ := (1 + X) ^ k + (t : Polynomial ℤ) * X
  have hqEval : eval (-1 : ℤ) q = -(t : ℤ) := by
    simp [q, zero_pow hk.ne']
  have hq : ¬ IsRoot q (-1 : ℤ) := by
    rw [IsRoot.def, hqEval]
    omega
  have hq0 : q ≠ 0 := by
    intro he
    exact hq (by simp [he, IsRoot])
  have hlinear : (1 + X : Polynomial ℤ) = X - C (-1 : ℤ) := by
    simp [add_comm, sub_eq_add_neg]
  have hfactor : independencePolynomial (corona t k) Finset.univ =
      q * (X - C (-1 : ℤ)) ^ ((t - 1) * k) := by
    calc
      _ = (1 + X) ^ ((t - 1) * k) * q := corona_factorization ht
      _ = _ := by rw [← hlinear, mul_comm]
  rw [hfactor, rootMultiplicity_mul_X_sub_C_pow hq0, rootMultiplicity_eq_zero hq, zero_add]

private theorem independencePolynomial_eq_of_deciders {V : Type*} (G : SimpleGraph V)
    (s : Finset V) (d₁ d₂ : DecidableEq V) (a₁ a₂ : DecidableRel G.Adj) :
    @independencePolynomial V d₁ G a₁ s = @independencePolynomial V d₂ G a₂ s := by
  cases Subsingleton.elim d₁ d₂
  cases Subsingleton.elim a₁ a₂
  rfl

/-- The bound asked for in Question 5.8, arXiv:2607.08480v1. -/
def Conjecture58 : Prop := by
  classical
  exact ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    2 ≤ Fintype.card V → G.Connected →
      (rootMultiplicity (-1 : ℤ) (independencePolynomial G Finset.univ) : ℤ) ≤
        ⌈(Fintype.card V : ℚ) / 2⌉ - 1

private theorem ceil_half (n : ℕ) : ⌈(n : ℚ) / 2⌉ = (↑((n + 1) / 2 : ℕ) : ℤ) := by
  rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) from rfl, Rat.ceil_natCast_div_natCast]
  omega

private theorem corona_order (t k : ℕ) : Fintype.card (Vertex t k) = t + t * k := by
  simp [Vertex, Fintype.card_sum, Fintype.card_prod]

private theorem witness_multiplicity :
    rootMultiplicity (-1 : ℤ) (independencePolynomial (corona 3 3) Finset.univ) = 6 :=
  corona_rootMultiplicity (by decide : 0 < 3) (by decide : 0 < 3)

private theorem witness_order : Fintype.card (Vertex 3 3) = 12 := by
  rw [corona_order]

private theorem witness_connected : (corona 3 3).Connected := corona_connected (by decide)

private theorem witness_bound : ⌈(Fintype.card (Vertex 3 3) : ℚ) / 2⌉ - 1 = 5 := by
  norm_num [witness_order, ceil_half]

theorem result : Not Conjecture58 := by
  intro h
  have horder : 2 ≤ Fintype.card (Vertex 3 3) := by rw [witness_order]; decide
  have hbound := h (Vertex 3 3) (corona 3 3) horder witness_connected
  have hw : rootMultiplicity (-1 : ℤ)
      (@independencePolynomial (Vertex 3 3) (Classical.decEq _) (corona 3 3)
        (fun _ _ => Classical.propDecidable _) Finset.univ) = 6 := by
    rw [independencePolynomial_eq_of_deciders (corona 3 3) Finset.univ
      (Classical.decEq _) (inferInstance : DecidableEq (Vertex 3 3))
      (fun _ _ => Classical.propDecidable _) (inferInstance : DecidableRel (corona 3 3).Adj)]
    exact witness_multiplicity
  rw [hw, witness_bound] at hbound
  exact (by decide : ¬ ((6 : ℤ) ≤ 5)) hbound

end D5.S3.StatisticalMechanics.HardCore.IndependenceRootMultiplicity

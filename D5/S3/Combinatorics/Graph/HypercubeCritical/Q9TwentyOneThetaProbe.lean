import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9TwentyOneSquareGeometryProbe

/-! The right-side compression of the four-high star. -/

set_option autoImplicit false
noncomputable section

open Finset SimpleGraph
open scoped BigOperators

-- The four bits record adjacency to the already labeled matched endpoints.
private def incidentCount (p : Fin 4 → Bool) : ℕ :=
  ∑ i, (p i).toNat

private def diagonalBit (other : Bool) (i : Fin 4) : Bool :=
  if i = 0 ∨ i = 2 then true else other

private def thetaIncidences (p q : Fin 4 → Bool) (other bridge : Bool) : Prop :=
    (∀ i, (p i).toNat + (q i).toNat + (diagonalBit other i).toNat = 2) →
    incidentCount p + bridge.toNat = 3 →
    incidentCount q + bridge.toNat = 3 →
    (p 0 && p 2) = false → (q 0 && q 2) = false →
    (other && p 1 && p 3) = false → (other && q 1 && q 3) = false →
    ((other = true ∧ bridge = true ∧ p 0 ≠ p 2 ∧ p 1 ≠ p 3 ∧
        ∀ i, q i = !(p i)) ∨
      (other = false ∧ bridge = false ∧
        p 1 = true ∧ q 1 = true ∧ p 3 = true ∧ q 3 = true ∧
        p 0 ≠ p 2 ∧ q 0 = !(p 0) ∧ q 2 = !(p 2)))

private def incidenceRow (m : Fin 16) (i : Fin 4) : Bool :=
  m.val.testBit i.val

private lemma incidenceRow_surjective : Function.Surjective incidenceRow := by
  intro p
  let bits := (p 0).toNat + 2 * (p 1).toNat + 4 * (p 2).toNat + 8 * (p 3).toNat
  have hbits : bits < 16 := by
    dsimp [bits]
    cases h₀ : p 0 <;> cases h₁ : p 1 <;> cases h₂ : p 2 <;> cases h₃ : p 3 <;>
      decide
  refine ⟨⟨bits, hbits⟩, ?_⟩
  funext i
  fin_cases i
  · change bits.testBit 0 = p 0
    cases h₀ : p 0 <;> cases h₁ : p 1 <;> cases h₂ : p 2 <;> cases h₃ : p 3 <;>
      simp only [bits, h₀, h₁, h₂, h₃] <;> decide
  · change bits.testBit 1 = p 1
    cases h₀ : p 0 <;> cases h₁ : p 1 <;> cases h₂ : p 2 <;> cases h₃ : p 3 <;>
      simp only [bits, h₀, h₁, h₂, h₃] <;> decide
  · change bits.testBit 2 = p 2
    cases h₀ : p 0 <;> cases h₁ : p 1 <;> cases h₂ : p 2 <;> cases h₃ : p 3 <;>
      simp only [bits, h₀, h₁, h₂, h₃] <;> decide
  · change bits.testBit 3 = p 3
    cases h₀ : p 0 <;> cases h₁ : p 1 <;> cases h₂ : p 2 <;> cases h₃ : p 3 <;>
      simp only [bits, h₀, h₁, h₂, h₃] <;> decide


private instance (p q : Fin 4 → Bool) (other bridge : Bool) :
    Decidable (thetaIncidences p q other bridge) := by
  unfold thetaIncidences
  infer_instance

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
-- The checker considers the two degree-three incidence rows, each of four bits.
private lemma theta_incidence_bits :
    ∀ (p q : Fin 16) (other bridge : Bool), thetaIncidences (incidenceRow p) (incidenceRow q) other bridge := by
  decide +kernel

/-- With the diagonal 0–2 present, the six-vertex compressed side has the
two theta patterns. The vertex labels remain attached to the given square. -/
private lemma theta_incidence_cases (p q : Fin 4 → Bool) (other bridge : Bool) :
    thetaIncidences p q other bridge := by
  obtain ⟨a, rfl⟩ := incidenceRow_surjective p
  obtain ⟨b, rfl⟩ := incidenceRow_surjective q
  exact theta_incidence_bits a b other bridge

#print axioms theta_incidence_cases

private lemma degree_as_incidence_sum {V : Type*} [Fintype V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (x : V) :
    H.degree x = ∑ y, (decide (H.Adj x y)).toNat := by
  rw [← H.card_neighborFinset_eq_degree, H.neighborFinset_eq_filter, card_eq_sum_ones, sum_filter]
  apply sum_congr rfl
  intro y _
  by_cases h : H.Adj x y <;> simp [h]

/-- Read the two possible theta shapes directly from the actual graph once
0 and 2 are known to be joined. The last two vertices are the degree-three
vertices outside the four labeled ends. -/
private lemma theta_from_matched_diagonal
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (hV : Fintype.card V = 6) (B : Fin 4 ↪ V)
    (hdeg : ∀ x, H.degree x = if x ∈ Set.range B then 2 else 3)
    (hdiag : ∀ i j, H.Adj (B i) (B j) → j = i + 2)
    (h02 : H.Adj (B 0) (B 2))
    (htri : ∀ x y z, H.Adj x y → H.Adj y z → H.Adj z x → False) :
    ∃ P Q : V, P ≠ Q ∧ P ∉ Set.range B ∧ Q ∉ Set.range B ∧
      ((H.Adj (B 1) (B 3) ∧ H.Adj P Q ∧
        (decide (H.Adj P (B 0))) ≠ decide (H.Adj P (B 2)) ∧
        (decide (H.Adj P (B 1))) ≠ decide (H.Adj P (B 3)) ∧
        ∀ i, ¬ (H.Adj Q (B i) ↔ H.Adj P (B i))) ∨
      (¬ H.Adj (B 1) (B 3) ∧ ¬ H.Adj P Q ∧
        H.Adj P (B 1) ∧ H.Adj Q (B 1) ∧ H.Adj P (B 3) ∧ H.Adj Q (B 3) ∧
        (decide (H.Adj P (B 0))) ≠ decide (H.Adj P (B 2)) ∧
        ¬ (H.Adj Q (B 0) ↔ H.Adj P (B 0)) ∧
        ¬ (H.Adj Q (B 2) ↔ H.Adj P (B 2)))) := by
  let ends : Finset V := univ.map B
  have memEnds (x : V) : x ∈ ends ↔ x ∈ Set.range B := by simp [ends, Set.mem_range]
  have hc : ((univ : Finset V) \ ends).card = 2 := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, hV]
    simp [ends]
  obtain ⟨P, Q, hPQ, hpair⟩ := card_eq_two.mp hc
  have hP : P ∉ Set.range B := by
    intro h
    have hm : P ∈ (univ : Finset V) \ ends := by rw [hpair]; simp
    exact (mem_sdiff.mp hm).2 ((memEnds P).mpr h)
  have hQ : Q ∉ Set.range B := by
    intro h
    have hm : Q ∈ (univ : Finset V) \ ends := by rw [hpair]; simp
    exact (mem_sdiff.mp hm).2 ((memEnds Q).mpr h)
  have hdis : Disjoint ends ({P, Q} : Finset V) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    rcases mem_insert.mp hy with he | hy
    · exact hP ((memEnds P).mp (he ▸ hx))
    · exact hQ ((memEnds Q).mp (mem_singleton.mp hy ▸ hx))
  have hu : ends ∪ {P, Q} = (univ : Finset V) := by
    rw [← hpair, union_sdiff_of_subset (subset_univ _)]
  let p (i : Fin 4) := decide (H.Adj P (B i))
  let q (i : Fin 4) := decide (H.Adj Q (B i))
  let other := decide (H.Adj (B 1) (B 3))
  let bridge := decide (H.Adj P Q)
  have degree_count (x : V) : H.degree x =
      (∑ i, (decide (H.Adj x (B i))).toNat) +
        (decide (H.Adj x P)).toNat + (decide (H.Adj x Q)).toNat := by
    rw [degree_as_incidence_sum H x, ← hu, sum_union hdis]
    rw [show (∑ y ∈ ends, (decide (H.Adj x y)).toNat) =
      ∑ i, (decide (H.Adj x (B i))).toNat by simp [ends, sum_map]]
    rw [sum_insert (by simpa using hPQ), sum_singleton, Nat.add_assoc]
  have hpd : incidentCount p + bridge.toNat = 3 := by
    have h := degree_count P
    rw [hdeg P, ite_eq_right hP] at h
    simpa [incidentCount, p, bridge] using h.symm
  have hqd : incidentCount q + bridge.toNat = 3 := by
    have h := degree_count Q
    rw [hdeg Q, ite_eq_right hQ] at h
    simpa [incidentCount, q, bridge, H.adj_comm Q P] using h.symm
  have hd (i : Fin 4) : (decide (H.Adj (B i) (B (i + 2)))) = diagonalBit other i := by
    fin_cases i
    · simp [diagonalBit, h02]
    · rfl
    · simp [diagonalBit, h02.symm]
    · change decide (H.Adj (B 3) (B 1)) = diagonalBit other 3
      simp [diagonalBit, other, H.adj_comm (B 3) (B 1)]
  have each (i : Fin 4) : (p i).toNat + (q i).toNat + (diagonalBit other i).toNat = 2 := by
    have h := degree_count (B i)
    rw [hdeg (B i), ite_eq_left (show B i ∈ Set.range B from ⟨i, rfl⟩)] at h
    have hs : (∑ j : Fin 4, (decide (H.Adj (B i) (B j))).toNat) =
        (diagonalBit other i).toNat := by
      rw [← hd i]
      apply sum_eq_single (i + 2)
      · intro j _ hne
        have hn : ¬ H.Adj (B i) (B j) := fun he => hne (hdiag i j he)
        simp [hn]
      · simp
    simp only [hs, H.adj_comm (B i) P, H.adj_comm (B i) Q] at h
    change 2 = (diagonalBit other i).toNat + (p i).toNat + (q i).toNat at h
    omega
  have no_tri (x : V) {i j : Fin 4} (h : H.Adj (B i) (B j)) :
      (decide (H.Adj x (B i)) && decide (H.Adj x (B j))) = false := by
    by_cases hxi : H.Adj x (B i)
    · have hnj : ¬ H.Adj x (B j) := fun hj => htri x (B i) (B j) hxi h hj.symm
      simp [hxi, hnj]
    · simp [hxi]
  have no_otherP : (other && p 1 && p 3) = false := by
    by_cases hh : H.Adj (B 1) (B 3)
    · simpa [other, hh, p] using no_tri P hh
    · simp [other, hh]
  have no_otherQ : (other && q 1 && q 3) = false := by
    by_cases hh : H.Adj (B 1) (B 3)
    · simpa [other, hh, q] using no_tri Q hh
    · simp [other, hh]
  have result := theta_incidence_cases p q other bridge each hpd hqd
    (no_tri P h02) (no_tri Q h02) no_otherP no_otherQ
  refine ⟨P, Q, hPQ, hP, hQ, ?_⟩
  simpa [other, bridge, p, q, Bool.eq_not_iff] using result

#print axioms theta_from_matched_diagonal

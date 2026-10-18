/- GID: D5/S3/Quantum/Information/StabilizerLogicalZSupportRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/StabilizerLogicalZSupportRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/StabilizerLogicalZSupportRefutation.claim; result=D5/S3/Quantum/Information/StabilizerLogicalZSupportRefutation.result; claim=D5/S3/Quantum/Information/StabilizerLogicalZSupportRefutation.claim
   digest: A five-qubit stabilizer code refutes universal logical Z support. -/

import D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Quantum.Information.StabilizerLogicalZSupportRefutation

open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence (Pauli anticomm)
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli

/-- Pointwise phase-free multiplication of Pauli words. -/
def wmul {n : ℕ} (u v : Fin n → Pauli) : Fin n → Pauli := fun i =>
  D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.letterProduct (u i) (v i)

/-- Pauli words commute when the number of anticommuting positions is even. -/
def Commutes {n : ℕ} (u v : Fin n → Pauli) : Prop :=
  (∑ i, (anticomm (u i) (v i)).toNat) % 2 = 0

private def sprod {n r : ℕ} (g : Fin r → Fin n → Pauli) (b : Fin r → Bool) :
    Fin n → Pauli :=
  (List.finRange r).foldr (fun j w => if b j then wmul (g j) w else w) (fun _ => I)

/-- Stabilizer words are products over a subset of the specified generators. -/
def InStabilizer {n r : ℕ} (g : Fin r → Fin n → Pauli) (w : Fin n → Pauli) : Prop :=
  ∃ b : Fin r → Bool, sprod g b = w

/-- Commuting independent generators with at least one encoded qubit.
Independence says that only the empty subset has the identity as its product. -/
def IsStabilizerCode {n r : ℕ} (g : Fin r → Fin n → Pauli) : Prop :=
  (∀ a b, Commutes (g a) (g b)) ∧
  (∀ b : Fin r → Bool, sprod g b = (fun _ => I) → ∀ j, b j = false) ∧ r < n

/-- The logical-Z support conjecture, weakened to the existence of one nontrivial logical word.
The support condition requires a literal `Z` in every stabilizer translate of that word. -/
def claim : Prop :=
  ∀ (n r : ℕ) (g : Fin r → Fin n → Pauli), IsStabilizerCode g →
    ∃ L : Fin n → Pauli, (∀ a, Commutes L (g a)) ∧ ¬ InStabilizer g L ∧
      ∀ s, InStabilizer g s → ∃ i, wmul s L i = Z

private def generators : Fin 4 → Fin 5 → Pauli :=
  ![![X, Z, Z, X, I], ![I, X, Z, Z, Z], ![X, I, X, Z, Y], ![Z, X, I, X, Y]]

private lemma code_valid : IsStabilizerCode generators := by
  unfold IsStabilizerCode Commutes
  decide

private def logical : Fin 4 → Fin 5 → Pauli :=
  ![![I, I, I, I, I], ![X, X, X, X, Z], ![Y, Y, Y, Y, X], ![Z, Z, Z, Z, Y]]

-- Splitting the first three coordinates leaves sixteen words per decision.
private lemma cosets_table (a b c : Pauli) :
    ∀ d e : Pauli, (∀ j, Commutes (![a, b, c, d, e]) (generators j)) →
      ∃ k : Fin 4, ∃ t : Fin 4 → Bool,
        ![a, b, c, d, e] = wmul (logical k) (sprod generators t) := by
  cases a <;> cases b <;> cases c <;> unfold Commutes <;> decide

private lemma classify (L : Fin 5 → Pauli) (h : ∀ j, Commutes L (generators j)) :
    ∃ k : Fin 4, ∃ t : Fin 4 → Bool, L = wmul (logical k) (sprod generators t) := by
  have hL : L = ![L 0, L 1, L 2, L 3, L 4] := by
    ext i
    fin_cases i <;> rfl
  rw [hL] at h ⊢
  exact cosets_table _ _ _ _ _ h

-- The nontrivial representatives are corrected by g2, the identity, and g1 respectively.
private def correction : Fin 4 → Fin 4 → Bool :=
  ![![false, false, false, false], ![false, true, false, false],
    ![false, false, false, false], ![true, false, false, false]]

-- Toggling the selected subset multiplies the correction by the same stabilizer word.
private lemma corrects (k : Fin 4) (t : Fin 4 → Bool) :
    wmul (sprod generators (fun j => xor (correction k j) (t j)))
        (wmul (logical k) (sprod generators t)) =
      wmul (sprod generators (correction k)) (logical k) := by
  fin_cases k <;> revert t <;> decide

private lemma zfree (k : Fin 4) (hk : k ≠ 0) :
    ∀ i, wmul (sprod generators (correction k)) (logical k) i ≠ Z := by
  fin_cases k
  · exact (hk rfl).elim
  · decide
  · decide
  · decide

private lemma identity_coset (t : Fin 4 → Bool) :
    wmul (logical 0) (sprod generators t) = sprod generators t := by
  ext i
  fin_cases i <;> rfl

/-- No choice of logical Z satisfies the support conjecture for the specified five-qubit code. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨L, hComm, hNon, hZ⟩ := h 5 4 generators code_valid
  obtain ⟨k, t, rfl⟩ := classify L hComm
  by_cases hk : k = 0
  · subst k
    exact hNon ⟨t, (identity_coset t).symm⟩
  · obtain ⟨i, hi⟩ := hZ
      (sprod generators (fun j => xor (correction k j) (t j))) ⟨_, rfl⟩
    rw [corrects] at hi
    exact zfree k hk i hi

end D5.S3.Quantum.Information.StabilizerLogicalZSupportRefutation

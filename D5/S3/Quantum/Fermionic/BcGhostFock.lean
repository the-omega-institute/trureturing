/- GID: D5/S3/Quantum/Fermionic/BcGhostFock
   generality: I
   mirror-B: D5/B/S3/Quantum/Fermionic/BcGhostFock
   mirror-E: none(waiver:algebraic-ghost-car)
   anchors: []
   utility: none
   digest: Integer bc modes on countable occupation Fock space obey ghost CAR. -/

import D5.S3.Quantum.Fermionic.CountableOccupationFock

/-! The algebraic bc ghost modes with the vacuum cuts at minus one and two. -/

open D5.S3.Quantum.Fermionic.CountableOccupationFock

noncomputable section
namespace D5.S3.Quantum.Fermionic.BcGhostFock

def b (m : ℤ) : Module.End ℂ Fock :=
  if m ≤ -2 then create (2 * (-m-2).toNat)
  else annihilate (2 * (m+1).toNat + 1)

def c (n : ℤ) : Module.End ℂ Fock :=
  if n ≤ 1 then create (2 * (1-n).toNat + 1)
  else annihilate (2 * (n-2).toNat)

/-- Each of the four branches is the exact inverse of its natural occupation index. -/
theorem mode_correspondence (j : ℕ) :
    b (-(j : ℤ)-2) = create (2*j) ∧
    c ((j : ℤ)+2) = annihilate (2*j) ∧
    c (1-(j : ℤ)) = create (2*j+1) ∧
    b ((j : ℤ)-1) = annihilate (2*j+1) := by
  have h₁ : -(j : ℤ)-2 ≤ -2 := by omega
  have h₂ : ¬((j : ℤ)+2 ≤ 1) := by omega
  have h₃ : 1-(j : ℤ) ≤ 1 := by omega
  have h₄ : ¬((j : ℤ)-1 ≤ -2) := by omega
  simp [b, c, h₁, h₂, h₃, h₄]

theorem ghost_b_car (m n : ℤ) : b m * b n + b n * b m = 0 := by
  by_cases hm : m ≤ -2 <;> by_cases hn : n ≤ -2
  · simpa [b, hm, hn, mode] using car (2*(-m-2).toNat) (2*(-n-2).toNat) true true
  · have he : 2*(-m-2).toNat ≠ 2*(n+1).toNat+1 := by omega
    simpa [b, hm, hn, mode, he] using car (2*(-m-2).toNat) (2*(n+1).toNat+1) true false
  · have he : 2*(m+1).toNat+1 ≠ 2*(-n-2).toNat := by omega
    simpa [b, hm, hn, mode, he] using car (2*(m+1).toNat+1) (2*(-n-2).toNat) false true
  · simpa [b, hm, hn, mode] using car (2*(m+1).toNat+1) (2*(n+1).toNat+1) false false

theorem ghost_c_car (m n : ℤ) : c m * c n + c n * c m = 0 := by
  by_cases hm : m ≤ 1 <;> by_cases hn : n ≤ 1
  · simpa [c, hm, hn, mode] using car (2*(1-m).toNat+1) (2*(1-n).toNat+1) true true
  · have he : 2*(1-m).toNat+1 ≠ 2*(n-2).toNat := by omega
    simpa [c, hm, hn, mode, he] using car (2*(1-m).toNat+1) (2*(n-2).toNat) true false
  · have he : 2*(m-2).toNat ≠ 2*(1-n).toNat+1 := by omega
    simpa [c, hm, hn, mode, he] using car (2*(m-2).toNat) (2*(1-n).toNat+1) false true
  · simpa [c, hm, hn, mode] using car (2*(m-2).toNat) (2*(n-2).toNat) false false

theorem ghost_mixed_car (m n : ℤ) :
    b m * c n + c n * b m =
      if m+n = 0 then (1 : Module.End ℂ Fock) else 0 := by
  by_cases hm : m ≤ -2 <;> by_cases hn : n ≤ 1
  · have hz : m+n ≠ 0 := by omega
    simpa [b, c, hm, hn, mode, hz] using car (2*(-m-2).toNat) (2*(1-n).toNat+1) true true
  · have he : 2*(-m-2).toNat = 2*(n-2).toNat ↔ m+n = 0 := by omega
    simpa [b, c, hm, hn, mode, he] using car (2*(-m-2).toNat) (2*(n-2).toNat) true false
  · have he : (m+1).toNat = (1-n).toNat ↔ m+n = 0 := by omega
    simpa [b, c, hm, hn, mode, he] using car (2*(m+1).toNat+1) (2*(1-n).toNat+1) false true
  · have hz : m+n ≠ 0 := by omega
    simpa [b, c, hm, hn, mode, hz] using car (2*(m+1).toNat+1) (2*(n-2).toNat) false false

theorem ghost_vacuum :
    (∀ m : ℤ, -1 ≤ m → b m vacuum = 0) ∧
    (∀ n : ℤ, 2 ≤ n → c n vacuum = 0) ∧
    c 1 vacuum = ket {1} ∧ c 0 vacuum = ket {3} ∧
    c 1 vacuum ≠ 0 ∧ c 0 vacuum ≠ 0 := by
  have hc₁ : c 1 vacuum = ket {1} := by norm_num [c, create_vacuum]
  have hc₀ : c 0 vacuum = ket {3} := by norm_num [c, create_vacuum]
  refine ⟨?_, ?_, hc₁, hc₀, ?_, ?_⟩
  · intro m hm
    have h : ¬m ≤ -2 := by omega
    simp [b, h, annihilate_vacuum]
  · intro n hn
    have h : ¬n ≤ 1 := by omega
    simp [c, h, annihilate_vacuum]
  · rw [hc₁]; simp [ket]
  · rw [hc₀]; simp [ket]

theorem ghost_parity (m : ℤ) :
    parity * b m + b m * parity = 0 ∧
    parity * c m + c m * parity = 0 := by
  constructor
  · by_cases hm : m ≤ -2
    · simpa [b, hm, mode] using parity_odd (2*(-m-2).toNat) true
    · simpa [b, hm, mode] using parity_odd (2*(m+1).toNat+1) false
  · by_cases hm : m ≤ 1
    · simpa [c, hm, mode] using parity_odd (2*(1-m).toNat+1) true
    · simpa [c, hm, mode] using parity_odd (2*(m-2).toNat) false


/-- The two full ghost vacuum cuts enumerate exactly the source annihilators. -/
theorem ghost_common_annihilator_kernel (v : Fock) :
    ((∀ m : ℤ, -1 ≤ m → b m v = 0) ∧
      (∀ n : ℤ, 2 ≤ n → c n v = 0)) ↔ ∃ α : ℂ, v = α • vacuum := by
  constructor
  · rintro ⟨hb, hc⟩
    apply (common_annihilator_kernel v).mp
    intro j
    by_cases he : j % 2 = 0
    · have hj : j = 2 * (j / 2) := by omega
      rw [hj, ← (mode_correspondence (j / 2)).2.1]
      exact hc ((j / 2 : ℕ) + 2) (by omega)
    · have hj : j = 2 * (j / 2) + 1 := by omega
      rw [hj, ← (mode_correspondence (j / 2)).2.2.2]
      exact hb ((j / 2 : ℕ) - 1) (by omega)
  · rintro ⟨α, rfl⟩
    constructor
    · intro m hm
      rw [map_smul, ghost_vacuum.1 m hm, smul_zero]
    · intro n hn
      rw [map_smul, ghost_vacuum.2.1 n hn, smul_zero]

/-- Every endomorphism commuting with all integer ghost modes is scalar on every state. -/
theorem scalar_commutant (A : Module.End ℂ Fock)
    (hb : ∀ m : ℤ, A * b m = b m * A)
    (hc : ∀ n : ℤ, A * c n = c n * A) :
    ∃ α : ℂ, A = α • (1 : Module.End ℂ Fock) := by
  have hAvac : (∀ m : ℤ, -1 ≤ m → b m (A vacuum) = 0) ∧
      (∀ n : ℤ, 2 ≤ n → c n (A vacuum) = 0) := by
    constructor
    · intro m hm
      calc
        b m (A vacuum) = A (b m vacuum) := (LinearMap.congr_fun (hb m) vacuum).symm
        _ = 0 := by rw [ghost_vacuum.1 m hm, map_zero]
    · intro n hn
      calc
        c n (A vacuum) = A (c n vacuum) := (LinearMap.congr_fun (hc n) vacuum).symm
        _ = 0 := by rw [ghost_vacuum.2.1 n hn, map_zero]
  obtain ⟨α, hvac⟩ := (ghost_common_annihilator_kernel (A vacuum)).mp hAvac
  refine ⟨α, eq_scalar_of_creator_commutation A α hvac ?_⟩
  intro j
  by_cases he : j % 2 = 0
  · have hj : j = 2 * (j / 2) := by omega
    rw [hj, ← (mode_correspondence (j / 2)).1]
    exact hb (-(j / 2 : ℕ) - 2)
  · have hj : j = 2 * (j / 2) + 1 := by omega
    rw [hj, ← (mode_correspondence (j / 2)).2.2.1]
    exact hc (1 - (j / 2 : ℕ))

end D5.S3.Quantum.Fermionic.BcGhostFock

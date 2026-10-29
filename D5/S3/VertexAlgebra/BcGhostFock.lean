/- GID: D5/S3/VertexAlgebra/BcGhostFock
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BcGhostFock
   mirror-E: none(waiver:algebraic-ghost-car)
   anchors: []
   utility: none
   digest: Integer bc modes on countable occupation Fock space obey ghost CAR. -/

import D5.S3.Quantum.Fermionic.CountableOccupationFock

/-! The algebraic bc ghost modes with the vacuum cuts at minus one and two. -/

open D5.S3.Quantum.Fermionic.CountableOccupationFock

noncomputable section
namespace D5.S3.VertexAlgebra.BcGhostFock

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

end D5.S3.VertexAlgebra.BcGhostFock

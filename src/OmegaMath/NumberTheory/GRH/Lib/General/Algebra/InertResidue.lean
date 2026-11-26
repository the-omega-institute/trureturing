import OmegaMath.NumberTheory.GRH.Lib.Adelic.Adeles.AdeleIdempotent
import OmegaMath.NumberTheory.GRH.Lib.Weil.Construction.GaussSumSign
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! A general count of the fixed points of an involution on a finite field, applied to finite places
of a stably unramified CM field: a place with w̄ = w has norm r ^ 2 with r ≡ 3 mod 4, so a place of
prime norm is split. -/

open Nat NumberField StablyUnram FiniteField Ideal Quotient Fint selfAdjoint

/-- A finite field with an involution that moves a square root of `-1` has `r ^ 2` elements,
where `r`, the number of fixed points, is `3` modulo `4`. -/
lemma card_selfAdjoint {k} [Field k] [StarRing k] [Finite k] {i : k} (a : i * i = -1) (h :
    star i ≠ i) : .card (selfAdjoint k) ^ 2 = Nat.card k ∧ .card (selfAdjoint k) % 4 = 3 := by
  rw [sq, ← card_prod]
  use card_congr ⟨fun (x, y) ↦ (x - i * y) / 2, fun z ↦ ⟨⟨_, .add_star_self z⟩, _, .add_star_self
    (i * z)⟩, ?_, ?_⟩, Fintype.card_eq_nat_card ▸ isSquare_neg_one_iff.not_left.1 ?_ <;> simp_intro
    x [mem_iff, IsSquare, Subtype.ext_iff] <;> grind [star_mul, star_inj, star_neg, star_one]

variable {E} [Field E] [NumberField E] [IsCMField E] [StablyUnram E] {w : FinPlace E}

/-- For stably unramified E and a finite place w with w = w̄, the norm of w is r² for a natural
number r ≡ 3 mod 4. -/
lemma StablyUnram.exists_sq_eq_q_of_inert (h : star w = w) : ∃ r, r ^ 2 = w.q ∧ r % 4 = 3 := by
  obtain ⟨i, ω, a, b, ⟨⟩⟩ := ‹StablyUnram E›.exists_i_c₀
  let := Quotient.field w.1
  apply_fun Ideal.Quotient.mk w at *
  exact ⟨_, @card_selfAdjoint _ _ (starRingOfInvolution (quotientMap _ _ congr($h.1).ge)
    (Quot.ind (congrArg _ <| star_star ·))) _ i a
    (b.trans_ne (by grind [one_add_one_eq_two, mem_star_place, eq_zero_iff_mem]))⟩

lemma isSplit_of_q_prime (h : w.q.Prime) :
  w.IsSplit := by grind [exists_sq_eq_q_of_inert, h.pow_eq_iff]

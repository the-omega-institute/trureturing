/- GID: D5/S1/Words/RankOneMorphismIterationBoundResidues
   generality: G
   mirror-B: D5/B/S1/Words/RankOneMorphismIterationBoundResidues
   mirror-E: none(waiver:one-sided-source-occurrence-residues)
   anchors: []
   digest: One-sided occurrence residue subgroup and cosets of the actual indexed fixed word. -/
import D5.S1.Words.RankOneMorphismIterationBoundPrimitivity
import Mathlib.FieldTheory.Finite.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.RankOneMorphismIterationBound
namespace Parameters
variable {f : Morphism} (p : Parameters f)

def occurrenceResidues (q : ℕ) (γ : State f) : Set (ZMod q) :=
  {a | ∃ i : ℕ, p.indexedFixedWord i = γ ∧ (i : ZMod q) = a}

private theorem coprime_power_one (q : ℕ) (hcop : Nat.Coprime p.lam q) :
    (p.lam : ZMod q) ^ q.totient = 1 := by
  have h := (ZMod.natCast_eq_natCast_iff _ _ q).mpr (Nat.ModEq.pow_totient hcop)
  simpa using h

private theorem long_power (T j : ℕ) (hT : 0 < T) : j < p.lam^(T*(j+1)) := by
  have h1 : j < p.lam^(j+1) :=
    (Nat.lt_two_pow_self : j < 2^j).trans_le
      ((Nat.pow_le_pow_left p.lam_ge_two j).trans
        (Nat.pow_le_pow_right (by have := p.lam_ge_two; omega) (Nat.le_succ j)))
  have he : j+1 ≤ T*(j+1) := by nlinarith
  exact h1.trans_le (Nat.pow_le_pow_right (by have := p.lam_ge_two; omega) he)

/-- Every actual return translates every occurrence residue, using only
    forward copies of the actual one-sided fixed word. -/
theorem occurrence_translate (hp : Prolongable f) (q : ℕ) (hq : 0 < q)
    (hcop : Nat.Coprime p.lam q) (γ : State f) {a b : ZMod q}
    (ha : a ∈ p.occurrenceResidues q (p.indexedFixedWord 0))
    (hb : b ∈ p.occurrenceResidues q γ) : a+b ∈ p.occurrenceResidues q γ := by
  obtain ⟨i,hi,rfl⟩ := ha
  obtain ⟨j,hj,rfl⟩ := hb
  let T := q.totient
  let k := T*(j+1)
  have hT : 0 < T := Nat.totient_pos.mpr hq
  have hjk : j < p.lam^k := p.long_power T j hT
  have hzero := p.indexedFixedWord_copy hp 0 k j hjk
  simp only [mul_zero, zero_add] at hzero
  have hcopy := p.indexedFixedWord_copy hp i k j hjk
  rw [hi, ← hzero, hj] at hcopy
  refine ⟨p.lam^k*i+j,hcopy,?_⟩
  have hk : ((p.lam^k : ℕ) : ZMod q) = 1 := by
    simp only [k, T, pow_mul, Nat.cast_pow, p.coprime_power_one q hcop, one_pow]
  simp only [Nat.cast_add, Nat.cast_mul, hk, one_mul]

/-- The source return residues form an additive subgroup, including q=1. -/
def returnSubgroup (hp : Prolongable f) (q : ℕ) (hq : 0 < q)
    (hcop : Nat.Coprime p.lam q) : AddSubgroup (ZMod q) where
  carrier := p.occurrenceResidues q (p.indexedFixedWord 0)
  zero_mem' := ⟨0,rfl,by simp⟩
  add_mem' := p.occurrence_translate hp q hq hcop (p.indexedFixedWord 0)
  neg_mem' := by
    intro a ha
    have hzero : (0 : ZMod q) ∈ p.occurrenceResidues q (p.indexedFixedWord 0) := ⟨0,rfl,by simp⟩
    have hn : ∀ n : ℕ, n • a ∈ p.occurrenceResidues q (p.indexedFixedWord 0) := by
      intro n
      induction n with
      | zero => simpa using hzero
      | succ n ih =>
        simpa only [succ_nsmul] using p.occurrence_translate hp q hq hcop (p.indexedFixedWord 0) ih ha
    have hq0 : q • a = 0 := by simp [nsmul_eq_mul, ZMod.natCast_self]
    have he : (q-1) • a = -a := by
      apply eq_neg_of_add_eq_zero_left
      rw [← succ_nsmul, Nat.sub_add_cancel (by omega : 1 ≤ q)]
      exact hq0
    exact he ▸ hn (q-1)

/-- An occurrence at the initial symbol is retained at every iterate. -/
theorem initial_mem_uniform (hp : Prolongable f) (k : ℕ) :
    p.indexedFixedWord 0 ∈ image p.uniform k (p.indexedFixedWord 0) := by
  have hpow : 0 < p.lam^k := pow_pos (by have := p.lam_ge_two; omega) _
  have h := p.indexedFixedWord_copy hp 0 k 0 hpow
  simp only [mul_zero, zero_add] at h
  exact List.mem_iff_getElem.mpr ⟨0,by rw [p.uniform_iter_length]; exact hpow,h.symm⟩

/-- Internal return property of the actual constructed morphism. -/
def AllStatesReturn : Prop :=
  ∀ γ : State f, ∃ k : ℕ, p.indexedFixedWord 0 ∈ image p.uniform k γ

theorem allStatesReturn : p.AllStatesReturn := by
  obtain ⟨k,hk,h⟩ := p.uniform_primitive
  intro γ
  exact ⟨k,h γ (p.indexedFixedWord 0)⟩

/-- Two occurrences of one source state differ by a source return residue. -/
theorem occurrence_difference (hp : Prolongable f) (hreturn : p.AllStatesReturn)
    (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime p.lam q) (γ : State f)
    {a b : ZMod q} (ha : a ∈ p.occurrenceResidues q γ)
    (hb : b ∈ p.occurrenceResidues q γ) : a-b ∈ p.returnSubgroup hp q hq hcop := by
  obtain ⟨i,hi,rfl⟩ := ha
  obtain ⟨j,hj,rfl⟩ := hb
  obtain ⟨e,he⟩ := hreturn γ
  let T := q.totient
  let k := T*(e+1)
  have hT : 0 < T := Nat.totient_pos.mpr hq
  have hek : e ≤ k := by dsimp [k]; nlinarith
  have hm : p.indexedFixedWord 0 ∈ image p.uniform k γ := by
    have hmem : p.indexedFixedWord 0 ∈ subst (image p.uniform (k-e)) (image p.uniform e γ) :=
      List.mem_flatMap.mpr ⟨p.indexedFixedWord 0,he,p.initial_mem_uniform hp (k-e)⟩
    rw [← image_add, Nat.sub_add_cancel hek] at hmem
    exact hmem
  obtain ⟨offset,hoff,hstate⟩ := List.mem_iff_getElem.mp hm
  have hoff' : offset < p.lam^k := by simpa only [p.uniform_iter_length] using hoff
  have hci := p.indexedFixedWord_copy hp i k offset hoff'
  have hcj := p.indexedFixedWord_copy hp j k offset hoff'
  rw [hi,hstate] at hci
  rw [hj,hstate] at hcj
  have hai : ((p.lam^k*i+offset : ℕ) : ZMod q) ∈ p.returnSubgroup hp q hq hcop :=
    ⟨_,hci,rfl⟩
  have haj : ((p.lam^k*j+offset : ℕ) : ZMod q) ∈ p.returnSubgroup hp q hq hcop :=
    ⟨_,hcj,rfl⟩
  have hdiff := (p.returnSubgroup hp q hq hcop).sub_mem hai haj
  have hk : ((p.lam^k : ℕ) : ZMod q) = 1 := by
    simp only [k,T,pow_mul,Nat.cast_pow,p.coprime_power_one q hcop,one_pow]
  simpa only [Nat.cast_add,Nat.cast_mul,hk,one_mul,add_sub_add_right_eq_sub] using hdiff

/-- Exact coset membership for any actual occurrence, with all positions one-sided. -/
theorem occurrence_coset (hp : Prolongable f) (hreturn : p.AllStatesReturn)
    (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime p.lam q) (γ : State f)
    {b : ZMod q} (hb : b ∈ p.occurrenceResidues q γ) (a : ZMod q) :
    a ∈ p.occurrenceResidues q γ ↔ a-b ∈ p.returnSubgroup hp q hq hcop := by
  constructor
  · intro ha; exact p.occurrence_difference hp hreturn q hq hcop γ ha hb
  · intro hdiff
    have h := p.occurrence_translate hp q hq hcop γ hdiff hb
    simpa only [sub_add_cancel] using h

/-- A positive actual return is constructed from a copy at position one. -/
theorem positive_return (hp : Prolongable f) :
    ∃ i : ℕ, 0 < i ∧ p.indexedFixedWord i = p.indexedFixedWord 0 := by
  obtain ⟨k,hk,h⟩ := p.uniform_primitive
  obtain ⟨j,hj,hs⟩ := List.mem_iff_getElem.mp
    (h (p.indexedFixedWord 1) (p.indexedFixedWord 0))
  have hj' : j < p.lam^k := by simpa only [p.uniform_iter_length] using hj
  refine ⟨p.lam^k+j,by have := pow_pos (by have := p.lam_ge_two; omega : 0 < p.lam) k; omega,?_⟩
  simpa only [mul_one,hs] using p.indexedFixedWord_copy hp 1 k j hj'

/-- A positive return with zero residue supplies genuinely one-sided recurrence. -/
theorem positive_zero_return (hp : Prolongable f) (q : ℕ) (hq : 0 < q)
    (hcop : Nat.Coprime p.lam q) :
    ∃ J : ℕ, 0 < J ∧ p.indexedFixedWord J = p.indexedFixedWord 0 ∧ (J : ZMod q) = 0 := by
  obtain ⟨i,hi,hstate⟩ := p.positive_return hp
  have hmem : (i : ZMod q) ∈ p.returnSubgroup hp q hq hcop := ⟨i,hstate,rfl⟩
  obtain ⟨j,hj,heq⟩ := (p.returnSubgroup hp q hq hcop).neg_mem hmem
  let k := q.totient*(j+1)
  have hjk : j < p.lam^k := p.long_power q.totient j (Nat.totient_pos.mpr hq)
  have hzero := p.indexedFixedWord_copy hp 0 k j hjk
  simp only [mul_zero,zero_add] at hzero
  have hcopy := p.indexedFixedWord_copy hp i k j hjk
  simp only [hstate,← hzero,hj] at hcopy
  have hk : ((p.lam^k : ℕ) : ZMod q) = 1 := by
    simp only [k,pow_mul,Nat.cast_pow,p.coprime_power_one q hcop,one_pow]
  refine ⟨p.lam^k*i+j,?_,hcopy,?_⟩
  · have hh : 0 < p.lam^k := pow_pos (by have := p.lam_ge_two; omega) _
    exact Nat.add_pos_left (Nat.mul_pos hh hi) _
  · simp only [Nat.cast_add,Nat.cast_mul,hk,one_mul,heq,add_neg_cancel]

/-- Every actual occurrence residue occurs arbitrarily far to the right,
    including modulo one. No two-sided extension is used. -/
theorem occurrence_tail (hp : Prolongable f) (q : ℕ) (hq : 0 < q)
    (hcop : Nat.Coprime p.lam q) (γ : State f) {a : ZMod q}
    (ha : a ∈ p.occurrenceResidues q γ) (R : ℕ) :
    ∃ i : ℕ, R ≤ i ∧ p.indexedFixedWord i = γ ∧ (i : ZMod q) = a := by
  obtain ⟨j,hj,rfl⟩ := ha
  obtain ⟨J,hJ,hstate,hres⟩ := p.positive_zero_return hp q hq hcop
  let k := q.totient*(R+j+1)
  have hbig : R+j < p.lam^k := p.long_power q.totient (R+j) (Nat.totient_pos.mpr hq)
  have hjk : j < p.lam^k := by omega
  have hzero := p.indexedFixedWord_copy hp 0 k j hjk
  simp only [mul_zero,zero_add] at hzero
  have hcopy := p.indexedFixedWord_copy hp J k j hjk
  simp only [hstate,← hzero,hj] at hcopy
  refine ⟨p.lam^k*J+j,?_,hcopy,?_⟩
  · have hh : p.lam^k ≤ p.lam^k*J := by
      simpa using Nat.mul_le_mul_left (p.lam^k) (show 1 ≤ J by omega)
    omega
  · simp only [Nat.cast_add,Nat.cast_mul,hres,mul_zero,zero_add]

end Parameters
end D5.S1.Words.RankOneMorphismIterationBound

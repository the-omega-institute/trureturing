/- GID: D5/S3/Arith/Additive/GreathouseA359506XorBound
   generality: E
   mirror-B: D5/B/S3/Arith/Additive/GreathouseA359506XorBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Every least zero-XOR ender satisfies Greathouse's sharp five-thirds bound. -/

/-
result:
  proof_shape: bind-only
  escape_witness: none
  admission_basis: open-problem-resolution (#23097; Proved)
  Direct frozen dependencies: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/25579.
The claim retains the source minimum condition and XOR fold literally, with the
fold written inline rather than duplicating the private xs owner in
D5.S0.Certificates.Games.EllisThanatipanondaCutFamilyA; proofs use List.foldr
and Mathlib IsLeast, whose correspondence is definitional.
All declarations have Direct frozen dependencies: none.
The exact-minimum proofs use the arbitrary-list invariant xorFold_span. The
weaker conclusions bounded_ender and result also follow from the explicit
bounded constructions and Nat.find, without those lower-bound proofs; their
bind-only labels account for this bypass after same-delivery expansion.
Definitions HasZeroXorSequence and claim have no proof shape.
Private theorem proof_shape and consumer(s):
  sequence_iff: bind-only; consumers: regular_construction, power_construction,
    regular_lower, power_lower, bounded_ender.
  xor_blocks: bind-only; consumers: regular_construction, power_construction.
  even_adjacent_xor: bind-only; consumers: regular_construction.
  regular_construction: bind-only; consumers: regular_least.
  power_construction: bind-only; consumers: power_least.
  xorFold_div: bind-only; consumers: regular_lower, power_lower.
  xorFold_span: content; escape_witness: xorFold_span; consumers: regular_lower, power_lower.
  sequence_tail_bounds: bind-only; consumers: regular_lower, power_lower.
  div_between: bind-only; consumers: regular_lower.
  regular_lower: content; escape_witness: xorFold_span; consumers: regular_least.
  power_lower: content; escape_witness: xorFold_span; consumers: power_least.
  regular_least: content; escape_witness: regular_lower; consumers: bounded_ender.
  power_least: content; escape_witness: power_lower; consumers: bounded_ender.
  bounded_ender: bind-only; consumers: result.
Utility none: arbitrary natural indices and finite lists of unrestricted length.
-/

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Bitwise

namespace D5.S3.Arith.Additive.GreathouseA359506XorBound

/-- A finite strictly increasing sequence starts at `n`, ends at `m`, and has XOR zero. -/
def HasZeroXorSequence (n m : ℕ) : Prop :=
  ∃ bs : List ℕ,
    bs.Pairwise (· < ·) ∧
      bs ≠ [] ∧
      bs.headD 0 = n ∧
      bs.getLastD 0 = m ∧
      (List.foldr (fun a b => a ^^^ b) 0 bs) = 0

/-- The A359506 assertion, with existence of the implicitly defined minimum made explicit. -/
def claim : Prop :=
  ∀ n : ℕ, ∃ m : ℕ,
    (HasZeroXorSequence n m ∧
      ∀ m' : ℕ, HasZeroXorSequence n m' → m ≤ m') ∧ 3 * m ≤ 5 * (n + 1)

end D5.S3.Arith.Additive.GreathouseA359506XorBound

namespace D5.S3.Arith.Additive.GreathouseA359506XorBound

private theorem sequence_iff (n m : ℕ) :
    HasZeroXorSequence n m ↔ ∃ bs : List ℕ,
      bs.Pairwise (· < ·) ∧ bs.head? = some n ∧ bs.getLast? = some m ∧
        (List.foldr (fun a b => a ^^^ b) 0 bs) = 0 := by
  unfold HasZeroXorSequence
  apply exists_congr
  intro bs
  cases bs with
  | nil => simp
  | cons a bs =>
    simp [List.getLastD_eq_getLast?,
      List.getLast?_eq_some_getLast (by simp : a :: bs ≠ [])]

private theorem xor_blocks (s a b r t : ℕ) (hr : r < 2^s) (ht : t < 2^s) :
    (2^s*a+r) ^^^ (2^s*b+t) = 2^s*(a ^^^ b)+(r ^^^ t) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_mul_add _ hr,
    Nat.testBit_two_pow_mul_add _ ht,
    Nat.testBit_two_pow_mul_add _ (Nat.xor_lt_two_pow hr ht)]
  split_ifs <;> simp [Nat.testBit_xor]

private theorem even_adjacent_xor (k : ℕ) : (2*k) ^^^ (2*k+1) = 1 := by
  simpa [Nat.bit] using Nat.xor_bit false k true k

private theorem regular_construction (s k : ℕ) :
    HasZeroXorSequence (2^s*(2*k+1)-1) (2^s*(2*k+3)) := by
  apply (sequence_iff _ _).2
  let q := 2^s
  have hq : 0 < q := Nat.two_pow_pos s
  have hr : q-1 < 2^s := Nat.sub_one_lt_of_lt hq
  have hp : q*(2*k)+ (q-1) = q*(2*k+1)-1 := by simp only [Nat.mul_add, Nat.mul_one]; omega
  have hx₁ : (q*(2*k)+ (q-1)) ^^^ (q*(2*k+1)+(q-1)) = q := by
    rw [xor_blocks s (2*k) (2*k+1) (q-1) (q-1) hr hr]
    simp [even_adjacent_xor, q]
  have hx₂ : (q*(2*k+2)) ^^^ (q*(2*k+3)) = q := by
    have he := xor_blocks s (2*(k+1)) (2*(k+1)+1) 0 0 (Nat.two_pow_pos s) (Nat.two_pow_pos s)
    rw [even_adjacent_xor] at he
    simpa [q, Nat.mul_add, Nat.add_assoc] using he
  refine ⟨[q*(2*k)+ (q-1), q*(2*k+1)+(q-1), q*(2*k+2), q*(2*k+3)], ?_, ?_, ?_, ?_⟩
  · simp [List.pairwise_cons]; simp only [Nat.mul_add, Nat.mul_one]; omega
  · simpa only [List.head?_cons] using congrArg some hp
  · rfl
  · simp only [List.foldr_cons, List.foldr_nil, Nat.xor_zero]
    rw [← Nat.xor_assoc, hx₁, hx₂, Nat.xor_self]

private theorem power_construction (s : ℕ) :
    HasZeroXorSequence (2^(s+1)-1) (3*2^s) := by
  apply (sequence_iff _ _).2
  let h := 2^s
  have hh : 0 < h := Nat.two_pow_pos s
  have hr : h-1 < 2^s := Nat.sub_one_lt_of_lt hh
  have hx : (h+(h-1)) ^^^ (2*h+(h-1)) = 3*h := by
    have he := xor_blocks s 1 2 (h-1) (h-1) hr hr
    simpa [h, Nat.mul_comm] using he
  refine ⟨[h+(h-1), 2*h+(h-1), 3*h], ?_, ?_, ?_, ?_⟩
  · simp [List.pairwise_cons]; omega
  · simp only [List.head?_cons, Option.some.injEq]
    dsimp [h]
    rw [pow_succ]
    omega
  · rfl
  · simp only [List.foldr_cons, List.foldr_nil, Nat.xor_zero]
    rw [← Nat.xor_assoc, hx, Nat.xor_self]

private theorem xorFold_div (s : ℕ) (bs : List ℕ) :
    (List.foldr (fun a b => a ^^^ b) 0 bs) / 2^s = (List.foldr (fun a b => a ^^^ b) 0) (bs.map (fun x => x / 2^s)) := by
  simpa only [Nat.zero_div] using (List.foldr_map_hom (g := fun n : ℕ => n / 2^s) (f := fun a b : ℕ => a ^^^ b)
    (f' := fun a b : ℕ => a ^^^ b) (a := 0) (l := bs)
    (fun a b => (Nat.xor_div_two_pow (a := a) (b := b) (n := s)).symm)).symm

private theorem xorFold_span (a b : ℕ) (bs : List ℕ)
    (hbs : ∀ x ∈ bs, x = a ∨ x = b) :
    (List.foldr (fun a b => a ^^^ b) 0 bs) = 0 ∨ (List.foldr (fun a b => a ^^^ b) 0 bs) = a ∨ (List.foldr (fun a b => a ^^^ b) 0 bs) = b ∨ (List.foldr (fun a b => a ^^^ b) 0 bs) = a ^^^ b := by
  induction bs with
  | nil => exact Or.inl rfl
  | cons x xs ih =>
    have ht : ∀ y ∈ xs, y = a ∨ y = b := fun y hy => hbs y (List.mem_cons_of_mem _ hy)
    change (x ^^^ (List.foldr (fun a b => a ^^^ b) 0 xs) = 0 ∨ x ^^^ (List.foldr (fun a b => a ^^^ b) 0 xs) = a ∨
      x ^^^ (List.foldr (fun a b => a ^^^ b) 0 xs) = b ∨ x ^^^ (List.foldr (fun a b => a ^^^ b) 0 xs) = a ^^^ b)
    rcases hbs x (by simp) with hx | hx
    all_goals
      rcases ih ht with h | h | h | h
      all_goals
        rw [hx, h]
        simp [Nat.xor_comm, Nat.xor_left_comm]

private theorem sequence_tail_bounds {n m : ℕ} {bs : List ℕ}
    (hpair : (n :: bs).Pairwise (· < ·)) (hlast : (n :: bs).getLast? = some m) :
    ∀ x ∈ bs, n < x ∧ x ≤ m := by
  intro x hx
  refine ⟨(List.pairwise_cons.mp hpair).1 x hx, ?_⟩
  have hle : (n :: bs).Pairwise (· ≤ ·) := hpair.imp (fun h => Nat.le_of_lt h)
  have h := hle.rel_getLast (List.mem_cons_of_mem n hx)
  simpa only [List.getLast_of_getLast?_eq_some hlast] using h

private theorem div_between {q x v : ℕ} (hq : 0 < q)
    (hlo : q*v ≤ x) (hhi : x < q*(v+2)) :
    x/q = v ∨ x/q = v+1 := by
  have h₁ : v ≤ x/q := (Nat.le_div_iff_mul_le hq).2 (by simpa [Nat.mul_comm] using hlo)
  have h₂ : x/q < v+2 := (Nat.div_lt_iff_lt_mul hq).2 (by simpa [Nat.mul_comm] using hhi)
  omega

private theorem regular_lower (s k m : ℕ) (hk : 1 ≤ k)
    (hseq : HasZeroXorSequence (2^s*(2*k+1)-1) m) :
    2^s*(2*k+3) ≤ m := by
  by_contra hm
  have hm' : m < 2^s*(2*k+3) := Nat.lt_of_not_le hm
  let q := 2^s
  change m < q*(2*k+3) at hm'
  have hq : 0 < q := Nat.two_pow_pos s
  have hr : q-1 < q := Nat.sub_one_lt_of_lt hq
  rcases (sequence_iff _ _).1 hseq with ⟨bs,hpair,hhead,hlast,hxor⟩
  cases bs with
  | nil => simp at hhead
  | cons n bs =>
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst n
    have hb := sequence_tail_bounds hpair hlast
    have hmap : ∀ y ∈ bs.map (fun x => x/q), y = 2*k+1 ∨ y = 2*k+2 := by
      intro y hy
      rcases List.mem_map.mp hy with ⟨x,hx,rfl⟩
      have hxb := hb x hx
      change q*(2*k+1)-1 < x ∧ x ≤ m at hxb
      apply div_between hq
      · omega
      · simpa only [Nat.add_assoc] using lt_of_le_of_lt hxb.2 hm'
    have hs := xorFold_span (2*k+1) (2*k+2) (bs.map (fun x => x/q)) hmap
    have hstart : (q*(2*k+1)-1)/q = 2*k := by
      have hp : q*(2*k+1)-1 = q*(2*k)+(q-1) := by simp only [Nat.mul_add, Nat.mul_one]; omega
      rw [hp, Nat.mul_add_div hq, Nat.div_eq_of_lt hr, Nat.add_zero]
    have heq : 2*k = (List.foldr (fun a b => a ^^^ b) 0) (bs.map (fun x => x/q)) := by
      have he := congrArg (fun x : ℕ => x/q) hxor
      rw [show (List.foldr (fun a b => a ^^^ b) 0) ((q*(2*k+1)-1) :: bs) = (q*(2*k+1)-1) ^^^ (List.foldr (fun a b => a ^^^ b) 0 bs) from rfl,
        Nat.xor_div_two_pow, hstart, xorFold_div s bs] at he
      have hc := congrArg (fun x : ℕ => (2*k) ^^^ x) he
      simpa only [Nat.xor_xor_cancel_left, Nat.zero_div, Nat.xor_zero] using hc.symm
    rw [← heq] at hs
    rcases hs with hz | ha | hb | hab
    · omega
    · omega
    · omega
    · have he := congrArg (fun x : ℕ => x%2) hab
      rw [Nat.xor_mod_two_eq] at he
      omega

private theorem power_lower (s m : ℕ)
    (hseq : HasZeroXorSequence (2^(s+1)-1) m) : 3*2^s ≤ m := by
  by_contra hm
  have hm' : m < 3*2^s := Nat.lt_of_not_le hm
  let h := 2^s
  have hh : 0 < h := Nat.two_pow_pos s
  have hr : h-1 < h := Nat.sub_one_lt_of_lt hh
  have hn : 2^(s+1)-1 = h+(h-1) := by dsimp [h]; rw [pow_succ]; omega
  rcases (sequence_iff _ _).1 hseq with ⟨bs,hpair,hhead,hlast,hxor⟩
  cases bs with
  | nil => simp at hhead
  | cons n bs =>
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst n
    have hb := sequence_tail_bounds hpair hlast
    have hmap : ∀ y ∈ bs.map (fun x => x/h), y = 2 ∨ y = 2 := by
      intro y hy
      rcases List.mem_map.mp hy with ⟨x,hx,rfl⟩
      have hxb := hb x hx
      have hlo : 2*h ≤ x := by rw [hn] at hxb; omega
      have hhi : x < 3*h := lt_of_le_of_lt hxb.2 hm'
      have h₁ : 2 ≤ x/h := (Nat.le_div_iff_mul_le hh).2 hlo
      have h₂ : x/h < 3 := (Nat.div_lt_iff_lt_mul hh).2 hhi
      left; omega
    have hs := xorFold_span 2 2 (bs.map (fun x => x/h)) hmap
    have hstart : (2^(s+1)-1)/h = 1 := by
      rw [hn, Nat.add_div_left (h-1) hh, Nat.div_eq_of_lt hr]
    have heq : 1 = (List.foldr (fun a b => a ^^^ b) 0) (bs.map (fun x => x/h)) := by
      have he := congrArg (fun x : ℕ => x/h) hxor
      rw [show (List.foldr (fun a b => a ^^^ b) 0) ((2^(s+1)-1) :: bs) = (2^(s+1)-1) ^^^ (List.foldr (fun a b => a ^^^ b) 0 bs) from rfl,
        Nat.xor_div_two_pow, hstart, xorFold_div s bs] at he
      have hc := congrArg (fun x : ℕ => 1 ^^^ x) he
      simpa only [Nat.xor_xor_cancel_left, Nat.zero_div, Nat.xor_zero] using hc.symm
    rw [← heq] at hs
    norm_num at hs

private theorem regular_least (s k : ℕ) (hk : 1 ≤ k) :
    IsLeast {m : ℕ | HasZeroXorSequence (2^s*(2*k+1)-1) m} (2^s*(2*k+3)) :=
  ⟨regular_construction s k, fun m hm => regular_lower s k m hk hm⟩

private theorem power_least (s : ℕ) : IsLeast {m : ℕ | HasZeroXorSequence (2^(s+1)-1) m} (3*2^s) :=
  ⟨power_construction s, fun m hm => power_lower s m hm⟩

private theorem bounded_ender (n : ℕ) :
    ∃ m : ℕ, IsLeast {m : ℕ | HasZeroXorSequence n m} m ∧ 3*m ≤ 5*(n+1) := by
  by_cases hn : n = 0
  · subst n
    exact ⟨0, ⟨(sequence_iff _ _).2
      ⟨[0], by simp [List.pairwise_cons], rfl, rfl, rfl⟩,
      fun _ _ => Nat.zero_le _⟩, by omega⟩
  obtain ⟨s,u,hu,he⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.succ_ne_zero n)
  change n+1 = 2^s*u at he
  rcases hu with ⟨k,hk⟩
  subst u
  by_cases hk0 : k = 0
  · subst k
    cases s with
    | zero => simp at he; omega
    | succ s =>
      refine ⟨3*2^s, ?_, ?_⟩
      · have hn' : n = 2^(s+1)-1 := by simpa using congrArg (fun x : ℕ => x-1) he
        rw [hn']
        exact power_least s
      · rw [he, pow_succ]
        omega
  · refine ⟨2^s*(2*k+3), ?_, ?_⟩
    · have hn' : n = 2^s*(2*k+1)-1 := Nat.eq_sub_of_add_eq he
      rw [hn']
      exact regular_least s k (by omega)
    · rw [he]
      have hq := Nat.two_pow_pos s
      have hmul := Nat.mul_le_mul_left (2^s) (show 3*(2*k+3) ≤ 5*(2*k+1) by omega)
      nlinarith

theorem result : claim :=
  bounded_ender

end D5.S3.Arith.Additive.GreathouseA359506XorBound

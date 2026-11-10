/- GID: D5/S3/Arith/Additive/NarayanExpandedGeneratorDeltaRefutation
   generality: I
   mirror-B: D5/B/S3/Arith/Additive/NarayanExpandedGeneratorDeltaRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Arith/Additive/NarayanExpandedGeneratorDeltaRefutation.claim; result=D5/S3/Arith/Additive/NarayanExpandedGeneratorDeltaRefutation.result; claim=D5/S3/Arith/Additive/NarayanExpandedGeneratorDeltaRefutation.claim
   digest: Expanded generators refute Narayan's delta-set formula by unit-length normalization. -/

/-
result:
  proof_shape: content
  escape_witness: none
  admission_basis: open-problem-resolution (#23185; Refuted)
  Direct frozen dependencies: none (Mathlib-only imports).
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
Source: Ashwin Narayan, arXiv:2610.02495v1, Conjecture 18.3, p. 22.
Factorizations retain every displayed generator, including ah, with nonnegative coordinates.
Delta means positive consecutive distinct length differences over all represented values.
Euclidean states retain the terminal diagonal pair, without adding any visited values.
Coordinate lengths use the literal finite-sum expression directly, avoiding a duplicate
of existing coordinate-sum owners; proofs use Mathlib finite-sum operations.
The implementation carrier is written directly as a product, without a type alias.

| declaration | proof_shape | escape_witness | direct consumer(s) |
| --- | --- | --- | --- |
| rewrite_value | bind-only | none | normalizes, trace_interval |
| rewrite_size | bind-only | none | normalizes, trace_interval |
| size_le_value | bind-only | none | normalizes |
| terminal_or_step | bind-only | none | normalizes |
| normalizes | content | none | family_intermediate |
| trace_interval | content | none | family_intermediate |
| cancel_residue | bind-only | none | terminal_unique |
| terminal_unique | bind-only | none | family_intermediate |
| pack_value | bind-only | none | expand_value, lengths_iff |
| pack_size | bind-only | none | expand_size, lengths_iff |
| pack_expand | bind-only | none | expand_value, expand_size |
| expand_value | bind-only | none | lengths_iff |
| expand_size | bind-only | none | lengths_iff |
| lengths_iff | bind-only | none | family_intermediate, family_delta |
| family_intermediate | content | none | family_delta |
| family_delta | content | none | result |
| generators_three | bind-only | none | result |
| result | content | none | none |

Content rows use the normalization and trace inductions after expanding same-module helpers.
All bind-only rows are consumed arithmetic or coordinate-transport steps.
Every row has Direct frozen dependencies: none.
-/

import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.BigOperators.Fin



namespace D5.S3.Arith.Additive.NarayanExpandedGeneratorDeltaRefutation

set_option autoImplicit false

open scoped BigOperators

/-- The tuple (a, a*h, a*h+d, ..., a*h+k*d), with every coordinate retained. -/
def generators (a h d k : ℕ) (i : Fin (k + 2)) : ℕ :=
  if i.val = 0 then a else a * h + (i.val - 1) * d

/-- The source's coordinate set Z(n), for a displayed tuple of p generators. -/
def Z {p : ℕ} (g : Fin p → ℕ) (n : ℕ) : Set (Fin p → ℕ) :=
  {z | ∑ i, z i * g i = n}

/-- The source's length set L(n). -/
def L {p : ℕ} (g : Fin p → ℕ) (n : ℕ) : Set ℕ :=
  (fun z : Fin p → ℕ => ∑ i, z i) '' Z g n

/-- The union over represented n of positive consecutive distinct length gaps. -/
def delta {p : ℕ} (g : Fin p → ℕ) : Set ℕ :=
  {q | ∃ n l₁ l₂ : ℕ, l₁ ∈ L g n ∧ l₂ ∈ L g n ∧ l₁ < l₂ ∧
    q = l₂ - l₁ ∧ ∀ l : ℕ, l ∈ L g n → ¬ (l₁ < l ∧ l < l₂)}

/-- One step of Definition 3.2; the diagonal is the terminating state. -/
def euclidStep (s : ℕ × ℕ) : ℕ × ℕ :=
  if s.2 < s.1 then (s.1 - s.2, s.2)
  else if s.1 < s.2 then (s.1, s.2 - s.1)
  else s

/-- Definition 3.2, with (x₀,y₀)=(e,d). -/
def euclidState (e d : ℕ) : ℕ → ℕ × ℕ
  | 0 => (e, d)
  | i + 1 => euclidStep (euclidState e d i)

/-- Positive coordinates encountered by the subtractive Euclidean algorithm. -/
def E (e d : ℕ) : Set ℕ :=
  {q | 0 < q ∧ ∃ i : ℕ,
    (euclidState e d i).1 = q ∨ (euclidState e d i).2 = q}

/-- Conjecture 18.3, for all positive parameters under the Section 3 restrictions. -/
def claim : Prop :=
  ∀ a h d k : ℕ, 0 < a → 0 < h → 0 < d → 0 < k →
    Nat.Coprime a d → 1 < k → k < a → 1 < h →
      delta (generators a h d k) = E (h - 1) d



private def b (a : ℕ) (i : Fin a) : ℕ := 2 * a + 2 * i.val

private def value {a : ℕ} (c : (ℕ × List (Fin a))) : ℕ :=
  a * c.1 + (c.2.map (b a)).sum

private def size {a : ℕ} (c : (ℕ × List (Fin a))) : ℕ := c.1 + c.2.length

private def Terminal {a : ℕ} (c : (ℕ × List (Fin a))) : Prop :=
  c.2 = [] ∨ ∃ i : Fin a, 0 < i.val ∧ c.2 = [i]

private inductive Rewrite {a : ℕ} (ha : 0 < a) : (ℕ × List (Fin a)) → (ℕ × List (Fin a)) → Prop
  | zero (x : ℕ) (s : List (Fin a)) :
      Rewrite ha (x, ⟨0, ha⟩ :: s) (x + 2, s)
  | small (x : ℕ) (i j : Fin a) (s : List (Fin a)) (h : i.val + j.val < a) :
      Rewrite ha (x, i :: j :: s) (x + 2, ⟨i.val + j.val, h⟩ :: s)
  | large (x : ℕ) (i j : Fin a) (s : List (Fin a)) (h : a ≤ i.val + j.val) :
      Rewrite ha (x, i :: j :: s)
        (x, ⟨0, ha⟩ :: ⟨0, ha⟩ :: ⟨i.val + j.val - a, by omega⟩ :: s)

private theorem rewrite_value {a : ℕ} {ha : 0 < a} {c d : (ℕ × List (Fin a))}
    (h : Rewrite ha c d) : value d = value c := by
  cases h with
  | zero x s => simp [value, b, Nat.mul_add]; omega
  | small x i j s h => simp [value, b, Nat.mul_add]; omega
  | large x i j s h => simp [value, b]; omega

private theorem rewrite_size {a : ℕ} {ha : 0 < a} {c d : (ℕ × List (Fin a))}
    (h : Rewrite ha c d) : size d = size c + 1 := by
  cases h <;> simp [size] <;> omega

private theorem size_le_value {a : ℕ} (ha : 0 < a) (c : (ℕ × List (Fin a))) :
    size c ≤ value c := by
  rcases c with ⟨x, s⟩
  have hs : s.length ≤ (s.map (b a)).sum := by
    have h := List.length_le_sum_of_one_le (s.map (b a)) (by
      intro n hn
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hn
      dsimp [b]
      omega)
    simpa using h
  have hx := Nat.le_mul_of_pos_left x ha
  dsimp [size, value]
  omega

private theorem terminal_or_step {a : ℕ} (ha : 0 < a) (c : (ℕ × List (Fin a))) :
    Terminal c ∨ ∃ d, Rewrite ha c d := by
  rcases c with ⟨x, s⟩
  cases s with
  | nil => exact Or.inl (Or.inl rfl)
  | cons i s =>
    cases s with
    | nil =>
      by_cases hi : i.val = 0
      · right
        have he : i = ⟨0, ha⟩ := Fin.ext hi
        subst i
        exact ⟨_, Rewrite.zero x []⟩
      · exact Or.inl (Or.inr ⟨i, Nat.pos_of_ne_zero hi, rfl⟩)
    | cons j s =>
      right
      by_cases h : i.val + j.val < a
      · exact ⟨_, Rewrite.small x i j s h⟩
      · exact ⟨_, Rewrite.large x i j s (Nat.le_of_not_gt h)⟩

private theorem normalizes {a : ℕ} (ha : 0 < a) (c : (ℕ × List (Fin a))) :
    ∃ t : (ℕ × List (Fin a)), Terminal t ∧ Relation.ReflTransGen (Rewrite ha) c t := by
  generalize hm : value c - size c = m
  induction m using Nat.strong_induction_on generalizing c with
  | h m ih =>
    rcases terminal_or_step ha c with ht | ⟨d, hd⟩
    · exact ⟨c, ht, .refl⟩
    · have hv := rewrite_value hd
      have hs := rewrite_size hd
      have hb := size_le_value ha d
      have hm' : value d - size d < m := by omega
      obtain ⟨t, ht, hreach⟩ := ih _ hm' d rfl
      exact ⟨t, ht, (Relation.ReflTransGen.single hd).trans hreach⟩

private theorem trace_interval {a : ℕ} {ha : 0 < a} {c d : (ℕ × List (Fin a))}
    (h : Relation.ReflTransGen (Rewrite ha) c d) :
    value d = value c ∧ size c ≤ size d ∧
      ∀ l : ℕ, size c ≤ l → l ≤ size d →
        ∃ u : (ℕ × List (Fin a)), value u = value c ∧ size u = l := by
  induction h with
  | refl => exact ⟨rfl, le_rfl, fun l hl hu => ⟨_, rfl, by omega⟩⟩
  | @tail d e hreach hstep ih =>
    have hv := rewrite_value hstep
    have hs := rewrite_size hstep
    refine ⟨hv.trans ih.1, by omega, ?_⟩
    intro l hl hu
    by_cases hd : l ≤ size d
    · exact ih.2.2 l hl hd
    · exact ⟨e, hv.trans ih.1, by omega⟩

private theorem cancel_residue {a r s : ℕ} (hc : Nat.Coprime a 2)
    (hr : r < a) (hs : s < a) (h : (2 * r) % a = (2 * s) % a) : r = s := by
  have he : Nat.ModEq a (2 * r) (2 * s) := h
  have he' := Nat.ModEq.cancel_left_of_coprime hc he
  simpa [Nat.ModEq, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hs] using he'

private theorem terminal_unique {a : ℕ} (ha : 0 < a) (hc : Nat.Coprime a 2)
    {c d : (ℕ × List (Fin a))} (htc : Terminal c) (htd : Terminal d)
    (hv : value c = value d) : c = d := by
  rcases c with ⟨x, s⟩
  rcases d with ⟨y, t⟩
  rcases htc with hs | ⟨i, hi, hs⟩ <;>
    rcases htd with ht | ⟨j, hj, ht⟩
  · dsimp only [Prod.snd] at hs ht
    subst s; subst t
    simp only [value, List.map_nil, List.sum_nil, add_zero] at hv
    exact Prod.ext (Nat.eq_of_mul_eq_mul_left ha hv) rfl
  · dsimp only [Prod.snd] at hs ht
    subst s; subst t
    have he := congrArg (fun n => n % a) hv
    simp [value, b, Nat.add_mod, Nat.mul_mod] at he
    have h := cancel_residue hc ha j.isLt (by simpa using he)
    omega
  · dsimp only [Prod.snd] at hs ht
    subst s; subst t
    have he := congrArg (fun n => n % a) hv
    simp [value, b, Nat.add_mod, Nat.mul_mod] at he
    have h := cancel_residue hc i.isLt ha (by simpa using he)
    omega
  · dsimp only [Prod.snd] at hs ht
    subst s; subst t
    have he := congrArg (fun n => n % a) hv
    have hij : i = j := Fin.ext (cancel_residue hc i.isLt j.isLt (by
      simpa [value, b, Nat.add_mod, Nat.mul_mod] using he))
    subst j
    have hxy : a * x = a * y := by exact Nat.add_right_cancel hv
    exact Prod.ext (Nat.eq_of_mul_eq_mul_left ha hxy) rfl


private def tuple (a : ℕ) : Fin (a + 1) → ℕ := Fin.cons a (b a)

private def pack {a : ℕ} (c : (ℕ × List (Fin a))) : Fin (a + 1) → ℕ :=
  Fin.cons c.1 (fun i => c.2.count i)

private def expand {a : ℕ} (z : Fin (a + 1) → ℕ) : (ℕ × List (Fin a)) :=
  (z 0, (List.finRange a).flatMap (fun i => List.replicate (z i.succ) i))

private theorem pack_value {a : ℕ} (c : (ℕ × List (Fin a))) :
    (∑ i, pack c i * tuple a i) = value c := by
  rw [Fin.sum_univ_succ]
  simp only [pack, tuple, Fin.cons_zero, Fin.cons_succ]
  have hs := (Finset.sum_list_map_count c.2 (b a)).symm
  simp only [nsmul_eq_mul, Nat.cast_id] at hs
  rw [Fintype.sum_subset (s := c.2.toFinset) (f := fun i => c.2.count i * b a i) (by
    intro i hi
    by_contra hn
    have hz : c.2.count i = 0 := List.count_eq_zero.mpr (by simpa using hn)
    exact hi (by simp [hz]))] at hs
  simpa [value, Nat.mul_comm] using congrArg (fun n => c.1 * a + n) hs

private theorem pack_size {a : ℕ} (c : (ℕ × List (Fin a))) : (∑ i, pack c i) = size c := by
  rw [Fin.sum_univ_succ]
  simp only [pack, Fin.cons_zero, Fin.cons_succ]
  have h := List.sum_toFinset_count_eq_length c.2
  rw [Fintype.sum_subset (s := c.2.toFinset) (f := fun i => c.2.count i) (by
    intro i hi
    by_contra hn
    exact hi (List.count_eq_zero.mpr (by simpa using hn)))] at h
  simpa [size] using congrArg (fun n => c.1 + n) h

private theorem pack_expand {a : ℕ} (z : Fin (a + 1) → ℕ) :
    pack (expand z) = z := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp [pack, expand, List.count_flatMap, List.count_replicate,
      Function.comp_def, ← Fin.sum_univ_def]

private theorem expand_value {a : ℕ} (z : Fin (a + 1) → ℕ) :
    value (expand z) = ∑ i, z i * tuple a i := by
  rw [← pack_value, pack_expand]

private theorem expand_size {a : ℕ} (z : Fin (a + 1) → ℕ) :
    size (expand z) = (∑ i, z i) := by
  rw [← pack_size, pack_expand]

private theorem lengths_iff {a n l : ℕ} :
    l ∈ L (tuple a) n ↔ ∃ c : (ℕ × List (Fin a)), value c = n ∧ size c = l := by
  constructor
  · rintro ⟨z, hz, hl⟩
    exact ⟨expand z, (expand_value z).trans hz, (expand_size z).trans hl⟩
  · rintro ⟨c, hv, hs⟩
    exact ⟨pack c, (pack_value c).trans hv, (pack_size c).trans hs⟩

private theorem family_intermediate {a n l₁ l₂ l : ℕ}
    (ha : 0 < a) (hc : Nat.Coprime a 2)
    (h₁ : l₁ ∈ L (tuple a) n) (h₂ : l₂ ∈ L (tuple a) n)
    (hl : l₁ ≤ l) (hu : l ≤ l₂) : l ∈ L (tuple a) n := by
  obtain ⟨c, hcv, hcs⟩ := lengths_iff.mp h₁
  obtain ⟨d, hdv, hds⟩ := lengths_iff.mp h₂
  obtain ⟨t, ht, hreach⟩ := normalizes ha c
  obtain ⟨u, hu', hreachu⟩ := normalizes ha d
  obtain ⟨htv, hst, hinter⟩ := trace_interval hreach
  obtain ⟨huv, hsu, _⟩ := trace_interval hreachu
  have he : t = u := terminal_unique ha hc ht hu' (by omega)
  subst u
  obtain ⟨v, hvv, hvs⟩ := hinter l (by omega) (by omega)
  exact lengths_iff.mpr ⟨v, hvv.trans hcv, hvs⟩

private theorem family_delta {a : ℕ} (ha : 0 < a) (hc : Nat.Coprime a 2) :
    delta (tuple a) = {1} := by
  ext q
  constructor
  · rintro ⟨n, l₁, l₂, h₁, h₂, hlt, hq, hgap⟩
    have hm := family_intermediate ha hc h₁ h₂ (l := l₁ + 1) (by omega) (by omega)
    have hg := hgap (l₁ + 1) hm
    have hq1 : q = 1 := by omega
    exact Set.mem_singleton_iff.mpr hq1
  · intro hq
    have he : q = 1 := Set.mem_singleton_iff.mp hq
    subst q
    refine ⟨2 * a, 1, 2, ?_, ?_, by omega, by omega, ?_⟩
    · apply lengths_iff.mpr
      refine ⟨(0, [⟨0, ha⟩]), ?_, ?_⟩ <;> simp [value, size, b]
    · apply lengths_iff.mpr
      refine ⟨(2, []), ?_, ?_⟩ <;> simp [value, size, Nat.mul_comm]
    · intro l _
      omega

private theorem generators_three : generators 3 2 2 2 = tuple 3 := by
  exact List.ofFn_inj.mp rfl

theorem result : ¬ claim := by
  intro h
  have he := h 3 2 2 2 (by omega) (by omega) (by omega) (by omega)
    (by decide) (by omega) (by omega) (by omega)
  have hd := family_delta (a := 3) (by omega) (by decide)
  rw [generators_three, hd] at he
  have htwo : 2 ∈ E (2 - 1) 2 := by
    exact ⟨by omega, 0, Or.inr rfl⟩
  rw [← he] at htwo
  have hbad : 2 = 1 := Set.mem_singleton_iff.mp htwo
  omega


end D5.S3.Arith.Additive.NarayanExpandedGeneratorDeltaRefutation

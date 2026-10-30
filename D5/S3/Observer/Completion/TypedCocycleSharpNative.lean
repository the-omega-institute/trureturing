/- GID: D5/S3/Observer/Completion/TypedCocycleSharpNative
   generality: G
   mirror-B: D5/B/S3/Observer/Completion/TypedCocycleSharpNative
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact static and complete names-only online costs on the entire native two-channel source. -/

import D5.S3.Observer.Completion.TypedCocycleSource
import Mathlib.Data.ZMod.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Observer.Completion.TypedCocycleSharpNative
open D5.S3.Observer.Completion.TypedCocycleSource

/-- The original full CLOSED box, including negative observations. -/
def Allowed (h ε : ℝ) (C E : Vector) (u : History) (y : Vector) : Prop :=
  |y.1 - (native h C E u).1| ≤ ε ∧ |y.2 - (native h C E u).2| ≤ ε

/-- Feasibility is defined by a decoder on exactly the permitted final inputs.
No expected cardinality, periodicity or prefix condition occurs here. -/
def Feasible {L : Type*} (h ε : ℝ) (C E : Vector) (label : History → L) : Prop :=
  ∃ decode : Vertex → L → Vector → Option (List Name),
    ∀ u y, Allowed h ε C E u y → decode (endpoint u) (label u) y = some (word u)

/-- Count actual labels of all legal root histories, not the ambient codomain. -/
def StaticCost (h ε : ℝ) (C E : Vector) (n : ℕ) : Prop :=
  ∃ (L : Type) (label : History → L), (Set.range label).Finite ∧
    Feasible h ε C E label ∧ Nat.card (Set.range label) = n

structure Register (M : Type*) where
  initial : M
  update : M → Name → M

def value {M : Type*} (r : Register M) (u : History) : M :=
  (word u).foldl r.update r.initial

/-- The ambient update is total. Only its complete legal reached range is
charged; that range is NOT assumed closed under source-illegal names. -/
def OnlineCost (h ε : ℝ) (C E : Vector) (n : ℕ) : Prop :=
  ∃ (M : Type) (_ : Finite M) (r : Register M),
    Feasible h ε C E (value r) ∧ Nat.card (Set.range (value r)) = n

/-- A least cost includes attainment and a bound for every feasible competitor. -/
def LeastCost (cost : ℕ → Prop) (n : ℕ) : Prop := cost n ∧ ∀ m, cost m → n ≤ m

def quantum (h ε : ℝ) : ℕ := ⌊2 * ε / h⌋₊ + 1

/-- One entire persistent state, with no vertex, phase, event index or clock. -/
def residueRegister (q : ℕ) : Register (ZMod q × ZMod q) where
  initial := (0, 0)
  update x b := match b with
    | .a => (x.1 + 1, x.2)
    | .c => (0, x.1)
    | .e => x

def tag (q : ℕ) : History → ZMod q × ZMod q
  | .pre m => (m, 0)
  | .mid m n => (n, m)
  | .terminal m n => (n, m)

private theorem fold_a (q m : ℕ) (x : ZMod q × ZMod q) :
    (List.replicate m Name.a).foldl (residueRegister q).update x = (x.1 + m, x.2) := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    simp [List.replicate_succ, List.foldl, ih, residueRegister, Nat.cast_add, add_assoc]

private theorem value_eq_tag (q : ℕ) (u : History) : value (residueRegister q) u = tag q u := by
  cases u <;> simp [value, word, List.foldl_append, fold_a, residueRegister, tag]

private theorem tag_surjective (q : ℕ) (hq : q ≠ 0) : Function.Surjective (tag q) := by
  letI : NeZero q := ⟨hq⟩
  rintro ⟨x, y⟩
  exact ⟨.mid y.val x.val, by simp [tag]⟩

private theorem reached_card (q : ℕ) (hq : q ≠ 0) :
    Nat.card (Set.range (value (residueRegister q))) = q ^ 2 := by
  have hv : value (residueRegister q) = tag q := funext (value_eq_tag q)
  rw [hv, Set.range_eq_univ.mpr (tag_surjective q hq)]
  simp [Nat.card_prod, Nat.card_zmod, pow_two]

/-- The actual translated square uses only nonnegative source lap counts. -/
def square (k : ℕ) (i : Fin (k + 1) × Fin (k + 1)) : History :=
  .mid (k + 2 * i.1.val - i.2.val) (k + i.2.val - i.1.val)

private theorem square_counts (k : ℕ) (i : Fin (k + 1) × Fin (k + 1)) :
    (k + 2 * i.1.val - i.2.val) + (k + i.2.val - i.1.val) = 2 * k + i.1.val ∧
    (k + 2 * i.1.val - i.2.val) + 2 * (k + i.2.val - i.1.val) = 3 * k + i.2.val := by
  have hi := i.1.isLt
  have hj := i.2.isLt
  omega

private theorem square_injective (k : ℕ) : Function.Injective (square k) := by
  intro i j hij
  have h := History.mid.inj hij
  have hi := square_counts k i
  have hj := square_counts k j
  apply Prod.ext <;> apply Fin.ext <;> omega

private theorem square_total (h : ℝ) (C E : Vector) (k : ℕ)
    (i : Fin (k + 1) × Fin (k + 1)) :
    native h C E (square k i) =
      (C.1 + h * (2 * k + i.1.val), C.2 + h * (3 * k + i.2.val)) := by
  have hc := square_counts k i
  unfold square native
  have h1 : ((k + 2 * i.1.val - i.2.val : ℕ) : ℝ) +
      ((k + i.2.val - i.1.val : ℕ) : ℝ) = 2 * k + i.1.val := by exact_mod_cast hc.1
  have h2 : ((k + 2 * i.1.val - i.2.val : ℕ) : ℝ) +
      2 * ((k + i.2.val - i.1.val : ℕ) : ℝ) = 3 * k + i.2.val := by exact_mod_cast hc.2
  rw [h1, h2]

private theorem square_allowed (h ε : ℝ) (hh : 0 ≤ h) (C E : Vector) (k : ℕ)
    (hk : h * k ≤ 2 * ε) (i : Fin (k + 1) × Fin (k + 1)) :
    Allowed h ε C E (square k i)
      (C.1 + h * (2 * k + (k : ℝ) / 2), C.2 + h * (3 * k + (k : ℝ) / 2)) := by
  rw [Allowed, square_total]
  have hi : (i.1.val : ℝ) ≤ k := by exact_mod_cast Nat.le_of_lt_succ i.1.isLt
  have hj : (i.2.val : ℝ) ≤ k := by exact_mod_cast Nat.le_of_lt_succ i.2.isLt
  have hi0 : (0 : ℝ) ≤ i.1.val := Nat.cast_nonneg _
  have hj0 : (0 : ℝ) ≤ i.2.val := Nat.cast_nonneg _
  constructor <;> apply abs_le.mpr <;> constructor <;> dsimp <;> nlinarith

private theorem static_lower {L : Type*} (h ε : ℝ) (hh : 0 ≤ h)
    (C E : Vector) (k : ℕ) (hk : h * k ≤ 2 * ε) (label : History → L)
    (hf : (Set.range label).Finite) (hd : Feasible h ε C E label) :
    (k + 1) ^ 2 ≤ Nat.card (Set.range label) := by
  letI : Finite (Set.range label) := hf
  obtain ⟨decode, hd⟩ := hd
  let f : Fin (k + 1) × Fin (k + 1) → Set.range label :=
    fun i => ⟨label (square k i), ⟨square k i, rfl⟩⟩
  have hinj : Function.Injective f := by
    intro i j hij
    have hl : label (square k i) = label (square k j) := congrArg Subtype.val hij
    have hi := hd (square k i) _ (square_allowed h ε hh C E k hk i)
    have hj := hd (square k j) _ (square_allowed h ε hh C E k hk j)
    have he : endpoint (square k i) = endpoint (square k j) := rfl
    rw [he, hl, hj] at hi
    exact square_injective k ((source_correspondence h C E).1 (Option.some.inj hi).symm)
  simpa [Nat.card_prod, Nat.card_eq_fintype_card, pow_two] using
    Nat.card_le_card_of_injective f hinj

def counts : History → ℕ × ℕ
  | .pre m => (m, m)
  | .mid m n => (m + n, m + 2 * n)
  | .terminal m n => (m + n, m + 2 * n)

def offset (C E : Vector) : Vertex → Vector
  | .p => 0
  | .s => C
  | .t => C + E

private theorem native_counts (h : ℝ) (C E : Vector) (u : History) :
    native h C E u =
      ((offset C E (endpoint u)).1 + h * (counts u).1,
       (offset C E (endpoint u)).2 + h * (counts u).2) := by
  cases u <;> simp [native, counts, offset, endpoint, Nat.cast_add, Nat.cast_mul]

private theorem counts_injective (u v : History) (he : endpoint u = endpoint v)
    (hc : counts u = counts v) : u = v := by
  cases u <;> cases v <;> simp [endpoint] at he
  all_goals simp only [counts, Prod.mk.injEq] at hc
  all_goals congr 1 <;> omega

private theorem tag_counts (q : ℕ) (u v : History) (he : endpoint u = endpoint v)
    (ht : tag q u = tag q v) :
    ((counts u).1 : ZMod q) = (counts v).1 ∧
    ((counts u).2 : ZMod q) = (counts v).2 := by
  cases u <;> cases v <;> simp [endpoint] at he
  all_goals simp only [tag, Prod.mk.injEq] at ht
  all_goals simp [counts, Nat.cast_add, Nat.cast_mul, ht.1, ht.2]

private theorem modular_close (h ε : ℝ) (hh : 0 < h) (q : ℕ)
    (hq : 2 * ε < h * q) (x y : ℕ) (hm : (x : ZMod q) = y)
    (hc : |h * x - h * y| ≤ 2 * ε) : x = y := by
  by_contra hxy
  have hd : (q : ℤ) ∣ (y : ℤ) - x :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (x : ℤ) (y : ℤ) q).mp (by simpa using hm)
  have hn : (y : ℤ) - x ≠ 0 := by omega
  have hg := Int.natAbs_le_of_dvd_ne_zero hd hn
  have hg' : (q : ℝ) ≤ |(y : ℝ) - x| := by
    have hh' : (q : ℝ) ≤ (((y : ℤ) - x).natAbs : ℕ) := by exact_mod_cast hg
    simpa only [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub, Int.cast_natCast] using hh'
  have hg'' := mul_le_mul_of_nonneg_left hg' hh.le
  have hr : |h * x - h * y| = h * |(y : ℝ) - x| := by
    rw [show h * (x : ℝ) - h * y = h * ((x : ℝ) - y) by ring,
      abs_mul, abs_of_pos hh, abs_sub_comm]
  rw [hr] at hc
  linarith

private theorem allowed_gap (h ε : ℝ) (C E : Vector) (u v : History) (y : Vector)
    (hu : Allowed h ε C E u y) (hv : Allowed h ε C E v y)
    (he : endpoint u = endpoint v) :
    |h * (counts u).1 - h * (counts v).1| ≤ 2 * ε ∧
    |h * (counts u).2 - h * (counts v).2| ≤ 2 * ε := by
  rw [Allowed, native_counts] at hu hv
  rw [he] at hu
  have hu1 := abs_le.mp hu.1
  have hu2 := abs_le.mp hu.2
  have hv1 := abs_le.mp hv.1
  have hv2 := abs_le.mp hv.2
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith

private theorem decoder_of_unique {L : Type*} (h ε : ℝ) (C E : Vector) (label : History → L)
    (hu : ∀ u v y, endpoint u = endpoint v → label u = label v →
      Allowed h ε C E u y → Allowed h ε C E v y → u = v) :
    Feasible h ε C E label := by
  let Explanation := {uy : History × Vector // Allowed h ε C E uy.1 uy.2}
  let process : Explanation → Vertex × L × Vector :=
    fun x => (endpoint x.val.1, label x.val.1, x.val.2)
  let target : Explanation → Option (List Name) := fun x => some (word x.val.1)
  have factors : target.FactorsThrough process := by
    intro x y hxy
    have hz : endpoint x.val.1 = endpoint y.val.1 := congrArg Prod.fst hxy
    have hl : label x.val.1 = label y.val.1 := congrArg (fun z => z.2.1) hxy
    have hy : x.val.2 = y.val.2 := congrArg (fun z => z.2.2) hxy
    have eqh := hu x.val.1 y.val.1 x.val.2 hz hl x.property (hy.symm ▸ y.property)
    dsimp [target]
    rw [eqh]
  obtain ⟨decode, hd⟩ := (Function.factorsThrough_iff target).mp factors
  refine ⟨fun z l y => decode (z, l, y), ?_⟩
  intro u y hy
  exact (congrFun hd ⟨(u, y), hy⟩).symm

private theorem upper_feasible (h ε : ℝ) (hh : 0 < h) (C E : Vector) (q : ℕ)
    (hq : 2 * ε < h * q) : Feasible h ε C E (tag q) := by
  apply decoder_of_unique
  intro u v y he ht hu hv
  have hm := tag_counts q u v he ht
  have hc := allowed_gap h ε C E u v y hu hv he
  apply counts_injective u v he
  exact Prod.ext (modular_close h ε hh q hq _ _ hm.1 hc.1)
    (modular_close h ε hh q hq _ _ hm.2 hc.2)

private theorem quantum_bounds (h ε : ℝ) (hh : 0 < h) (hε : 0 ≤ ε) :
    h * (⌊2 * ε / h⌋₊ : ℝ) ≤ 2 * ε ∧ 2 * ε < h * quantum h ε := by
  have hn : 0 ≤ 2 * ε / h := div_nonneg (by linarith) hh.le
  have hlo := Nat.floor_le hn
  have hhi := Nat.lt_floor_add_one (2 * ε / h)
  constructor
  · simpa only [mul_comm] using (le_div_iff₀ hh).mp hlo
  · have hb := (div_lt_iff₀ hh).mp hhi
    simpa [quantum, Nat.cast_add, Nat.cast_one, mul_comm] using hb

private theorem cost_attained (h ε : ℝ) (hh : 0 < h) (hε : 0 ≤ ε) (C E : Vector) :
    StaticCost h ε C E ((quantum h ε) ^ 2) ∧
    OnlineCost h ε C E ((quantum h ε) ^ 2) := by
  let q := quantum h ε
  have hq : q ≠ 0 := by dsimp [q, quantum]; omega
  letI : NeZero q := ⟨hq⟩
  have hf := upper_feasible h ε hh C E q (quantum_bounds h ε hh hε).2
  have hv : value (residueRegister q) = tag q := funext (value_eq_tag q)
  have hc := reached_card q hq
  constructor
  · exact ⟨ZMod q × ZMod q, value (residueRegister q), Set.toFinite _, hv.symm ▸ hf, hc⟩
  · exact ⟨ZMod q × ZMod q, inferInstance, residueRegister q, hv.symm ▸ hf, hc⟩

private theorem whole_minima (h ε : ℝ) (hh : 0 < h) (hε : 0 ≤ ε) (C E : Vector) :
    LeastCost (StaticCost h ε C E) ((quantum h ε) ^ 2) ∧
    LeastCost (OnlineCost h ε C E) ((quantum h ε) ^ 2) := by
  have att := cost_attained h ε hh hε C E
  have hl : ∀ n, StaticCost h ε C E n → (quantum h ε) ^ 2 ≤ n := by
    rintro n ⟨L, label, hf, hd, rfl⟩
    exact static_lower h ε hh.le C E _ (quantum_bounds h ε hh hε).1 label hf hd
  refine ⟨⟨att.1, hl⟩, att.2, ?_⟩
  rintro n ⟨M, hM, r, hd, rfl⟩
  letI : Finite M := hM
  exact hl _ ⟨M, value r, Set.toFinite _, hd, rfl⟩

private theorem no_supplement (h ε : ℝ) (hh : 0 < h) (C E : Vector) :
    Feasible h ε C E (fun _ : History => ()) ↔ 2 * ε < h := by
  constructor
  · intro hd
    by_contra hn
    have hl := static_lower h ε hh.le C E 1 (by simpa using le_of_not_gt hn)
      (fun _ : History => ()) (Set.toFinite _) hd
    norm_num [Set.range_const] at hl
  · intro hn
    obtain ⟨decode, hd⟩ := upper_feasible h ε hh C E 1 (by simpa using hn)
    refine ⟨fun z _ y => decode z (0, 0) y, ?_⟩
    intro u y hy
    have ht : tag 1 u = (0, 0) := Subsingleton.elim _ _
    simpa [ht] using hd u y hy

private theorem quantum_threshold (h ε : ℝ) (hh : 0 < h) (hε : 0 ≤ ε) (k : ℕ)
    (hlo : (k : ℝ) * h ≤ 2 * ε) (hhi : 2 * ε < (k + 1 : ℕ) * h) :
    quantum h ε = k + 1 := by
  unfold quantum
  congr 1
  apply (Nat.floor_eq_iff (div_nonneg (by linarith) hh.le)).mpr
  constructor
  · exact (le_div_iff₀ hh).mpr hlo
  · apply (div_lt_iff₀ hh).mpr
    simpa only [Nat.cast_add, Nat.cast_one] using hhi

/-- Both minima on the ENTIRE actual source, arbitrary finite actual static
ranges and complete legal online reached ranges. The decoder recovers ordered
words on every point of every original closed box. Offsets need no sign
restriction, so in particular all fixed positive C,E are included. -/
theorem whole_sharp_native_law (h ε : ℝ) (hh : 0 < h) (hε : 0 < ε) (C E : Vector) :
    LeastCost (StaticCost h ε C E) ((quantum h ε) ^ 2) ∧
    LeastCost (OnlineCost h ε C E) ((quantum h ε) ^ 2) ∧
    (Feasible h ε C E (fun _ : History => ()) ↔ 2 * ε < h) ∧
    (∀ k : ℕ, (k : ℝ) * h ≤ 2 * ε → 2 * ε < (k + 1 : ℕ) * h →
      quantum h ε = k + 1) := by
  have hm := whole_minima h ε hh hε.le C E
  exact ⟨hm.1, hm.2, no_supplement h ε hh C E,
    quantum_threshold h ε hh hε.le⟩

#print axioms whole_sharp_native_law
end D5.S3.Observer.Completion.TypedCocycleSharpNative

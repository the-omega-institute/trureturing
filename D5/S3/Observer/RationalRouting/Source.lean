/- GID: D5/S3/Observer/RationalRouting/Source
   generality: I
   mirror-B: D5/B/S3/Observer/RationalRouting/Source
   mirror-E: none(waiver:exact-symbolic-source)
   anchors: []
   utility: none
   digest: Finite rational-source runs must read an attained grid to distinguish a lower accumulation tail. -/

import D5.S3.PrimeForms.SternBrocot.WordNodesAreReduced
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Order.Archimedean.Basic

/-! One-source rational action semantics and finite endpoint replay. -/

set_option autoImplicit false

namespace D5.S3.Observer.RationalRouting

/-- False is L and true is R. The head is the first physical action. -/
def step (b : Bool) (x : ℚ) : ℚ := if b then x + 1 else x / (1 + x)

def attain : List Bool → ℚ → ℚ
  | [], x => x
  | b :: w, x => attain w (step b x)

/-- An actual installed read, including the whole integer report. -/
def port (w : List Bool) (s : ℕ) (x : ℚ) : ℤ := ⌊(2 : ℚ)^s * attain w x⌋

def Grid (w : List Bool) (s : ℕ) (x : ℚ) : Prop :=
  ∃ k : ℤ, (2 : ℚ)^s * attain w x = k

def endpoint (i : Bool) : ℚ := if i then 2/3 else 1/6

def tail (i : Bool) (n : ℕ) : ℚ := endpoint i - 1/(n : ℚ)

def Band (i : Bool) (x : ℚ) : Prop :=
  x = endpoint i ∨ ∃ n : ℕ, 12 ≤ n ∧ x = tail i n

def Prior (x : ℚ) : Prop := ∃ i : Bool, Band i x

/-- Local transitions have no source argument. Only read continuations receive reports. -/
inductive Command (State Output : Type)
  | halt (output : Output)
  | work (next : State)
  | move (letter : Bool) (next : State)
  | read (scale : ℕ) (next : ℤ → State)

/-- A finite actual run on one source, with chronological prefixes retained at reads.
No inverse, copy, reset, source archive or timing input is an instruction. -/
inductive Run {State Output : Type} (code : State → Command State Output) (x : ℚ) :
    State → List Bool → Output → List Bool → List (List Bool × ℕ) → Prop
  | halt {st w out} : code st = .halt out → Run code x st w out w []
  | work {st next w out v reads} : code st = .work next →
      Run code x next w out v reads → Run code x st w out v reads
  | move {st next w out v reads b} : code st = .move b next →
      Run code x next (w ++ [b]) out v reads → Run code x st w out v reads
  | read {st next w out v reads s} : code st = .read s next →
      Run code x (next (port w s x)) w out v reads →
      Run code x st w out v ((w,s) :: reads)

/-- Termination and full output correctness are both required on every prior member. -/
def Correct {State Output : Type} (code : State → Command State Output)
    (init : State) (target : ℚ → Output) : Prop :=
  ∀ x, Prior x →
    (∃ out v reads, Run code x init [] out v reads) ∧
    ∀ out v reads, Run code x init [] out v reads → out = target x

private theorem step_control (b : Bool) {y r : ℚ} (hy : 0 < y) (hyr : y ≤ r) :
    0 < step b y ∧ 0 ≤ step b r - step b y ∧ step b r - step b y ≤ r-y := by
  have hr : 0 < r := hy.trans_le hyr
  cases b
  · have hd : 0 < (1+r)*(1+y) := by positivity
    have hone : 1 ≤ (1+r)*(1+y) := by nlinarith
    have heq : r/(1+r)-y/(1+y) = (r-y)/((1+r)*(1+y)) := by
      field_simp
      <;> ring
    dsimp [step]
    refine ⟨by positivity, ?_, ?_⟩
    · rw [heq]; exact div_nonneg (sub_nonneg.mpr hyr) hd.le
    · rw [heq]; exact div_le_self (sub_nonneg.mpr hyr) hone
  · dsimp [step]
    constructor
    · linarith
    constructor <;> linarith

private theorem attain_control (w : List Bool) {y r : ℚ} (hy : 0 < y) (hyr : y ≤ r) :
    0 < attain w y ∧ 0 ≤ attain w r - attain w y ∧ attain w r - attain w y ≤ r-y := by
  induction w generalizing y r with
  | nil => exact ⟨hy, sub_nonneg.mpr hyr, le_rfl⟩
  | cons b w ih =>
    obtain ⟨hp, hm, hb⟩ := step_control b hy hyr
    obtain ⟨hp', hm', hb'⟩ := ih hp (by linarith)
    exact ⟨hp', hm', hb'.trans hb⟩

private theorem port_left_stable (w : List Bool) (s : ℕ) {r : ℚ}
    (hr : 0 < r) (hg : ¬ Grid w s r) :
    ∃ δ : ℚ, 0 < δ ∧ ∀ y : ℚ, 0 < y → y ≤ r → r-y < δ →
      port w s y = port w s r := by
  let a : ℚ := (2 : ℚ)^s
  let z : ℚ := a * attain w r
  have ha : 0 < a := by dsimp [a]; positivity
  generalize hk : Int.floor z = k
  have hfloor : (k : ℚ) ≤ z := by rw [← hk]; exact Int.floor_le z
  have hne : z ≠ (k : ℚ) := by
    intro h
    exact hg ⟨k, h⟩
  have hgap : 0 < z - (k : ℚ) :=
    sub_pos.mpr (lt_of_le_of_ne hfloor hne.symm)
  refine ⟨(z - (k : ℚ))/a, div_pos hgap ha, ?_⟩
  intro y hy hyr hδ
  obtain ⟨_, hm, hb⟩ := attain_control w hy hyr
  have hδ' : a*(r-y) < z-(k : ℚ) := by
    have h := (lt_div_iff₀ ha).mp hδ
    nlinarith
  have hmul : a*(attain w r - attain w y) ≤ a*(r-y) :=
    mul_le_mul_of_nonneg_left hb ha.le
  have hz : z = a*attain w r := rfl
  have hlo : (k : ℚ) ≤ a*attain w y := by nlinarith
  have hup : a*attain w y < (k : ℚ)+1 := by
    have hh : z < (k : ℚ)+1 := by rw [← hk]; exact Int.lt_floor_add_one z
    nlinarith
  change ⌊a*attain w y⌋ = ⌊z⌋
  rw [hk]
  exact Int.floor_eq_iff.mpr ⟨hlo, hup⟩

/-- An entire finite branch replays on a left neighborhood if none of its actual reads is a grid read. -/
private theorem run_left_stable {State Output : Type} {code : State → Command State Output}
    {r : ℚ} {st : State} {w : List Bool} {out : Output} {v : List Bool}
    {reads : List (List Bool × ℕ)} (run : Run code r st w out v reads) (hr : 0 < r)
    (hg : ∀ p ∈ reads, ¬ Grid p.1 p.2 r) :
    ∃ δ : ℚ, 0 < δ ∧ ∀ y : ℚ, 0 < y → y ≤ r → r-y < δ →
      Run code y st w out v reads := by
  induction run with
  | halt h => exact ⟨1, by norm_num, fun _ _ _ _ => Run.halt h⟩
  | work h run ih =>
    obtain ⟨δ, hδ, replay⟩ := ih hg
    exact ⟨δ,hδ,fun y hy hyr hd => Run.work h (replay y hy hyr hd)⟩
  | move h run ih =>
    obtain ⟨δ, hδ, replay⟩ := ih hg
    exact ⟨δ,hδ,fun y hy hyr hd => Run.move h (replay y hy hyr hd)⟩
  | @read st next w out v reads s h run ih =>
    obtain ⟨δ, hδ, replay⟩ := ih (fun p hp => hg p (by simp [hp]))
    obtain ⟨ε, hε, same⟩ := port_left_stable w s hr (hg (w,s) (by simp))
    refine ⟨min δ ε, lt_min hδ hε, ?_⟩
    intro y hy hyr hd
    have hsame := same y hy hyr (lt_of_lt_of_le hd (min_le_right _ _))
    apply Run.read h
    rw [hsame]
    exact replay y hy hyr (lt_of_lt_of_le hd (min_le_left _ _))

private theorem endpoint_pos (i : Bool) : 0 < endpoint i := by
  cases i <;> norm_num [endpoint]

private theorem tail_arbitrarily_close (i : Bool) {δ : ℚ} (hδ : 0 < δ) :
    ∃ n : ℕ, 12 ≤ n ∧ 0 < tail i n ∧ tail i n < endpoint i ∧ endpoint i-tail i n < δ := by
  have hc := endpoint_pos i
  obtain ⟨n,hn⟩ := exists_nat_gt (max 12 (max (1/endpoint i) (1/δ)))
  have hn12 : (12 : ℚ) < n := lt_of_le_of_lt (le_max_left _ _) hn
  have hn0 : (0 : ℚ) < n := by linarith
  have hnN : 12 ≤ n := by exact_mod_cast hn12.le
  have hnc : 1/endpoint i < (n : ℚ) :=
    lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hn
  have hnd : 1/δ < (n : ℚ) :=
    lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hn
  have hc' : 1/(n : ℚ) < endpoint i := by
    apply (div_lt_iff₀ hn0).mpr
    have hh := (div_lt_iff₀ hc).mp hnc
    nlinarith
  have hd' : 1/(n : ℚ) < δ := by
    apply (div_lt_iff₀ hn0).mpr
    have hh := (div_lt_iff₀ hδ).mp hnd
    nlinarith
  refine ⟨n, hnN, ?_, ?_, ?_⟩ <;> dsimp [tail] <;>
    have hinv : 0 < 1/(n : ℚ) := by positivity
  · linarith
  · linarith
  · linarith

/-- Every correct finite endpoint run for an injective original output includes
an actual attained-grid read. This quantifies over all deterministic controllers,
without a bound on their read scales, local work, read count or other runs. -/
theorem endpoint_run_requires_grid {State Output : Type}
    {code : State → Command State Output} {init : State} {target : ℚ → Output}
    (correct : Correct code init target) (injective : Set.InjOn target {x | Prior x})
    (i : Bool) {out : Output} {v : List Bool} {reads : List (List Bool × ℕ)}
    (run : Run code (endpoint i) init [] out v reads) :
    ∃ p ∈ reads, Grid p.1 p.2 (endpoint i) := by
  by_contra h
  have hg : ∀ p ∈ reads, ¬ Grid p.1 p.2 (endpoint i) := by simpa using h
  obtain ⟨δ,hδ,replay⟩ := run_left_stable run (endpoint_pos i) hg
  obtain ⟨n,hn,hy,hlt,hclose⟩ := tail_arbitrarily_close i hδ
  have hp : Prior (endpoint i) := ⟨i,Or.inl rfl⟩
  have hq : Prior (tail i n) := ⟨i,Or.inr ⟨n,hn,rfl⟩⟩
  have same := replay (tail i n) hy hlt.le hclose
  have heq : target (endpoint i) = target (tail i n) :=
    ((correct _ hp).2 _ _ _ run).symm.trans ((correct _ hq).2 _ _ _ same)
  exact (ne_of_gt hlt) (injective hp hq heq)

#print axioms endpoint_run_requires_grid

end D5.S3.Observer.RationalRouting

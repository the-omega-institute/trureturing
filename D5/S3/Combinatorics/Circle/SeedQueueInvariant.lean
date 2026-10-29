/- GID: D5/S3/Combinatorics/Circle/SeedQueueInvariant
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/SeedQueueInvariant
   mirror-E: none(waiver:audit-open-22063)
   anchors: [D5/S3/Combinatorics/Circle/SourceWidth]
   utility: none
   digest: Deferred prefixes preserve ancestor heights and bound the first-omission peak. -/
module
public import D5.S3.Combinatorics.Circle.SourceWidth

/-! # Deferred dyadic queues with physical occurrence identity -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace D5.S3.Combinatorics.Circle.SeedQueueInvariant
open SourceWidth

/-- Initial segment before the first budget crossing, paired with its literal
suffix. For positive weights this is the longest affordable prefix. -/
def splitBudget {α : Type*} (f : α → ℤ) : ℤ → List α → List α × List α
  | _, [] => ([], [])
  | B, x :: xs => if f x ≤ B then
      let z := splitBudget f (B - f x) xs
      (x :: z.1, z.2)
    else ([], x :: xs)

/-- T is preceding mass; each occurrence remembers its birth height. -/
def Ancestors {α : Type*} (f : α → ℤ) (mu D : ℤ) : ℤ → List α → Prop
  | _, [] => True
  | T, x :: xs => 0 ≤ f x - mu - T ∧ f x - mu - T ≤ D ∧
      Ancestors f mu D (T + f x) xs

private theorem ancestor_prefix {α : Type*} {f : α → ℤ} {mu D T : ℤ}
    (q e : List α) (h : Ancestors f mu D T (q ++ e)) : Ancestors f mu D T q := by
  induction q generalizing T with
  | nil => trivial
  | cons x xs ih => exact ⟨h.1, h.2.1, ih h.2.2⟩

private theorem ancestor_suffix {α : Type*} {f : α → ℤ} {mu D T : ℤ}
    (q e : List α) (h : Ancestors f mu D T (q ++ e)) :
    Ancestors f mu D (T + (q.map f).sum) e := by
  induction q generalizing T with
  | nil => simpa using h
  | cons x xs ih => simpa [add_assoc] using ih h.2.2

private theorem ancestor_append {α : Type*} {f : α → ℤ} {mu D T : ℤ}
    (q e : List α) (hq : Ancestors f mu D T q)
    (he : Ancestors f mu D (T + (q.map f).sum) e) : Ancestors f mu D T (q ++ e) := by
  induction q generalizing T with
  | nil => simpa using he
  | cons x xs ih =>
    refine ⟨hq.1, hq.2.1, ih hq.2.2 ?_⟩
    simpa [add_assoc] using he

private theorem dyadic_ancestors {α : Type*} {f : α → ℤ} {mu D T a : ℤ}
    {l : List α} (hl : Dyadic f a l) (hlo : 0 ≤ a - mu - T)
    (hhi : a - mu - T ≤ D) : Ancestors f mu D T l := by
  induction l generalizing a T with
  | nil => trivial
  | cons x xs ih =>
    refine ⟨by simpa [hl.1] using hlo, by simpa [hl.1] using hhi, ?_⟩
    exact ih hl.2 (by rw [hl.1]; omega) (by rw [hl.1]; omega)

private theorem split_spec {α : Type*} (f : α → ℤ) (B : ℤ) (l : List α)
    (hB : 0 ≤ B) :
    let q := (splitBudget f B l).1
    let e := (splitBudget f B l).2
    l = q ++ e ∧ (q.map f).sum ≤ B ∧
      ∀ x xs, e = x :: xs → B < (q.map f).sum + f x := by
  induction l generalizing B with
  | nil => simp [splitBudget, hB]
  | cons x xs ih =>
    by_cases hx : f x ≤ B
    · have hp := ih (B - f x) (by omega)
      dsimp only at hp ⊢
      simp only [splitBudget, ite_eq_left hx, List.map_cons, List.sum_cons]
      refine ⟨?_, by omega, ?_⟩
      · simpa using congrArg (List.cons x) hp.1
      · intro y ys he
        have hh := hp.2.2 y ys he
        omega
    · simp only [splitBudget, ite_eq_right hx, List.nil_append, List.map_nil, List.sum_nil, true_and]
      refine ⟨hB, ?_⟩
      intro y ys he
      have : x = y := (List.cons.inj he).1
      subst y
      omega

/-- Appending dyadic SMALL labels preserves every retained ancestor height.
A first omission bounds the peak by C+floor(D/2). If all labels are retained,
the peak is exactly the old height plus the root parameter. -/
theorem deferred_prefix_invariant {α : Type*} (f : α → ℤ)
    (old small : List α) (mu D a b p B C : ℤ)
    (hold : Ancestors f mu D 0 old) (hdyadic : Dyadic f a small)
    (hbirth : small ≠ [] → 0 ≤ a - mu - (old.map f).sum ∧
      a - mu - (old.map f).sum ≤ D)
    (hbudget : mu ≤ b)
    (htransport : (small.map f).sum - (B - p) = b - a)
    (hcapacity : 2 * (C - B) = b - 1) :
    let q := (splitBudget f (b - mu) (old ++ small)).1
    let e := (splitBudget f (b - mu) (old ++ small)).2
    let h := b - mu - (q.map f).sum
    old ++ small = q ++ e ∧ Ancestors f mu D 0 q ∧ 0 ≤ h ∧
      (a - mu - (old.map f).sum) + (e.map f).sum + p - B = h ∧
      (∀ x xs, e = x :: xs → h < f x ∧ B + h ≤ C + D / 2) ∧
      (e = [] → B + h = a - mu - (old.map f).sum + p) ∧
      (b = mu → (∀ x ∈ old ++ small, 0 < f x) → q = [] ∧ h = 0) := by
  dsimp only
  let q := (splitBudget f (b - mu) (old ++ small)).1
  let e := (splitBudget f (b - mu) (old ++ small)).2
  obtain ⟨hsplit, hmass, hmax⟩ := split_spec f (b - mu) (old ++ small) (by omega)
  change old ++ small = q ++ e at hsplit
  change (q.map f).sum ≤ b - mu at hmass
  have hall : Ancestors f mu D 0 (old ++ small) := by
    apply ancestor_append old small hold
    cases small with
    | nil => trivial
    | cons x xs =>
      have hh := hbirth (by simp)
      exact dyadic_ancestors hdyadic (by simpa using hh.1) (by simpa using hh.2)
  have hq := ancestor_prefix q e (hsplit ▸ hall)
  have he : Ancestors f mu D (q.map f).sum e := by
    have hsuf := ancestor_suffix q e (hsplit ▸ hall)
    rw [zero_add] at hsuf
    exact hsuf
  have hconserve : (old.map f).sum + (small.map f).sum =
      (q.map f).sum + (e.map f).sum := by
    have ht := congrArg (fun l : List α => (l.map f).sum) hsplit
    simpa only [List.map_append, List.sum_append] using ht
  change old ++ small = q ++ e ∧ Ancestors f mu D 0 q ∧
    0 ≤ b - mu - (q.map f).sum ∧
    (a - mu - (old.map f).sum) + (e.map f).sum + p - B =
      b - mu - (q.map f).sum ∧
    (∀ x xs, e = x :: xs → b - mu - (q.map f).sum < f x ∧
      B + (b - mu - (q.map f).sum) ≤ C + D / 2) ∧
    (e = [] → B + (b - mu - (q.map f).sum) = a - mu - (old.map f).sum + p) ∧
    (b = mu → (∀ x ∈ old ++ small, 0 < f x) →
      q = [] ∧ b - mu - (q.map f).sum = 0)
  change ∀ x xs, e = x :: xs → b - mu < (q.map f).sum + f x at hmax
  refine ⟨hsplit, hq, by omega, by omega, ?_, ?_, ?_⟩
  · intro x xs hex
    have hd : 0 ≤ f x - mu - (q.map f).sum ∧ f x - mu - (q.map f).sum ≤ D := by
      rw [hex] at he
      exact ⟨he.1, he.2.1⟩
    have hm := hmax x xs hex
    change b - mu < (q.map f).sum + f x at hm
    constructor <;> omega
  · intro hex
    rw [hex, List.map_nil, List.sum_nil] at hconserve
    omega
  · intro hb hpos
    have hqpos (x : α) (hx : x ∈ q) : 0 < f x := by
      apply hpos x
      rw [hsplit]
      exact List.mem_append_left _ hx
    have hqzero : q = [] := by
      cases hqeq : q with
      | nil => rfl
      | cons x xs =>
        have hx := hqpos x (by simp [hqeq])
        have htail : 0 ≤ (xs.map f).sum := List.sum_nonneg (by
          intro z hz
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
          exact le_of_lt (hqpos y (by simp [hqeq, hy])))
        rw [hqeq, List.map_cons, List.sum_cons] at hmass
        omega
    exact ⟨hqzero, by simp [hqzero, hb]⟩

end D5.S3.Combinatorics.Circle.SeedQueueInvariant

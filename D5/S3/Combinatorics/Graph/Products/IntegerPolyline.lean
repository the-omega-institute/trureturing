/- GID: D5/S3/Combinatorics/Graph/Products/IntegerPolyline
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Products/IntegerPolyline
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.List.Range]
   utility: none
   digest: Integer polyline samples agree with the complete corner expansion and the right-closed verifier convention. -/
import D5.S3.Combinatorics.Graph.Products.LatticeRouting

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Products.IntegerPolyline

open LatticeRouting

def segmentLength (a b : Point) : ℕ := (b.1 - a.1).natAbs + (b.2 - a.2).natAbs

def sign (z : ℤ) : ℤ := if z = 0 then 0 else if 0 < z then 1 else -1

def step (a b : Point) (i : ℕ) : Point :=
  (a.1 + (i : ℤ) * sign (b.1 - a.1), a.2 + (i : ℤ) * sign (b.2 - a.2))

def axisAligned (p : List Point) : Prop :=
  ∀ ab ∈ p.zip p.tail, ab.1.1 = ab.2.1 ∨ ab.1.2 = ab.2.2

instance (p : List Point) : Decidable (axisAligned p) := by
  unfold axisAligned
  infer_instance

/-- Exclude the right endpoint; the next segment contributes it. -/
def segmentPrefix (a b : Point) : List Point :=
  (List.range (segmentLength a b)).map (step a b)

def expandFrom (a : Point) : List Point → List Point
  | [] => [a]
  | b :: bs => segmentPrefix a b ++ expandFrom b bs

def expand : List Point → List Point
  | [] => []
  | a :: as => expandFrom a as

def lengthFrom (a : Point) : List Point → ℕ
  | [] => 0
  | b :: bs => segmentLength a b + lengthFrom b bs

def length : List Point → ℕ
  | [] => 0
  | a :: as => lengthFrom a as

/-- The same enumeration, sampled without expanding the long paths.
This makes the consumed checker O(number of points × number of corners),
instead of repeatedly searching a 6,329-element expanded route. -/
def sampleFrom (a : Point) : List Point → ℕ → Option Point
  | [], i => if i = 0 then some a else none
  | b :: bs, i =>
    if i < segmentLength a b then some (step a b i)
    else sampleFrom b bs (i - segmentLength a b)

def sample (p : List Point) (i : ℕ) : Point :=
  (match p with
   | [] => none
   | a :: as => sampleFrom a as i).getD (0, 0)

theorem length_expandFrom (a : Point) (bs : List Point) :
    (expandFrom a bs).length = lengthFrom a bs + 1 := by
  induction bs generalizing a with
  | nil => simp [expandFrom, lengthFrom]
  | cons b bs ih => simp [expandFrom, lengthFrom, segmentPrefix, ih, Nat.add_assoc]

theorem length_expand (p : List Point) (hne : p ≠ []) :
    (expand p).length = length p + 1 := by
  cases p with
  | nil => contradiction
  | cons a as => exact length_expandFrom a as

theorem sampleFrom_eq_getElem? (a : Point) (bs : List Point) (i : ℕ) :
    sampleFrom a bs i = (expandFrom a bs)[i]? := by
  induction bs generalizing a i with
  | nil =>
    cases i <;> simp [sampleFrom, expandFrom]
  | cons b bs ih =>
    rw [sampleFrom, expandFrom, List.getElem?_append]
    have hl : (segmentPrefix a b).length = segmentLength a b := by simp [segmentPrefix]
    rw [hl]
    split_ifs with hi
    · simp [segmentPrefix, List.getElem?_map, List.getElem?_range, hi]
    · exact ih b (i - segmentLength a b)

theorem sample_eq_getD (p : List Point) (i : ℕ) :
    sample p i = (expand p)[i]?.getD (0, 0) := by
  cases p with
  | nil => rfl
  | cons a as => simp only [sample, expand, sampleFrom_eq_getElem?]

theorem step_zero (a b : Point) : step a b 0 = a := by simp [step]

@[simp] theorem sign_zero : sign 0 = 0 := by simp [sign]

theorem signed_natAbs (z : ℤ) : (z.natAbs : ℤ) * sign z = z := by
  by_cases hz : z = 0
  · simp [hz, sign]
  · rcases lt_or_gt_of_ne hz with hn | hp
    · simp [sign, hz, not_lt.mpr hn.le, Int.natCast_natAbs, abs_of_neg hn]
    · simp [sign, hz, hp, Int.natCast_natAbs, abs_of_pos hp]

theorem step_last (a b : Point)
    (ha : a.1 = b.1 ∨ a.2 = b.2) : step a b (segmentLength a b) = b := by
  rcases a with ⟨x, y⟩
  rcases b with ⟨z, w⟩
  dsimp only [Prod.fst, Prod.snd] at ha
  rcases ha with ha | ha
  · subst z
    simp only [step, segmentLength, sub_self, Int.natAbs_zero, zero_add,
      sign_zero, mul_zero, add_zero, signed_natAbs]
    congr 1 <;> omega
  · subst w
    simp only [step, segmentLength, sub_self, Int.natAbs_zero, add_zero,
      sign_zero, mul_zero, signed_natAbs]
    congr 1 <;> omega

/-- An equivalent right-closed convention, exactly the scientific verifier's loop. -/
def verifierFrom (a : Point) : List Point → List Point
  | [] => []
  | b :: bs =>
    ((List.range (segmentLength a b)).map fun i => step a b (i + 1)) ++ verifierFrom b bs

def verifierExpand : List Point → List Point
  | [] => []
  | a :: as => a :: verifierFrom a as

theorem prefix_shift (a b : Point)
    (ha : a.1 = b.1 ∨ a.2 = b.2) :
    segmentPrefix a b ++ [b] = a :: ((List.range (segmentLength a b)).map fun i => step a b (i+1)) := by
  have he := step_last a b ha
  have hz := step_zero a b
  have h := congrArg (List.map (step a b)) (List.range_succ (n := segmentLength a b))
  have h' := congrArg (List.map (step a b)) (List.range_succ_eq_map (n := segmentLength a b))
  simpa only [segmentPrefix, List.map_append, List.map_singleton, List.map_cons,
    List.map_nil, List.map_map, Function.comp_def, Nat.succ_eq_add_one, he, hz]
    using h.symm.trans h'

theorem expandFrom_verifier (a : Point) (bs : List Point)
    (ha : axisAligned (a :: bs)) : expandFrom a bs = a :: verifierFrom a bs := by
  induction bs generalizing a with
  | nil => rfl
  | cons b bs ih =>
    have hab : a.1 = b.1 ∨ a.2 = b.2 := by
      apply ha (a, b)
      simp
    have htail : axisAligned (b :: bs) := by
      intro ab hab'
      apply ha ab
      simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons] at *
      exact Or.inr hab'
    rw [expandFrom, ih b htail]
    change segmentPrefix a b ++ ([b] ++ verifierFrom b bs) = _
    rw [← List.append_assoc, prefix_shift a b hab]
    simp [verifierFrom]

/-- Zero-length cleanup and every detour/corner have exactly the original loop's semantics. -/
theorem expand_eq_verifier (p : List Point) (ha : axisAligned p) :
    expand p = verifierExpand p := by
  cases p with
  | nil => rfl
  | cons a as => exact expandFrom_verifier a as ha

end D5.S3.Combinatorics.Graph.Products.IntegerPolyline

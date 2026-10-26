/- GID: D5/S3/Combinatorics/BinomialBases/MazorchukXuClosure
   generality: G
   mirror-B: D5/B/S3/Combinatorics/BinomialBases/MazorchukXuClosure
   mirror-E: none(waiver:universal-ordered-closure-arguments)
   anchors: [mathlib/module/Mathlib.Data.Finset.Powerset]
   utility: none
   digest: Literal triangular closure and its ordered-edge rules. -/

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic

/-! The finite triangular family and the universal ordered-edge presentation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MazorchukXu

/-- The source triangle, with nonnegative integer coordinates represented by naturals. -/
def triangle (n : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (n + 1)).product (Finset.range (n + 1))).filter
    (fun p => p.1 ≤ p.2)

/-- The literal repeated-point Condition (star). No distinctness premise is imposed. -/
def Star (Y : Finset (ℕ × ℕ)) : Prop :=
  ∀ (a b c d e f : ℕ), (a, b) ∈ Y → (c, d) ∈ Y → (e, f) ∈ Y →
    a ≤ c → c ≤ b → a ≤ e → e ≤ b → b ≤ d → b ≤ f →
      (max c e, max d f) ∈ Y ∧
        (b < min d f → (b + 1, min d f) ∈ Y)

/-- The number of selected points in the first column. -/
def firstColumnCard (Y : Finset (ℕ × ℕ)) : ℕ :=
  (Y.filter (fun p => p.1 = 0)).card

/-- The literal finite family R(n,k), including the empty subset when appropriate. -/
noncomputable def family (n k : ℕ) : Finset (Finset (ℕ × ℕ)) := by
  classical
  exact (triangle n).powerset.filter (fun Y => Star Y ∧ firstColumnCard Y = k)

/-- The cardinal r(n,k); its first argument is always a natural number. -/
noncomputable def count (n k : ℕ) : ℕ := (family n k).card

/-- The full original all-deficit, all-valid-rank conjecture over rational polynomials. -/
def Conjecture : Prop :=
  ∀ i : ℕ, ∃ p : Polynomial ℚ,
    p.natDegree = 2 * i ∧ p.leadingCoeff = (i.factorial : ℚ)⁻¹ ∧
      ∀ n : ℕ, i ≤ n + 1 → p.eval (n : ℚ) = (count n (n + 1 - i) : ℚ)

/-- The ordered edge corresponding to (a,b-1). -/
def pointEdges (Y : Finset (ℕ × ℕ)) (a b : ℕ) : Prop :=
  a < b ∧ (a, b - 1) ∈ Y

/-- The two universal edge implications P and J, together with strict endpoint order. -/
structure Rules {α : Type*} [LinearOrder α] (E : α → α → Prop) : Prop where
  ordered : ∀ {a b}, E a b → a < b
  propagate : ∀ {a b c d}, E a b → E c d → a ≤ c → c < b → b < d → E b d
  join : ∀ {a b c d e f}, E a b → E c d → E e f →
    a ≤ c → c < b → a ≤ e → e < b → b ≤ d → b ≤ f →
      E (max c e) (max d f)

theorem mem_triangle {n a b : ℕ} : (a, b) ∈ triangle n ↔ a ≤ b ∧ b ≤ n := by
  simp [triangle]
  omega

/-- A literal source equivalence, with all repeated points and both conclusions retained. -/
theorem star_iff_rules {Y : Finset (ℕ × ℕ)}
    (hY : ∀ {a b}, (a, b) ∈ Y → a ≤ b) :
    Star Y ↔ Rules (pointEdges Y) := by
  constructor
  · intro h
    refine ⟨fun h => h.1, ?_, ?_⟩
    · intro a b c d hab hcd hac hcb hbd
      have hsource := (h a (b - 1) c (d - 1) c (d - 1)
        hab.2 hcd.2 hcd.2 hac (by omega) hac (by omega)
        (by omega) (by omega)).2 (by omega)
      have hb : b - 1 + 1 = b := by omega
      simpa only [pointEdges, min_self, hb] using And.intro hbd hsource
    · intro a b c d e f hab hcd hef hac hcb hae heb hbd hbf
      have hsource := (h a (b - 1) c (d - 1) e (f - 1)
        hab.2 hcd.2 hef.2 hac (by omega) hae (by omega)
        (by omega) (by omega)).1
      have hmax : max (d - 1) (f - 1) = max d f - 1 := by omega
      refine ⟨?_, ?_⟩
      · omega
      · simpa only [hmax] using hsource
  · intro h a b c d e f hab hcd hef hac hcb hae heb hbd hbf
    have hab' : pointEdges Y a (b + 1) := ⟨by have := hY hab; omega, by simpa⟩
    have hcd' : pointEdges Y c (d + 1) := ⟨by have := hY hcd; omega, by simpa⟩
    have hef' : pointEdges Y e (f + 1) := ⟨by have := hY hef; omega, by simpa⟩
    have hj := h.join hab' hcd' hef' hac (by omega) hae (by omega)
      (by omega) (by omega)
    have hmax : max (d + 1) (f + 1) - 1 = max d f := by omega
    refine ⟨by simpa only [pointEdges, hmax] using hj.2, ?_⟩
    intro hmin
    rcases le_total d f with hdf | hfd
    · have hp := h.propagate hab' hcd' hac (by omega) (by omega)
      simpa only [Nat.add_sub_cancel, min_eq_left hdf] using hp.2
    · have hp := h.propagate hab' hef' hae (by omega) (by omega)
      simpa only [Nat.add_sub_cancel, min_eq_right hfd] using hp.2

/-- Every member of the finite source family is tested against exactly the edge rules. -/
theorem mem_family_iff {n k : ℕ} {Y : Finset (ℕ × ℕ)} :
    Y ∈ family n k ↔ Y ⊆ triangle n ∧ Rules (pointEdges Y) ∧ firstColumnCard Y = k := by
  classical
  simp only [family, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨hY, hs, hk⟩
    exact ⟨hY, (star_iff_rules (fun h => (mem_triangle.mp (hY h)).1)).mp hs, hk⟩
  · rintro ⟨hY, hs, hk⟩
    exact ⟨hY, (star_iff_rules (fun h => (mem_triangle.mp (hY h)).1)).mpr hs, hk⟩

end D5.S3.Combinatorics.MazorchukXu

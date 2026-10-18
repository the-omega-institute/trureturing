/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/IntegerPath
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/IntegerPath
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integer edges meeting a consecutive path either repeat or extend an endpoint. -/
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.Source
import Mathlib.Data.Int.Interval

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

/-- Left endpoints and vertices of a path containing n integer edges. -/
def pathEdges (L : ℤ) (n : ℕ) : Finset ℤ := Finset.Icc L (L + n - 1)

def pathVertices (L : ℤ) (n : ℕ) : Finset ℤ := Finset.Icc L (L + n)

/-- The three cases include arbitrary negative edge indices. -/
theorem integer_edge_trichotomy (L e : ℤ) {n : ℕ} (hn : 1 ≤ n) :
    e ∈ pathEdges L n ∨ (e = L - 1 ∨ e = L + n) ∨
      Disjoint ({e, e + 1} : Finset ℤ) (pathVertices L n) := by
  by_cases hi : e ∈ pathEdges L n
  · exact Or.inl hi
  by_cases hl : e = L - 1
  · exact Or.inr (Or.inl (Or.inl hl))
  by_cases hr : e = L + n
  · exact Or.inr (Or.inl (Or.inr hr))
  right; right
  apply Finset.disjoint_left.mpr
  intro v hv hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  simp only [pathVertices, Finset.mem_Icc] at hp
  simp only [pathEdges, Finset.mem_Icc, not_and_or, not_le] at hi
  rcases hv with rfl | rfl <;> omega

theorem extend_left (L : ℤ) (n : ℕ) :
    insert (L - 1) (pathEdges L n) = pathEdges (L - 1) (n + 1) := by
  ext e
  simp only [Finset.mem_insert, pathEdges, Finset.mem_Icc, Nat.cast_add, Nat.cast_one]
  omega

theorem extend_right (L : ℤ) (n : ℕ) :
    insert (L + n) (pathEdges L n) = pathEdges L (n + 1) := by
  ext e
  simp only [Finset.mem_insert, pathEdges, Finset.mem_Icc, Nat.cast_add, Nat.cast_one]
  omega

theorem vertices_card (L : ℤ) (n : ℕ) : (pathVertices L n).card = n + 1 := by
  simp only [pathVertices, Int.card_Icc]
  omega

/-- Adjacent equalities on an integer interval force a single common spin value. -/
theorem path_constant_iff (L : ℤ) (n : ℕ) (S : Spins) :
    (∀ e ∈ pathEdges L n, S e = S (e + 1)) ↔
      ∀ v ∈ pathVertices L n, S v = S L := by
  constructor
  · intro h v hv
    have hv' : L ≤ v ∧ v ≤ L + n := by simpa [pathVertices] using hv
    have key : ∀ m : ℕ, m ≤ n → S (L + m) = S L := by
      intro m hm
      induction m with
      | zero => simp
      | succ m ih =>
        have hm' : m ≤ n := by omega
        have he : L + m ∈ pathEdges L n := by
          simp only [pathEdges, Finset.mem_Icc]
          constructor <;> omega
        have hh := h _ he
        have hi := ih hm'
        have hc : L + (m + 1 : ℕ) = L + m + 1 := by push_cast; ring
        rw [hc, ← hh, hi]
    have hc : L + (v - L).toNat = v := by omega
    have hm : (v - L).toNat ≤ n := by omega
    have hp := key (v - L).toNat hm
    rw [hc] at hp
    exact hp
  · intro h e he
    have he' : L ≤ e ∧ e ≤ L + n - 1 := by simpa [pathEdges] using he
    have h0 : e ∈ pathVertices L n := by simp only [pathVertices, Finset.mem_Icc]; omega
    have h1 : e + 1 ∈ pathVertices L n := by simp only [pathVertices, Finset.mem_Icc]; omega
    exact (h e h0).trans (h _ h1).symm

/-- A target contained in a zero path specifies the spin of every vertex. -/
theorem path_target_iff (L q : ℤ) (n : ℕ) (S : Spins) (s : Bool)
    (hq : q ∈ pathVertices L n) :
    ((∀ e ∈ pathEdges L n, S e = S (e + 1)) ∧ S q = s) ↔
      ∀ v ∈ pathVertices L n, S v = s := by
  constructor
  · rintro ⟨h, hs⟩
    have hc := (path_constant_iff L n S).1 h
    intro v hv
    exact (hc v hv).trans ((hc q hq).symm.trans hs)
  · intro h
    refine ⟨(path_constant_iff L n S).2 ?_, h q hq⟩
    intro v hv
    have hl : L ∈ pathVertices L n := by simp [pathVertices]
    exact (h v hv).trans (h L hl).symm

/-- A target outside a consecutive k-edge path forces a remote original-clock address. -/
theorem detached_path_remote (j : Bool) {k : ℕ} (hk : 1 ≤ k) (L : ℤ)
    (hq : j.toInt ∉ pathVertices L k) :
    ∃ e ∈ pathEdges L k, (2 * k + 1 : ℤ) ≤ |2 * e + (!j).toInt - j.toInt| := by
  have hsep : j.toInt < L ∨ L + k < j.toInt := by
    simp only [pathVertices, Finset.mem_Icc, not_and_or, not_le] at hq
    exact hq
  rcases hsep with hr | hl
  · refine ⟨L + k - 1, ?_, ?_⟩
    · simp only [pathEdges, Finset.mem_Icc]; constructor <;> omega
    · have hle := le_abs_self (2 * (L + k - 1) + (!j).toInt - j.toInt)
      cases j <;> simp only [Bool.not_false, Bool.not_true, Bool.toInt_false,
        Bool.toInt_true] at * <;> omega
  · refine ⟨L, ?_, ?_⟩
    · simp only [pathEdges, Finset.mem_Icc]; constructor <;> omega
    · have hle := neg_le_abs (2 * L + (!j).toInt - j.toInt)
      cases j <;> simp only [Bool.not_false, Bool.not_true, Bool.toInt_false,
        Bool.toInt_true] at * <;> omega

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

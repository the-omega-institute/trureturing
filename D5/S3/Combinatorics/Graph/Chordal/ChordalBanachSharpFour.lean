/- GID: D5/S3/Combinatorics/Graph/Chordal/ChordalBanachSharpFour
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Chordal/ChordalBanachSharpFour
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rolling clique separators force Banach gain reconstruction errors approaching four. -/

import D5.S3.Combinatorics.Graph.Chordal.Dirac
import D5.S3.Combinatorics.Graph.Chordal.ChordalCycleFillingNorm
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Order.Sum.Order

namespace SimpleGraph.ChordalReconstruction

open scoped BigOperators

noncomputable section

private def residue {w : ℕ} (r : Fin w) (t : ℕ) : ℝ :=
  (if t % w = r.val then 1 else 0) - 1 / (w : ℝ)

private theorem residue_bounds {w : ℕ} (r : Fin w) (t : ℕ) :
    -1 ≤ residue r t ∧ residue r t ≤ 1 := by
  have hw : (1 : ℝ) ≤ w := by exact_mod_cast (Nat.succ_le_of_lt (Nat.zero_lt_of_lt r.isLt))
  have h₀ : (0 : ℝ) ≤ 1 / w := by positivity
  have h₁ : (1 : ℝ) / w ≤ 1 := (div_le_one (by linarith)).2 hw
  unfold residue
  split <;> constructor <;> linarith

private theorem sum_residue {w : ℕ} (hw : 0 < w) (t : ℕ) :
    ∑ r : Fin w, residue r t = 0 := by
  have hw' : (w : ℝ) ≠ 0 := by positivity
  let a : Fin w := ⟨t % w, Nat.mod_lt t hw⟩
  have he (r : Fin w) : (t % w = r.val) ↔ a = r := by
    change a.val = r.val ↔ a = r
    exact ⟨Fin.ext, congrArg Fin.val⟩
  simp [residue, he, Finset.sum_sub_distrib, div_eq_mul_inv, hw']

private def bandForward {w : ℕ} (r : Fin w) (u v : ℕ) : ℝ :=
  residue r v + if v - u = w then residue r u else 0

private def band {w : ℕ} (r : Fin w) (u v : ℕ) : ℝ :=
  if u < v then bandForward r u v else if v < u then -bandForward r v u else 0

private theorem band_reverse {w : ℕ} (r : Fin w) (u v : ℕ) :
    band r v u = -band r u v := by
  rcases lt_trichotomy u v with h | rfl | h
  · simp [band, h, not_lt_of_ge h.le]
  · simp [band]
  · simp [band, h, not_lt_of_ge h.le]

private theorem band_abs_le {w : ℕ} (r : Fin w) (u v : ℕ) :
    |band r u v| ≤ 2 := by
  have h (i j : ℕ) : |bandForward r i j| ≤ 2 := by
    rw [abs_le]
    unfold bandForward
    split <;> constructor <;> linarith [(residue_bounds r i).1, (residue_bounds r i).2,
      (residue_bounds r j).1, (residue_bounds r j).2]
  unfold band
  split
  · exact h _ _
  · split
    · rw [abs_neg]
      exact h _ _
    · norm_num

private theorem band_sorted_defect {w : ℕ} (r : Fin w) {u v z : ℕ}
    (hua : u < v) (hvb : v < z) (hspan : z - u ≤ w) :
    |band r u v + band r v z - band r u z| ≤ 1 := by
  have huv : v - u ≠ w := by omega
  have hvz : z - v ≠ w := by omega
  simp only [band, hua, hvb, hua.trans hvb, ite_true, bandForward, huv, hvz, ite_false]
  by_cases h : z - u = w
  · simp only [h, ite_true]
    rw [show residue r v + 0 + (residue r z + 0) - (residue r z + residue r u) =
      residue r v - residue r u by ring, abs_le]
    unfold residue
    split <;> split <;> constructor <;> linarith
  · simp only [h, ite_false, add_zero, add_sub_cancel_right]
    exact abs_le.mpr (residue_bounds r v)

private theorem band_long {w : ℕ} (r : Fin w) {t : ℕ} (ht : t % w = r.val) :
    band r t (t + w) = 2 - 2 / (w : ℝ) := by
  have h : t < t + w := by omega
  have hmod : (t + w) % w = r.val := by simpa using ht
  simp [band, h, bandForward, residue, ht, hmod]
  ring

private def laneStart {w : ℕ} (r : Fin w) : ℕ := if r.val = 0 then w else r.val

private theorem laneStart_spec {w : ℕ} (r : Fin w) :
    0 < laneStart r ∧ laneStart r ≤ w ∧ laneStart r % w = r.val := by
  unfold laneStart
  split
  · rename_i h
    simp [h, show 0 < w by omega]
  · rename_i h
    exact ⟨Nat.pos_of_ne_zero h, r.isLt.le, Nat.mod_eq_of_lt r.isLt⟩

private theorem band_average {w n : ℕ} (hw : 0 < w)
    (H : Fin w → ℕ → ℝ) (hH : ∀ t, ∑ r, H r t = 0) (R δ : ℝ)
    (bound : ∀ (r : Fin w) (u v : ℕ), u < v → v ≤ u + w → v ≤ n * w + w + 1 →
      2 + band r u v + H r u - H r v ≤ R + δ) :
    (n : ℝ) * (4 - 2 / (w : ℝ)) ≤ ((n : ℝ) + 2) * (R + δ) := by
  let finish := n * w + w + 1
  have lane (r : Fin w) :
      (n : ℝ) * (4 - 2 / (w : ℝ)) + H r 0 - H r finish ≤
        ((n : ℝ) + 2) * (R + δ) := by
    let start := laneStart r
    have ⟨hstart, hstartw, hres⟩ := laneStart_spec r
    change 0 < start at hstart
    change start ≤ w at hstartw
    change start % w = r.val at hres
    have hin := bound r 0 start (by omega) (by omega) (by omega)
    have ha := (abs_le.mp (band_abs_le r 0 start)).1
    have hout := bound r (start + n * w) finish (by dsimp [finish]; omega)
      (by dsimp [finish]; omega) (by rfl)
    have hb := (abs_le.mp (band_abs_le r (start + n * w) finish)).1
    have steps (k : ℕ) (hk : k ≤ n) :
        (k : ℝ) * (4 - 2 / (w : ℝ)) + H r start - H r (start + k * w) ≤
          (k : ℝ) * (R + δ) := by
      induction k with
      | zero => simp
      | succ k ih =>
        have hm : k * w ≤ n * w := Nat.mul_le_mul_right _ (by omega)
        have hm' : (k + 1) * w ≤ n * w := Nat.mul_le_mul_right _ hk
        have hd :
            2 + band r (start + k * w) (start + (k + 1) * w) +
              H r (start + k * w) - H r (start + (k + 1) * w) ≤ R + δ :=
          bound r _ _ (by rw [Nat.succ_mul]; omega)
            (by rw [Nat.succ_mul]; omega) (by omega)
        have hmres : (start + k * w) % w = r.val := by simpa using hres
        rw [Nat.succ_mul, ← add_assoc, band_long r hmres] at hd
        rw [Nat.succ_mul, ← add_assoc, Nat.cast_succ]
        nlinarith [ih (by omega)]
    linarith [steps n le_rfl]
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin w))) fun r _ => lane r
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hH, add_zero, sub_zero] at hsum
  exact le_of_mul_le_mul_left hsum (by positivity : (0 : ℝ) < w)

private theorem band_parameters (ε : ℝ) (hε : 0 < ε) :
    ∃ m : ℕ, 1 ≤ m ∧ ((m : ℝ) + 2) * (4 - ε / 2) <
      (m : ℝ) * (4 - 2 / (m : ℝ)) := by
  obtain ⟨m, hm⟩ := exists_nat_gt (max 1 (20 / ε))
  have h₁ : (1 : ℝ) < m := (le_max_left _ _).trans_lt hm
  have h₂ : (20 : ℝ) < m * ε := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hm)
  have hm' : (m : ℝ) ≠ 0 := by linarith
  have he : (m : ℝ) * (4 - 2 / (m : ℝ)) = 4 * (m : ℝ) - 2 := by
    field_simp
  refine ⟨m, by exact_mod_cast h₁.le, ?_⟩
  rw [he]
  nlinarith

private theorem band_contradiction (ε : ℝ) {m : ℕ}
    (hm : 1 ≤ m) (hparam : ((m : ℝ) + 2) * (4 - ε / 2) <
      (m : ℝ) * (4 - 2 / (m : ℝ)))
    (H : Fin m → ℕ → ℝ) (hH : ∀ t, ∑ r, H r t = 0)
    (bound : ∀ (r : Fin m) (u v : ℕ), u < v → v ≤ u + m → v ≤ m * m + m + 1 →
      2 + band r u v + H r u - H r v ≤ (4 - ε) + ε / 2) : False := by
  have h := band_average (n := m) (show 0 < m by omega) H hH (4 - ε) (ε / 2) bound
  rw [show (4 - ε) + ε / 2 = 4 - ε / 2 by ring] at h
  exact hparam.not_ge h

private theorem skew_defect_le {A : Type*} [LinearOrder A] (f : A → A → ℝ)
    (hs : ∀ x y, f y x = -f x y) (P : A → A → Prop)
    (symm : ∀ x y, P x y → P y x)
    (sorted : ∀ x y z, x < y → y < z → P x y → P y z → P x z →
      |f x y + f y z - f x z| ≤ 1)
    (x y z : A) (hxy : P x y) (hyz : P y z) (hxz : P x z) :
    |f x y + f y z - f x z| ≤ 1 := by
  have diag (x : A) : f x x = 0 := by linarith [hs x x]
  have swapLeft (a b c : A) :
      |f b a + f a c - f b c| = |f a b + f b c - f a c| := by
    rw [hs a b, show -f a b + f a c - f b c = -(f a b + f b c - f a c) by ring, abs_neg]
  have swapRight (a b c : A) :
      |f a c + f c b - f a b| = |f a b + f b c - f a c| := by
    rw [hs b c, show f a c + -f b c - f a b = -(f a b + f b c - f a c) by ring, abs_neg]
  rcases eq_or_ne x y with rfl | hn₁
  · simp [diag]
  rcases eq_or_ne y z with rfl | hn₂
  · simp [diag]
  rcases eq_or_ne x z with rfl | hn₃
  · simp [diag, hs x y]
  rcases lt_or_gt_of_ne hn₁ with h₁ | h₁ <;>
    rcases lt_or_gt_of_ne hn₂ with h₂ | h₂ <;>
    rcases lt_or_gt_of_ne hn₃ with h₃ | h₃
  · exact sorted x y z h₁ h₂ hxy hyz hxz
  · exact ((h₁.trans h₂).not_gt h₃).elim
  · rw [← swapRight x y z]
    exact sorted x z y h₃ h₂ hxz (symm _ _ hyz) hxy
  · rw [← swapRight x y z, ← swapLeft x z y]
    exact sorted z x y h₃ h₁ (symm _ _ hxz) hxy (symm _ _ hyz)
  · rw [← swapLeft x y z]
    exact sorted y x z h₁ h₃ (symm _ _ hxy) hxz hyz
  · rw [← swapLeft x y z, ← swapRight y x z]
    exact sorted y z x h₂ h₃ hyz (symm _ _ hxz) (symm _ _ hxy)
  · exact ((h₂.trans h₁).not_gt h₃).elim
  · rw [← swapLeft x y z, ← swapRight y x z, ← swapLeft y z x]
    exact sorted z y x h₂ h₁ (symm _ _ hyz) (symm _ _ hxy) (symm _ _ hxz)

private abbrev Tags := ℕ ⊕ Bool

private def tagPair (w j i : ℕ) : Tags → Tags → Prop
  | .inl a, .inl b => a ≤ b + w ∧ b ≤ a + w
  | .inl a, .inr false | .inr false, .inl a => j ≤ a ∧ a ≤ i
  | .inl a, .inr true | .inr true, .inl a => a = i
  | .inr _, .inr _ => True

private def tagValue {w : ℕ} (r : Fin w) (i : ℕ) : Tags → Tags → ℝ
  | .inl a, .inl b => band r a b
  | .inl a, .inr false => if a = i then 0 else band r a i + 1
  | .inr false, .inl a => -(if a = i then 0 else band r a i + 1)
  | .inr false, .inr true => 1
  | .inr true, .inr false => -1
  | _, _ => 0

private theorem tagPair_symm (w j i : ℕ) (x y : Tags) :
    tagPair w j i x y → tagPair w j i y x := by
  cases x using Sum.rec <;> cases y using Sum.rec
  · exact And.symm
  · rename_i b
    cases b <;> exact id
  · rename_i b a
    cases b <;> exact id
  · rename_i a b
    cases a <;> cases b <;> exact id

private theorem tagValue_skew {w : ℕ} (r : Fin w) (i : ℕ) (x y : Tags) :
    tagValue r i y x = -tagValue r i x y := by
  cases x using Sum.rec <;> cases y using Sum.rec
  · apply band_reverse
  · rename_i b
    cases b <;> simp [tagValue]
  · rename_i b a
    cases b <;> simp [tagValue]
  · rename_i a b
    cases a <;> cases b <;> norm_num [tagValue]

private theorem tagValue_abs {w : ℕ} (r : Fin w) (i : ℕ) (x y : Tags) :
    |tagValue r i x y| ≤ 3 := by
  cases x using Sum.rec <;> cases y using Sum.rec
  · exact (band_abs_le _ _ _).trans (by norm_num)
  · rename_i a b
    cases b
    · by_cases h : a = i
      · simp [tagValue, h]
      · simp only [tagValue, h, ite_false, abs_le]
        obtain ⟨h₁, h₂⟩ := abs_le.mp (band_abs_le r a i)
        constructor <;> linarith
    · norm_num [tagValue]
  · rw [tagValue_skew r i]
    rw [abs_neg]
    rename_i b a
    cases b
    · by_cases h : a = i
      · simp [tagValue, h]
      · simp only [tagValue, h, ite_false, abs_le]
        obtain ⟨h₁, h₂⟩ := abs_le.mp (band_abs_le r a i)
        constructor <;> linarith
    · norm_num [tagValue]
  · rename_i a b
    cases a <;> cases b <;> norm_num [tagValue]

private theorem tagValue_defect {w : ℕ} (r : Fin w) {j i : ℕ}
    (hwidth : i ≤ j + w) (x y z : Tags)
    (hxy : tagPair w j i x y) (hyz : tagPair w j i y z) (hxz : tagPair w j i x z) :
    |tagValue r i x y + tagValue r i y z - tagValue r i x z| ≤ 1 := by
  letI : LinearOrder Tags := LinearOrder.lift' (toLex : Tags → ℕ ⊕ₗ Bool) (fun _ _ h => congrArg ofLex h)
  refine skew_defect_le (tagValue r i) (tagValue_skew r i)
    (tagPair w j i) (tagPair_symm w j i) ?_ x y z hxy hyz hxz
  intro a b c hab hbc hab' hbc' hac'
  cases a using Sum.rec <;> cases b using Sum.rec <;> cases c using Sum.rec
  · rename_i a b c
    have h₁ : a < b := Sum.Lex.inl_lt_inl_iff.mp hab
    have h₂ : b < c := Sum.Lex.inl_lt_inl_iff.mp hbc
    have h₃ : c ≤ a + w := hac'.2
    exact band_sorted_defect r h₁ h₂ (by omega)
  · rename_i a b t
    cases t
    · obtain ⟨hja, hai⟩ := hac'
      obtain ⟨hjb, hbi⟩ := hbc'
      have habn : a < b := Sum.Lex.inl_lt_inl_iff.mp hab
      have hani : a ≠ i := by omega
      by_cases h : b = i
      · subst b
        simp [tagValue, hani]
      · have hbi' : b < i := by omega
        simp only [tagValue, h, hani, ite_false]
        rw [show band r a b + (band r b i + 1) - (band r a i + 1) =
          band r a b + band r b i - band r a i by ring]
        exact band_sorted_defect r habn hbi' (by omega)
    · have ha : a = i := hac'
      have hb : b = i := hbc'
      exact (Sum.Lex.inl_lt_inl_iff.mp hab).ne (ha.trans hb.symm) |>.elim
  · exact (Sum.Lex.not_inr_lt_inl hbc).elim
  · rename_i a s t
    have hst : s < t := Sum.Lex.inr_lt_inr_iff.mp hbc
    cases s <;> cases t
    · exact (lt_irrefl _ hst).elim
    · have ha : a = i := hac'
      subst a
      norm_num [tagValue]
    · exact (by decide : ¬true < false) hst |>.elim
    · exact (lt_irrefl _ hst).elim
  · exact (Sum.Lex.not_inr_lt_inl hab).elim
  · exact (Sum.Lex.not_inr_lt_inl hab).elim
  · exact (Sum.Lex.not_inr_lt_inl hbc).elim
  · rename_i a b c
    have h₁ : a < b := Sum.Lex.inr_lt_inr_iff.mp hab
    have h₂ : b < c := Sum.Lex.inr_lt_inr_iff.mp hbc
    cases a <;> cases b <;> cases c <;>
      first
      | exact (lt_irrefl _ h₁).elim
      | exact (lt_irrefl _ h₂).elim
      | exact ((by decide : ¬true < false) h₁).elim
      | exact ((by decide : ¬true < false) h₂).elim

section RollingGraph

variable {B X : Type*} [Fintype B] [Fintype X]

/-- The ancestors of each block are linearly ordered, and each surviving
label at a descendant survives at every intermediate block. -/
private structure RollingData (B X : Type*) where
  depth : B → ℕ
  ancestor : B → B → Prop
  refl (b : B) : ancestor b b
  trans {a b c : B} : ancestor a b → ancestor b c → ancestor a c
  depth_lt {a b : B} : ancestor a b → a ≠ b → depth a < depth b
  comparable {a b c : B} : ancestor a c → ancestor b c → ancestor a b ∨ ancestor b a
  retain : B → B → Set X
  nested {a b c : B} : ancestor b c → retain a c ⊆ retain a b
  root : B
  earlier (b : B) : b = root ∨ ∃ a, ancestor a b ∧ a ≠ b ∧ (retain a b).Nonempty

private def rolling (D : RollingData B X) : SimpleGraph (B × X) where
  Adj u v := u ≠ v ∧ (u.1 = v.1 ∨
    (D.ancestor u.1 v.1 ∧ u.2 ∈ D.retain u.1 v.1) ∨
    (D.ancestor v.1 u.1 ∧ v.2 ∈ D.retain v.1 u.1))
  symm := ⟨by
    intro u v h
    exact ⟨h.1.symm, h.2.elim (fun he => Or.inl he.symm)
      (fun hr => Or.inr (Or.symm hr))⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private theorem rolling_earlier (D : RollingData B X) {u v : B × X}
    (huv : (rolling D).Adj u v) (hd : D.depth u.1 ≤ D.depth v.1) :
    D.ancestor u.1 v.1 ∧ (u.1 = v.1 ∨ u.2 ∈ D.retain u.1 v.1) := by
  by_cases he : u.1 = v.1
  · exact ⟨he ▸ D.refl u.1, Or.inl he⟩
  rcases huv.2 with h | h | h
  · exact (he h).elim
  · exact ⟨h.1, Or.inr h.2⟩
  · exact ((D.depth_lt h.1 (fun h' => he h'.symm)).not_ge hd).elim

private theorem rolling_clique (D : RollingData B X) (v : B × X) :
    (rolling D).IsClique {u | D.depth u.1 ≤ D.depth v.1 ∧ (rolling D).Adj u v} := by
  intro u hu z hz hne
  have hu' := rolling_earlier D hu.2 hu.1
  have hz' := rolling_earlier D hz.2 hz.1
  refine ⟨hne, ?_⟩
  by_cases he : u.1 = z.1
  · exact Or.inl he
  rcases D.comparable hu'.1 hz'.1 with h | h
  · have hv : u.1 ≠ v.1 := by
      intro hh
      exact (D.depth_lt h he).not_ge (hh ▸ hz.1)
    exact Or.inr (Or.inl ⟨h, D.nested hz'.1 (hu'.2.resolve_left hv)⟩)
  · have hv : z.1 ≠ v.1 := by
      intro hh
      exact (D.depth_lt h (fun h' => he h'.symm)).not_ge (hh ▸ hu.1)
    exact Or.inr (Or.inr ⟨h, D.nested hu'.1 (hz'.2.resolve_left hv)⟩)

private theorem rolling_chordal (D : RollingData B X) : (rolling D).IsChordal := by
  classical
  intro x c hc hl
  obtain ⟨v, hv, hmax⟩ :=
    Finset.exists_max_image c.support.toFinset (fun u => D.depth u.1) ⟨x, by simp⟩
  have hmem : v ∈ c.support := by simpa using hv
  let d := c.rotate v hmem
  have hd : d.IsCycle := hc.rotate hmem
  have hn : 4 ≤ d.length := by simpa [d] using hl
  have support (u : B × X) (hu : u ∈ d.support) : u ∈ c.support := by
    rw [← Walk.cons_tail_support] at hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact hmem
    · exact List.mem_of_mem_tail ((c.support_rotate v hmem).mem_iff.mp hu)
  have hs := support d.snd (d.getVert_mem_support 1)
  have hp := support d.penultimate (d.getVert_mem_support (d.length - 1))
  refine ⟨d.snd, d.penultimate, hs, hp, rolling_clique D v
    ⟨hmax _ (by simpa using hs), (d.adj_snd hd.not_nil).symm⟩
    ⟨hmax _ (by simpa using hp), d.adj_penultimate hd.not_nil⟩
    hd.snd_ne_penultimate, ?_⟩
  intro edge
  have mem := Walk.adj_toSubgraph_iff_mem_edges.mpr ((c.rotate_edges v hmem).mem_iff.mpr edge)
  change d.getVert (d.length - 1) ∈ d.toSubgraph.neighborSet (d.getVert 1) at mem
  rw [hd.neighborSet_toSubgraph_internal (by omega) (by omega)] at mem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Nat.sub_self] at mem
  rcases mem with hm | hm <;>
    have eq := hd.getVert_injOn' (by simp : d.length - 1 ∈ {n | n ≤ d.length - 1})
      (by simp <;> omega) hm <;> omega

private theorem rolling_connected (D : RollingData B X) (x₀ : X) :
    (rolling D).Connected := by
  let o : B × X := (D.root, x₀)
  have go (v : B × X) : (rolling D).Reachable o v := by
    generalize hd : D.depth v.1 = m
    induction m using Nat.strong_induction_on generalizing v with
    | h m ih =>
      rcases D.earlier v.1 with hb | ⟨a, ha, hne, x, hx⟩
      · by_cases h : o = v
        · exact h ▸ SimpleGraph.Reachable.refl o
        · have hed : (rolling D).Adj o v := ⟨h, Or.inl hb.symm⟩
          exact hed.reachable
      · have ha' : D.depth (a, x).1 < m := by rw [← hd]; exact D.depth_lt ha hne
        have hed : (rolling D).Adj (a, x) v := ⟨fun h => hne (congrArg Prod.fst h),
          Or.inr (Or.inl ⟨ha, hx⟩)⟩
        exact (ih _ ha' (a, x) rfl).trans hed.reachable
  letI : Nonempty (B × X) := ⟨o⟩
  exact ⟨fun u v => (go u).symm.trans (go v)⟩

private theorem rolling_short_walk {B X : Type*} (D : RollingData B X) (a : X) (v : B × X) :
    ∃ p : (rolling D).Walk (D.root, a) v, p.length ≤ D.depth v.1 + 1 := by
  let o : B × X := (D.root, a)
  generalize hd : D.depth v.1 = m
  induction m using Nat.strong_induction_on generalizing v with
  | h m ih =>
    rcases D.earlier v.1 with hb | ⟨b, hb, hne, x, hx⟩
    · by_cases h : o = v
      · subst v
        exact ⟨Walk.nil, by simp⟩
      · have ed : (rolling D).Adj o v := ⟨h, Or.inl hb.symm⟩
        exact ⟨Walk.cons ed Walk.nil, by simp⟩
    · have hd' : D.depth (b, x).1 < m := by rw [← hd]; exact D.depth_lt hb hne
      obtain ⟨p, hp⟩ := ih _ hd' (b,x) rfl
      have ed : (rolling D).Adj (b,x) v :=
        ⟨fun h => hne (congrArg Prod.fst h), Or.inr (Or.inl ⟨hb,hx⟩)⟩
      exact ⟨p.concat ed, by simp only [Walk.length_concat]; omega⟩

end RollingGraph

section Histories

/-- The cardinalities of the nested retention sets, indexed by birth and stage. -/
private structure Retention (n q : ℕ) where
  count : Fin (n + 1) → Fin (n + 1) → ℕ
  root (j : Fin (n + 1)) : count j 0 = q
  positivePrevious (i : Fin (n + 1)) (hi : 0 < i.val) :
    0 < count ⟨i.val - 1, by omega⟩ i

private abbrev Step (n q k : ℕ) := (Fin (n + 1) → Finset (Fin q)) × Fin (k + 1)

private def rootStep (n q k : ℕ) : Step n q k := (fun _ => Finset.univ, 0)

private structure History {n q : ℕ} (P : Retention n q) (k : ℕ) where
  stage : Fin (n + 1)
  step : Fin (n + 1) → Step n q k
  root_step : step 0 = rootStep n q k
  beyond (i : Fin (n + 1)) : stage < i → step i = rootStep n q k
  cardinal (j i : Fin (n + 1)) : i ≤ stage → ((step i).1 j).card = P.count j i
  nested (j i l : Fin (n + 1)) :
    i ≤ l → l ≤ stage → (step l).1 j ⊆ (step i).1 j

private theorem History.ext' {n q k : ℕ} {P : Retention n q} {b c : History P k}
    (hs : b.stage = c.stage) (hf : b.step = c.step) : b = c := by
  cases b
  cases c
  cases hs
  cases hf
  rfl

private noncomputable instance {n q k : ℕ} {P : Retention n q} : DecidableEq (History P k) :=
  Classical.decEq _

private noncomputable instance {n q k : ℕ} {P : Retention n q} : Fintype (History P k) := by
  classical
  have : Finite (History P k) :=
    Finite.of_injective (fun b : History P k => (b.stage, b.step))
      (fun _ _ h => History.ext' (congrArg Prod.fst h) (congrArg Prod.snd h))
  exact Fintype.ofFinite _

private def History.initial {n q k : ℕ} (P : Retention n q) : History P k where
  stage := 0
  step := fun _ => rootStep n q k
  root_step := rfl
  beyond _ _ := rfl
  cardinal j i hi := by
    have he : i = 0 := le_antisymm hi (Fin.zero_le i)
    simpa [he, rootStep] using (P.root j).symm
  nested _ _ _ _ _ := Finset.Subset.rfl

private def History.IsPrefix {n q k : ℕ} {P : Retention n q} (b c : History P k) : Prop :=
  b.stage ≤ c.stage ∧ ∀ i, i ≤ b.stage → b.step i = c.step i

private theorem History.IsPrefix.eq_of_stage_eq {n q k : ℕ} {P : Retention n q}
    {b c : History P k} (h : b.IsPrefix c) (he : b.stage = c.stage) : b = c := by
  apply History.ext' he
  funext i
  by_cases hi : i ≤ b.stage
  · exact h.2 i hi
  · exact (b.beyond i (lt_of_not_ge hi)).trans (c.beyond i (he ▸ lt_of_not_ge hi)).symm

private def History.prefix {n q k : ℕ} {P : Retention n q} (b : History P k)
    (t : Fin (n + 1)) (ht : t ≤ b.stage) : History P k where
  stage := t
  step i := if i ≤ t then b.step i else rootStep n q k
  root_step := by simp [b.root_step]
  beyond i hi := if_neg (not_le_of_gt hi)
  cardinal j i hi := by simpa [hi] using b.cardinal j i (hi.trans ht)
  nested j i l hil hl := by
    simpa [hl, hil.trans hl] using b.nested j i l hil (hl.trans ht)

private theorem History.prefix_spec {n q k : ℕ} {P : Retention n q}
    (b : History P k) (t : Fin (n + 1)) (ht : t ≤ b.stage) :
    (b.prefix t ht).IsPrefix b :=
  ⟨ht, fun i hi => if_pos hi⟩

private def historyData {n q k : ℕ} (P : Retention n q) :
    RollingData (History P k) (Fin q) where
  depth b := b.stage.val
  ancestor := History.IsPrefix
  refl b := ⟨le_rfl, fun _ _ => rfl⟩
  trans h₁ h₂ := ⟨h₁.1.trans h₂.1, fun i hi => (h₁.2 i hi).trans (h₂.2 i (hi.trans h₁.1))⟩
  depth_lt h hne := lt_of_le_of_ne h.1 (fun he => hne (h.eq_of_stage_eq (Fin.ext he)))
  comparable := by
    intro a b c h₁ h₂
    rcases le_total a.stage b.stage with h | h
    · exact Or.inl ⟨h, fun i hi => (h₁.2 i hi).trans (h₂.2 i (hi.trans h)).symm⟩
    · exact Or.inr ⟨h, fun i hi => (h₂.2 i hi).trans (h₁.2 i (hi.trans h)).symm⟩
  retain a b := ((b.step b.stage).1 a.stage : Set (Fin q))
  nested := by
    intro a b c h x hx
    change x ∈ (b.step b.stage).1 a.stage
    rw [h.2 b.stage le_rfl]
    exact c.nested a.stage b.stage c.stage h.1 le_rfl hx
  root := History.initial P
  earlier b := by
    by_cases hb : b.stage = 0
    · exact Or.inl (History.IsPrefix.eq_of_stage_eq
        (b := History.initial P) (c := b)
        ⟨Fin.zero_le _, fun i hi => by
          have he : i = 0 := le_antisymm hi (Fin.zero_le i)
          simp [he, History.initial, b.root_step]⟩ hb.symm).symm
    · have hpos : 0 < b.stage.val := Nat.pos_of_ne_zero (fun h => hb (Fin.ext h))
      let a : Fin (n + 1) := ⟨b.stage.val - 1, by omega⟩
      have ha : a < b.stage := by change b.stage.val - 1 < b.stage.val; omega
      refine Or.inr ⟨b.prefix a ha.le, b.prefix_spec a ha.le, ?_, ?_⟩
      · exact fun he => ha.ne (congrArg History.stage he)
      · change ((b.step b.stage).1 a : Set (Fin q)).Nonempty
        rw [Finset.coe_nonempty, ← Finset.card_pos, b.cardinal _ _ le_rfl]
        exact P.positivePrevious b.stage hpos

end Histories

section RootNormalization

variable {n q k : ℕ} {P : Retention n q}

private abbrev HV (P : Retention n q) (k : ℕ) := History P k × Fin q

private theorem History.stage_zero {b : History P k} (h : b.stage = 0) :
    b = History.initial P :=
  ((historyData P).earlier b).resolve_right (by
    rintro ⟨c,hpre,hne,_⟩
    have hlt := (historyData P).depth_lt hpre hne
    change c.stage.val < b.stage.val at hlt
    simp [h] at hlt)

private def rootMass (v : HV P k) : ℝ := if v.1.stage = 0 then (q : ℝ)⁻¹ else 0

private def centerRoot (p : HV P k → Chains (HV P k)) (v : HV P k) : Chains (HV P k) :=
  p v - meanChain (fun a : Fin q => p (History.initial P,a))

private theorem centerRoot_boundary (hq : 0 < q) (o : HV P k)
    (p : HV P k → Chains (HV P k))
    (hp : ∀ v, boundary (p v) = Pi.single v 1 - Pi.single o 1) (v : HV P k) :
    boundary (centerRoot p v) = Pi.single v 1 - rootMass := by
  classical
  funext x
  rw [centerRoot, boundary_sub, hp, Pi.sub_apply, Pi.sub_apply, Pi.sub_apply, boundary_mean]
  have hc : ∑ a : Fin q, boundary (p (History.initial P,a)) x =
      (if x.1.stage = 0 then 1 else 0) - (q : ℝ) * Pi.single (M := fun _ : HV P k => ℝ) o 1 x := by
    simp only [hp, Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    congr 1
    by_cases hx : x.1.stage = 0
    · have he := History.stage_zero hx
      rcases x with ⟨b,a⟩
      change b = History.initial P at he
      subst b
      simp [Pi.single_apply, History.initial]
    · have he : x.1 ≠ History.initial P := fun h => hx (congrArg History.stage h)
      have hne (a : Fin q) : x ≠ (History.initial P, a) := fun h => he (congrArg Prod.fst h)
      simp [Pi.single_apply, hne, hx]
  rw [hc, Fintype.card_fin]
  have hq' : (q : ℝ) ≠ 0 := by positivity
  by_cases hx : x.1.stage = 0 <;> simp [rootMass, hx, mul_sub, ← mul_assoc, hq'] <;> ring

private theorem centerRoot_mass (hq : 0 < q) (R : ℝ) (hR : R ≤ 4)
    (p : HV P k → Chains (HV P k))
    (hp : ∀ u v, (rolling (historyData P)).Adj u v →
      dualNorm (triangleChain (G := rolling (historyData P))) (orientedEdge u v + p u - p v) ≤ R)
    (v : HV P k) : mass (centerRoot p v) ≤ 13 * (n + 1) := by
  classical
  letI : Nonempty (Fin q) := ⟨⟨0,hq⟩⟩
  have edge (u v : HV P k) (h : (rolling (historyData P)).Adj u v) :
      mass (p v - p u) ≤ 13 :=
    (mass_edge_difference_le _ _ _ _ (hp u v h)).trans (by linarith)
  have hall (a : Fin q) : mass (p v - p (History.initial P,a)) ≤ 13 * (n + 1) := by
    obtain ⟨walk,hwalk⟩ := rolling_short_walk (historyData P) a v
    have h' : walk.length ≤ n + 1 := hwalk.trans (Nat.add_le_add_right (Nat.le_of_lt_succ v.1.stage.isLt) 1)
    exact (mass_walk_difference_le p 13 edge walk).trans
      (by
        have : (walk.length : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast h'
        nlinarith)
  have hEq : centerRoot p v = meanChain (fun a : Fin q => p v - p (History.initial P,a)) := by
    funext e
    have hq' : (q : ℝ) ≠ 0 := by positivity
    simp [centerRoot, meanChain, Finset.sum_sub_distrib, mul_sub, ← mul_assoc, hq']
  rw [hEq]
  exact mass_mean_le _ _ hall

end RootNormalization


section LabelPermutations

variable {n q k : ℕ} {P : Retention n q}

/-- Relabel each birth layer independently, transporting all retention choices. -/
private def relabelStep (σ : Fin (n + 1) → Equiv.Perm (Fin q)) (s : Step n q k) :
    Step n q k :=
  (fun j => (s.1 j).map (σ j).toEmbedding, s.2)

private theorem relabel_root (σ : Fin (n + 1) → Equiv.Perm (Fin q)) :
    relabelStep σ (rootStep n q k) = rootStep n q k := by
  ext j x
  · simp [relabelStep, rootStep, Finset.mem_map_equiv]
  · rfl

private def History.relabel (σ : Fin (n + 1) → Equiv.Perm (Fin q)) (b : History P k) :
    History P k where
  stage := b.stage
  step i := relabelStep σ (b.step i)
  root_step := (congrArg _ b.root_step).trans (relabel_root σ)
  beyond i hi := (congrArg _ (b.beyond i hi)).trans (relabel_root σ)
  cardinal j i hi := by simp [relabelStep, b.cardinal j i hi]
  nested j i l hil ht := by
    intro a ha
    simp only [relabelStep, Finset.mem_map_equiv] at *
    exact b.nested j i l hil ht ha

private theorem relabelStep_symm (σ : Fin (n + 1) → Equiv.Perm (Fin q)) (s : Step n q k) :
    relabelStep (fun j => (σ j).symm) (relabelStep σ s) = s := by
  ext j x
  · simp [relabelStep, Finset.mem_map_equiv]
  · rfl

private theorem History.relabel_symm (σ : Fin (n + 1) → Equiv.Perm (Fin q)) (b : History P k) :
    (b.relabel σ).relabel (fun j => (σ j).symm) = b :=
  History.ext' rfl (funext fun _ => relabelStep_symm σ _)

private theorem History.relabel_prefix (σ : Fin (n + 1) → Equiv.Perm (Fin q))
    {b c : History P k} : (b.relabel σ).IsPrefix (c.relabel σ) ↔ b.IsPrefix c := by
  constructor
  · intro h
    refine ⟨h.1, fun i hi => ?_⟩
    exact (relabelStep_symm σ _).symm.trans
      ((congrArg (relabelStep (fun j => (σ j).symm)) (h.2 i hi)).trans (relabelStep_symm σ _))
  · exact fun h => ⟨h.1, fun i hi => congrArg (relabelStep σ) (h.2 i hi)⟩

private def labelPerm (σ : Fin (n + 1) → Equiv.Perm (Fin q)) :
    Equiv.Perm (History P k × Fin q) where
  toFun v := (v.1.relabel σ, σ v.1.stage v.2)
  invFun v := (v.1.relabel (fun j => (σ j).symm), (σ v.1.stage).symm v.2)
  left_inv v := Prod.ext (History.relabel_symm σ _) ((σ _).symm_apply_apply _)
  right_inv v := Prod.ext (History.relabel_symm (fun j => (σ j).symm) _) ((σ _).apply_symm_apply _)

private theorem labelPerm_adj (σ : Fin (n + 1) → Equiv.Perm (Fin q))
    (u v : History P k × Fin q) :
    (rolling (historyData P)).Adj (labelPerm σ u) (labelPerm σ v) ↔
      (rolling (historyData P)).Adj u v := by
  have h (a b : History P k) : a.relabel σ = b.relabel σ ↔ a = b := by
    constructor
    · intro he
      simpa only [History.relabel_symm] using congrArg (History.relabel (fun j => (σ j).symm)) he
    · exact congrArg _
  change (labelPerm σ u ≠ labelPerm σ v ∧ _) ↔ _
  rw [(labelPerm σ).injective.ne_iff]
  change (_ ∧ (u.1.relabel σ = v.1.relabel σ ∨
    ((u.1.relabel σ).IsPrefix (v.1.relabel σ) ∧
      σ u.1.stage u.2 ∈ (relabelStep σ (v.1.step v.1.stage)).1 u.1.stage) ∨
    ((v.1.relabel σ).IsPrefix (u.1.relabel σ) ∧
      σ v.1.stage v.2 ∈ (relabelStep σ (u.1.step u.1.stage)).1 v.1.stage))) ↔ _
  simp only [h, History.relabel_prefix, relabelStep, Finset.mem_map_equiv, Equiv.symm_apply_apply]
  rfl

end LabelPermutations

section ClonePermutations

variable {n q k : ℕ} {P : Retention n q}

private def History.reclone (i : Fin (n + 1)) (hi : i ≠ 0)
    (σ : Equiv.Perm (Fin (k + 1))) (b : History P k) : History P k where
  stage := b.stage
  step t := if t = i ∧ i ≤ b.stage then ((b.step t).1, σ (b.step t).2) else b.step t
  root_step := by simpa [hi.symm] using b.root_step
  beyond t ht := by
    simp [show ¬(t = i ∧ i ≤ b.stage) from fun h => ht.not_ge (h.1.symm ▸ h.2), b.beyond t ht]
  cardinal j t ht := by
    split <;> exact b.cardinal j t ht
  nested j t l htl hl := by
    split <;> split <;> exact b.nested j t l htl hl

private theorem History.reclone_symm (i : Fin (n + 1)) (hi : i ≠ 0)
    (σ : Equiv.Perm (Fin (k + 1))) (b : History P k) : (b.reclone i hi σ).reclone i hi σ.symm = b := by
  refine History.ext' (b := (b.reclone i hi σ).reclone i hi σ.symm) (c := b) rfl ?_
  funext t
  change (if t = i ∧ i ≤ b.stage then (((b.reclone i hi σ).step t).1,
    σ.symm ((b.reclone i hi σ).step t).2) else (b.reclone i hi σ).step t) = _
  split
  · rename_i ht
    simp [History.reclone, ht]
  · rename_i ht
    simp [History.reclone, ht]

private theorem History.reclone_prefix (i : Fin (n + 1)) (hi : i ≠ 0)
    (σ : Equiv.Perm (Fin (k + 1))) {b c : History P k} :
    (b.reclone i hi σ).IsPrefix (c.reclone i hi σ) ↔ b.IsPrefix c := by
  have forward (τ : Equiv.Perm (Fin (k + 1))) {b c : History P k} (h : b.IsPrefix c) :
      (b.reclone i hi τ).IsPrefix (c.reclone i hi τ) := by
    refine ⟨h.1, fun t ht => ?_⟩
    change t ≤ b.stage at ht
    have he := h.2 t ht
    by_cases hit : t = i
    · subst t
      simp [History.reclone, ht, ht.trans h.1, he]
    · simp [History.reclone, hit, he]
  exact ⟨fun h => by simpa only [History.reclone_symm] using forward σ.symm h, forward σ⟩

private def clonePerm (i : Fin (n + 1)) (hi : i ≠ 0) (σ : Equiv.Perm (Fin (k + 1))) :
    Equiv.Perm (History P k × Fin q) where
  toFun v := (v.1.reclone i hi σ, v.2)
  invFun v := (v.1.reclone i hi σ.symm, v.2)
  left_inv v := Prod.ext (History.reclone_symm i hi σ _) rfl
  right_inv v := Prod.ext (History.reclone_symm i hi σ.symm _) rfl

private theorem clonePerm_adj (i : Fin (n + 1)) (hi : i ≠ 0) (σ : Equiv.Perm (Fin (k + 1)))
    (u v : History P k × Fin q) :
    (rolling (historyData P)).Adj (clonePerm i hi σ u) (clonePerm i hi σ v) ↔
      (rolling (historyData P)).Adj u v := by
  have e (b c : History P k) : b.reclone i hi σ = c.reclone i hi σ ↔ b = c := by
    constructor
    · intro hb
      simpa only [History.reclone_symm] using congrArg (History.reclone i hi σ.symm) hb
    · exact congrArg _
  have h (b : History P k) (t : Fin (n + 1)) :
      ((b.reclone i hi σ).step t).1 = (b.step t).1 := by
    simp only [History.reclone]
    split <;> rfl
  change (clonePerm i hi σ u ≠ clonePerm i hi σ v ∧ _) ↔ _
  rw [(clonePerm i hi σ).injective.ne_iff]
  change (_ ∧ ((u.1.reclone i hi σ = v.1.reclone i hi σ) ∨
    ((u.1.reclone i hi σ).IsPrefix (v.1.reclone i hi σ) ∧
      u.2 ∈ ((v.1.reclone i hi σ).step v.1.stage).1 u.1.stage) ∨
    ((v.1.reclone i hi σ).IsPrefix (u.1.reclone i hi σ) ∧
      v.2 ∈ ((u.1.reclone i hi σ).step u.1.stage).1 v.1.stage))) ↔ _
  simp only [e, History.reclone_prefix, h]
  rfl

end ClonePermutations

private theorem clone_load_le {n q k : ℕ} {P : Retention n q}
    (p : History P k × Fin q → Chains (History P k × Fin q)) (L : ℝ)
    (hp : ∀ v, mass (p v) ≤ L)
    (hs : ∀ (σ : depthAutomorphisms (rolling (historyData P)) (fun v => v.1.stage.val)
      (fun u v => u.1.IsPrefix v.1)) v a b,
      p (σ.val v) (σ.val a, σ.val b) = p v (a,b))
    (x : History P k × Fin q) (t : Fin (n + 1)) (ht : x.1.stage < t) (a : Fin (k + 1)) :
    ∑ v ∈ Finset.univ.filter (fun v : History P k × Fin q => t ≤ v.1.stage ∧ (v.1.step t).2 = a),
      load (p x) v ≤ 2 * L / (k + 1 : ℝ) := by
  classical
  let V := History P k × Fin q
  let S : Finset V := Finset.univ.filter fun v => t ≤ v.1.stage
  let f : V → Fin (k + 1) := fun v => (v.1.step t).2
  have hroot : t ≠ 0 := fun h => (Fin.zero_le x.1.stage).not_gt (h ▸ ht)
  have hEq (b : Fin (k + 1)) :
      ∑ v ∈ S with f v = b, load (p x) v = ∑ v ∈ S with f v = a, load (p x) v := by
    let π := Equiv.swap a b
    let σ : Equiv.Perm V := clonePerm t hroot π
    have hσ : σ ∈ depthAutomorphisms (rolling (historyData P)) (fun v => v.1.stage.val)
      (fun u v => u.1.IsPrefix v.1) :=
      ⟨clonePerm_adj t hroot π, fun _ => rfl, fun _ _ => History.reclone_prefix t hroot π⟩
    have hx : σ x = x := by
      apply Prod.ext
      · apply History.ext' (b := x.1.reclone t hroot π) (c := x.1) rfl
        funext i
        simp [History.reclone, not_le_of_gt ht]
      · rfl
    have hload := invariant_load σ (p x) (fun u v => by
      have h := hs ⟨σ,hσ⟩ x u v
      change p (σ x) (σ u, σ v) = p x (u,v) at h
      rwa [hx] at h)
    simp only [Finset.sum_filter, and_assoc, S, Finset.mem_univ, true_and]
    rw [← Equiv.sum_comp σ (fun v => if t ≤ v.1.stage then if f v = b then load (p x) v else 0 else 0)]
    apply Finset.sum_congr rfl
    intro v _
    have he : (σ v).1.stage = v.1.stage := rfl
    rw [he, hload]
    by_cases hv : t ≤ v.1.stage
    · have hfv : f (σ v) = π (f v) := by simp [f, σ, clonePerm, History.reclone, hv]
      have hπ : π a = b := Equiv.swap_apply_left a b
      simp only [hfv, ← hπ, π.injective.eq_iff]
    · simp [hv]
  have hmass := equal_fiber_mass_bound S f (load (p x)) a hEq
  have hS : ∑ v ∈ S, load (p x) v ≤ 2 * L := by
    calc
      _ ≤ ∑ v, load (p x) v :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun v _ _ => load_nonneg _ v)
      _ ≤ _ := by rw [sum_load]; exact mul_le_mul_of_nonneg_left (hp x) (by norm_num)
  have hfilter : S.filter (fun v => f v = a) = Finset.univ.filter
      (fun v : V => t ≤ v.1.stage ∧ f v = a) := by
    rw [Finset.filter_filter]
  rw [← hfilter, hmass, Fintype.card_fin, Nat.cast_add, Nat.cast_one, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hS (by positivity)

section ConcreteRetention

private def quota (w M j i : ℕ) : ℕ :=
  if i ≤ j + w then M ^ (w + 2 - (i - j)) else 0

private theorem quota_antitone (w M j : ℕ) (hM : 1 ≤ M) :
    Antitone (quota w M j) := by
  intro i l hil
  by_cases h : l ≤ j + w
  · simp only [quota, h, hil.trans h, ite_true]
    exact pow_le_pow_right' hM (by omega)
  · simp [quota, h]

private theorem quota_le (w M j i : ℕ) (hM : 1 ≤ M) :
    quota w M j i ≤ M ^ (w + 2) := by
  have h := quota_antitone w M j hM (Nat.zero_le i)
  simpa [quota] using h

private def concreteRetention (w n M : ℕ) (hw : 1 ≤ w) (hM : 1 ≤ M) :
    Retention n (M ^ (w + 2)) where
  count j i := quota w M j.val i.val
  root j := by simp [quota]
  positivePrevious i hi := by
    have hwi : i.val ≤ i.val - 1 + w := by omega
    simp [quota, hwi, pow_pos (show 0 < M by omega)]

private def segment {m q : ℕ} (h : m ≤ q) : Finset (Fin q) :=
  Finset.univ.map (Fin.castLEEmb h)

private theorem mem_segment {m q : ℕ} (h : m ≤ q) (x : Fin q) :
    x ∈ segment h ↔ x.val < m := by
  simp only [segment, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨y, rfl⟩
    exact y.isLt
  · intro hx
    exact ⟨⟨x.val, hx⟩, Fin.ext rfl⟩

private theorem card_segment {m q : ℕ} (h : m ≤ q) : (segment h).card = m := by
  simp [segment]

private def fullSpine (w n M k : ℕ) (hw : 1 ≤ w) (hM : 1 ≤ M) :
    History (concreteRetention w n M hw hM) k where
  stage := ⟨n, Nat.lt_succ_self n⟩
  step i := (fun j => segment (quota_le w M j.val i.val hM), 0)
  root_step := by
    ext j x
    · simp [mem_segment, quota, x.isLt, rootStep]
    · rfl
  beyond i hi := (Nat.not_lt_of_ge (Nat.le_of_lt_succ i.isLt) hi).elim
  cardinal j i _ := card_segment (quota_le w M j.val i.val hM)
  nested j i l hil _ := by
    intro x hx
    simp only [mem_segment] at *
    exact hx.trans_le (quota_antitone w M j.val hM hil)

private theorem quota_step (w M j i : ℕ) (hj : j ≤ i) (hi : i + 1 ≤ j + w) :
    quota w M j i = M * quota w M j (i + 1) := by
  rw [quota, if_pos (by omega : i ≤ j + w), quota, if_pos hi]
  have he : w + 2 - (i - j) = w + 2 - (i + 1 - j) + 1 := by omega
  rw [he, pow_succ, Nat.mul_comm]

end ConcreteRetention

section SpineRetraction

variable {n q k : ℕ} {P : Retention n q}

private def History.Break (b c : History P k) (i : Fin (n + 1)) : Prop :=
  i ≤ b.stage ∧ (c.stage < i ∨ b.step i ≠ c.step i)

private theorem History.exists_break {b c : History P k} (h : ¬b.IsPrefix c) :
    ∃ i, b.Break c i := by
  classical
  by_contra! hn
  apply h
  refine ⟨?_, ?_⟩
  · exact le_of_not_gt fun ht => hn b.stage ⟨le_rfl, Or.inl ht⟩
  · exact fun i hi => not_ne_iff.mp fun he => hn i ⟨hi, Or.inr he⟩

private noncomputable def History.firstBreak {b c : History P k} (h : ¬b.IsPrefix c) : Fin (n + 1) :=
  letI := Classical.propDecidable
  ((Finset.univ : Finset (Fin (n + 1))).filter (b.Break c)).min'
    (by obtain ⟨i, hi⟩ := exists_break h; exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩)

private theorem History.firstBreak_mem {b c : History P k} (h : ¬b.IsPrefix c) :
    b.Break c (firstBreak h) := by
  classical
  unfold firstBreak
  exact (Finset.mem_filter.mp (Finset.min'_mem _ _)).2

private theorem History.firstBreak_min {b c : History P k} (h : ¬b.IsPrefix c)
    {i : Fin (n + 1)} (hi : b.Break c i) : firstBreak h ≤ i := by
  classical
  unfold firstBreak
  exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)

private theorem History.firstBreak_pos {b c : History P k} (h : ¬b.IsPrefix c) :
    0 < (firstBreak h).val := by
  have hh := (firstBreak_mem h).2
  by_contra! hl
  have he : firstBreak h = 0 := Fin.ext (Nat.eq_zero_of_le_zero hl)
  simp [he, b.root_step, c.root_step] at hh

private theorem History.firstBreak_eq {b d c : History P k} (h : b.IsPrefix d)
    (hb : ¬b.IsPrefix c) (hd : ¬d.IsPrefix c) :
    firstBreak hb = firstBreak hd := by
  have hm := firstBreak_mem hb
  have ha : d.Break c (firstBreak hb) := by
    exact ⟨hm.1.trans h.1, by rw [← h.2 _ hm.1]; exact hm.2⟩
  have hle := firstBreak_min hd ha
  have hh := firstBreak_mem hd
  have hh' : firstBreak hd ≤ b.stage := hle.trans hm.1
  have hz : b.Break c (firstBreak hd) := by
    exact ⟨hh', by rw [h.2 _ hh']; exact hh.2⟩
  exact le_antisymm (firstBreak_min hb hz) hle

private def Fin.previous (i : Fin (n + 1)) : Fin (n + 1) :=
  ⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.isLt⟩

private theorem History.beforeBreak {b c : History P k} (h : ¬b.IsPrefix c)
    {i : Fin (n + 1)} (hi : i < firstBreak h) : i ≤ c.stage ∧ b.step i = c.step i := by
  have hb := hi.le.trans (firstBreak_mem h).1
  constructor
  · exact le_of_not_gt fun hh => hi.not_ge (firstBreak_min h ⟨hb, Or.inl hh⟩)
  · exact not_ne_iff.mp fun hh => hi.not_ge (firstBreak_min h ⟨hb, Or.inr hh⟩)

private theorem History.previous_lt_break {b c : History P k} (h : ¬b.IsPrefix c) :
    Fin.previous (firstBreak h) < firstBreak h := by
  have hh := firstBreak_pos h
  change (firstBreak h).val - 1 < (firstBreak h).val
  omega

private def History.breakBlock {b c : History P k} (h : ¬b.IsPrefix c) : History P k :=
  b.prefix (firstBreak h) (firstBreak_mem h).1

private theorem History.breakBlock_eq {b d c : History P k} (h : b.IsPrefix d)
    (hb : ¬b.IsPrefix c) (hd : ¬d.IsPrefix c) :
    breakBlock hb = breakBlock hd := by
  have he := firstBreak_eq h hb hd
  apply History.ext' he
  funext i
  simp only [breakBlock, History.prefix, ← he]
  split
  · rename_i hi
    exact h.2 _ (hi.trans (firstBreak_mem hb).1)
  · rfl

private noncomputable def History.collapseVertex (a : History P k) (h : 0 < a.stage.val) :
    History P k × Fin q := by
  have hp : Fin.previous a.stage ≤ a.stage := Nat.sub_le _ _
  have hn : ((a.step a.stage).1 (Fin.previous a.stage)).Nonempty := by
    rw [← Finset.card_pos, a.cardinal _ _ le_rfl]
    exact P.positivePrevious a.stage h
  exact (a.prefix (Fin.previous a.stage) hp, hn.choose)

private theorem History.collapse_mem (a : History P k) (h : 0 < a.stage.val) :
    (collapseVertex a h).2 ∈ (a.step a.stage).1 (Fin.previous a.stage) :=
  Classical.choose_spec _

private noncomputable def spineMap (c : History P k) (v : History P k × Fin q) :
    History P k × Fin q := by
  classical
  exact if h : v.1.IsPrefix c then v else
    History.collapseVertex (History.breakBlock h) (History.firstBreak_pos h)

private theorem spineMap_fixed {c : History P k} {v : History P k × Fin q}
    (h : v.1.IsPrefix c) : spineMap c v = v := by
  simp [spineMap, h]

private theorem spineMap_on_spine (c : History P k) (v : History P k × Fin q) :
    (spineMap c v).1.IsPrefix c := by
  classical
  by_cases h : v.1.IsPrefix c
  · rwa [spineMap_fixed h]
  rw [spineMap, dite_eq_right h]
  have hm := History.previous_lt_break h
  have hc := (History.beforeBreak h hm).1
  refine ⟨hc, fun i hi => ?_⟩
  have hb : i < History.firstBreak h := hi.trans_lt hm
  have hi' : i ≤ Fin.previous (History.firstBreak h) := hi
  simpa [History.collapseVertex, History.breakBlock, History.prefix, hi', hb.le] using
    (History.beforeBreak h hb).2

private theorem spineMap_eq_of_outside {b d c : History P k} (h : b.IsPrefix d)
    (hb : ¬b.IsPrefix c) (hd : ¬d.IsPrefix c) (x y : Fin q) :
    spineMap c (b,x) = spineMap c (d,y) := by
  simp only [spineMap, dif_neg hb, dif_neg hd]
  have e : (⟨History.breakBlock hb, History.firstBreak_pos hb⟩ :
      {a : History P k // 0 < a.stage.val}) =
      ⟨History.breakBlock hd, History.firstBreak_pos hd⟩ :=
    Subtype.ext (History.breakBlock_eq h hb hd)
  exact congrArg (fun a => History.collapseVertex a.val a.property) e

private theorem spineMap_edge (c : History P k) {u v : History P k × Fin q}
    (h : (rolling (historyData P)).Adj u v) :
    spineMap c u = spineMap c v ∨ (rolling (historyData P)).Adj (spineMap c u) (spineMap c v) := by
  classical
  let D : RollingData (History P k) (Fin q) := historyData P
  have earlier (x y : History P k × Fin q) (hxy : (rolling D).Adj x y)
      (hpre : x.1.IsPrefix y.1) :
      spineMap c x = spineMap c y ∨ (rolling D).Adj (spineMap c x) (spineMap c y) := by
    by_cases hx : x.1.IsPrefix c
    · rw [spineMap_fixed hx]
      by_cases hy : y.1.IsPrefix c
      · rw [spineMap_fixed hy]
        exact Or.inr hxy
      · have hp : x.1.stage < History.firstBreak hy := by
          by_contra! hn
          have hm := (History.firstBreak_mem hy).2
          rw [← hpre.2 _ hn, hx.2 _ hn] at hm
          exact hm.elim (fun hh => hh.not_ge (hn.trans hx.1)) (fun hh => hh rfl)
        rw [spineMap, dite_eq_right hy]
        let a := History.breakBlock hy
        let d := History.collapseVertex a (History.firstBreak_pos hy)
        change x = d ∨ (rolling D).Adj x d
        by_cases he : x = d
        · exact Or.inl he
        · apply Or.inr
          refine ⟨he, ?_⟩
          by_cases hb : x.1 = d.1
          · exact Or.inl hb
          · refine Or.inr (Or.inl ⟨?_, ?_⟩)
            · have hc : x.1.stage ≤ d.1.stage := by
                change x.1.stage.val ≤ (History.firstBreak hy).val - 1
                have hp' : x.1.stage.val < (History.firstBreak hy).val := hp
                omega
              refine ⟨hc, fun i hi => ?_⟩
              have hi' := hi.trans hp.le
              have hdi := hi.trans hc
              change x.1.step i =
                if i ≤ d.1.stage then (if i ≤ History.firstBreak hy then y.1.step i else _) else _
              rw [if_pos hdi, if_pos hi']
              exact hpre.2 _ hi
            · have hretain := (rolling_earlier D hxy hpre.1).2.resolve_left (fun hz => by
                have hp' := (History.firstBreak_mem hy).1
                exact hp.not_ge (hp'.trans (congrArg History.stage hz).ge))
              have hprefix (b c : History P k) (hbc : b.IsPrefix c) :
                  D.ancestor b c := hbc
              have hdy : d.1.IsPrefix y.1 :=
                D.trans (History.prefix_spec a (Fin.previous a.stage) (Nat.sub_le _ _))
                  (History.prefix_spec y.1 (History.firstBreak hy) (History.firstBreak_mem hy).1)
              exact D.nested (hprefix _ _ hdy) hretain
    · have hy : ¬y.1.IsPrefix c := fun hy => hx (D.trans hpre hy)
      exact Or.inl (spineMap_eq_of_outside hpre hx hy x.2 y.2)
  rcases h.2 with hh | hh | hh
  · exact earlier u v h (hh ▸ D.refl u.1)
  · exact earlier u v h hh.1
  · exact (earlier v u h.symm hh.1).elim (fun he => Or.inl he.symm) (fun he => Or.inr he.symm)

private theorem spineMap_stable {b c : History P k} (h : b.IsPrefix c)
    (t : Fin (n + 1)) (ht : t.val = b.stage.val + 1) (htc : t ≤ c.stage)
    (v : History P k × Fin q) (hv : ¬(c.prefix t htc).IsPrefix v.1) :
    spineMap b v = spineMap c v := by
  classical
  let D : RollingData (History P k) (Fin q) := historyData P
  by_cases h₁ : v.1.IsPrefix b
  · rw [spineMap_fixed h₁, spineMap_fixed (D.trans h₁ h)]
  have hmin := (History.firstBreak_mem h₁).1
  let i := History.firstBreak h₁
  have hit : i ≤ t := by
    rcases le_total v.1.stage t with hv' | hv'
    · exact hmin.trans hv'
    · exact History.firstBreak_min h₁ ⟨hv', Or.inl (show b.stage < t from Nat.lt_of_succ_le ht.ge)⟩
  have hbefore (s : Fin (n + 1)) (hs : s < i) : s ≤ c.stage ∧ v.1.step s = c.step s := by
    obtain ⟨hh, he⟩ := History.beforeBreak h₁ hs
    exact ⟨hh.trans h.1, he.trans (h.2 s hh)⟩
  have hincompat : v.1.Break c i := by
    refine ⟨hmin, ?_⟩
    by_cases hlt : i < t
    · have hi : i ≤ b.stage := by
        change i.val < t.val at hlt
        exact show i.val ≤ b.stage.val by omega
      have hh := (History.firstBreak_mem h₁).2.resolve_left (not_lt_of_ge hi)
      exact Or.inr fun he => hh (he.trans (h.2 i hi).symm)
    · have he : i = t := le_antisymm hit (le_of_not_gt hlt)
      apply Or.inr
      intro har
      refine hv ⟨he ▸ hmin, fun s hs => ?_⟩
      change s ≤ t at hs
      change (if s ≤ t then c.step s else _) = v.1.step s
      rw [ite_eq_left hs]
      rcases lt_or_eq_of_le hs with hlt' | rfl
      · exact (hbefore s (he ▸ hlt')).2.symm
      · exact (he ▸ har).symm
  have h₂ : ¬v.1.IsPrefix c := fun g =>
    hincompat.2.elim (fun hh => hh.not_ge (hmin.trans g.1)) (fun hh => hh (g.2 i hmin))
  have eq : History.firstBreak h₁ = History.firstBreak h₂ := by
    refine le_antisymm (le_of_not_gt fun hj => ?_) (History.firstBreak_min h₂ hincompat)
    have g := hbefore _ hj
    exact (History.firstBreak_mem h₂).2.elim (fun hh => hh.not_ge g.1) (fun hh => hh g.2)
  simp only [spineMap, dite_eq_right h₁, dite_eq_right h₂]
  have equalBlock : History.breakBlock h₁ = History.breakBlock h₂ :=
    History.ext' eq (by funext s; simp [History.breakBlock, History.prefix, eq])
  have e : (⟨History.breakBlock h₁, History.firstBreak_pos h₁⟩ :
      {a : History P k // 0 < a.stage.val}) =
      ⟨History.breakBlock h₂, History.firstBreak_pos h₂⟩ :=
    Subtype.ext equalBlock
  exact congrArg (fun a => History.collapseVertex a.val a.property) e

private theorem localize_residual {n q k : ℕ} {P : Retention n q}
    (p : History P k × Fin q → Chains (History P k × Fin q)) (R L : ℝ)
    (hp : ∀ v, mass (p v) ≤ L)
    (hs : ∀ (σ : depthAutomorphisms (rolling (historyData P)) (fun v => v.1.stage.val)
      (fun u v => u.1.IsPrefix v.1)) v a b,
      p (σ.val v) (σ.val a, σ.val b) = p v (a,b))
    (hr : ∀ u v, (rolling (historyData P)).Adj u v →
      dualNorm (triangleChain (G := rolling (historyData P)))
        (orientedEdge u v + p u - p v) ≤ R)
    (u v : History P k × Fin q) (huv : (rolling (historyData P)).Adj u v) :
    dualNorm (triangleChain (G := rolling (historyData P)))
      (orientedEdge u v + pushChain (spineMap u.1) (p u) - pushChain (spineMap v.1) (p v)) ≤
       R + 12 * L / (k + 1 : ℝ) := by
  classical
  let G : SimpleGraph (History P k × Fin q) := rolling (historyData P)
  have hL : 0 ≤ L := (Finset.sum_nonneg fun e _ => abs_nonneg (p u e)).trans (hp u)
  have forward (x y : History P k × Fin q) (hxy : G.Adj x y) (hd : x.1.stage ≤ y.1.stage) :
      dualNorm (triangleChain (G := G))
        (orientedEdge x y + pushChain (spineMap x.1) (p x) - pushChain (spineMap y.1) (p y)) ≤
        R + 12 * L / (k + 1 : ℝ) := by
    have hpre := (rolling_earlier _ hxy hd).1
    let tChain := triangleChain (G := G)
    have hpush := dualNorm_pushChain_le (spineMap y.1)
      (fun _ _ e => spineMap_edge y.1 e) (orientedEdge x y + p x - p y)
    rw [pushChain_sub, pushChain_add, pushChain_edge, spineMap_fixed hpre,
      spineMap_fixed ((historyData P).refl y.1)] at hpush
    by_cases hEq : x.1.stage = y.1.stage
    · have he := History.IsPrefix.eq_of_stage_eq hpre hEq
      rw [he]
      exact (hpush.trans (hr x y hxy)).trans
        (le_add_of_nonneg_right (by positivity))
    · have hlt := lt_of_le_of_ne hd hEq
      let i : Fin (n + 1) := ⟨x.1.stage.val + 1, (Nat.succ_le_of_lt hlt).trans_lt y.1.stage.isLt⟩
      have hi : i ≤ y.1.stage := Nat.succ_le_of_lt hlt
      let S := Finset.univ.filter (fun v : History P k × Fin q =>
        i ≤ v.1.stage ∧ (v.1.step i).2 = (y.1.step i).2)
      have hstay (z : History P k × Fin q) (hz : z ∉ S) : spineMap x.1 z = spineMap y.1 z := by
        apply spineMap_stable hpre i rfl hi z
        intro h
        apply hz
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.1,
          (congrArg Prod.snd (h.2 i le_rfl)).symm.trans (by simp [History.prefix])⟩
      have hm := clone_load_le p L hp hs x i (show x.1.stage.val < i.val from Nat.lt_succ_self _) (y.1.step i).2
      have herr := (dualNorm_push_change tChain (spineMap x.1) (spineMap y.1) (p x) S hstay).trans
        (mul_le_mul_of_nonneg_left hm (by norm_num))
      have he : orientedEdge x y + pushChain (spineMap x.1) (p x) - pushChain (spineMap y.1) (p y) =
          (orientedEdge x y + pushChain (spineMap y.1) (p x) - pushChain (spineMap y.1) (p y)) +
          (pushChain (spineMap x.1) (p x) - pushChain (spineMap y.1) (p x)) := by abel
      rw [he]
      have h₁ := hpush.trans (hr x y hxy)
      have h₂ : dualNorm tChain (pushChain (spineMap x.1) (p x) -
          pushChain (spineMap y.1) (p x)) ≤ 12 * L / (k + 1 : ℝ) :=
        herr.trans (by ring_nf; rfl)
      exact (dualNorm_add_le tChain _ _).trans (add_le_add h₁ h₂)
  rcases le_total u.1.stage v.1.stage with hd | hd
  · exact forward u v huv hd
  · rw [show orientedEdge u v + pushChain (spineMap u.1) (p u) - pushChain (spineMap v.1) (p v) =
        -(orientedEdge v u + pushChain (spineMap v.1) (p v) - pushChain (spineMap u.1) (p u)) by
      rw [orientedEdge_reverse v u]
      abel, dualNorm_neg_eq]
    exact forward v u huv.symm hd

end SpineRetraction

section LocalizedPotential

variable {n q k : ℕ} {P : Retention n q}

private abbrev histGraph (P : Retention n q) (k : ℕ) : SimpleGraph (HV P k) :=
  rolling (historyData P)

private abbrev histDepth (v : HV P k) : ℕ := v.1.stage.val

private abbrev histPre (u v : HV P k) : Prop := u.1.IsPrefix v.1

private structure Localized (P : Retention n q) (k : ℕ) (R L : ℝ) where
  chain : HV P k → Chains (HV P k)
  boundary_eq (v : HV P k) : boundary (chain v) = Pi.single v 1 - rootMass
  mass_le (v : HV P k) : mass (chain v) ≤ L
  support (v a b : HV P k) :
    ¬(histPre a v ∧ histPre b v ∧ (a = b ∨ (histGraph P k).Adj a b)) → chain v (a,b) = 0
  residual (u v : HV P k) : (histGraph P k).Adj u v →
    dualNorm (triangleChain (G := histGraph P k)) (orientedEdge u v + chain u - chain v) ≤ R
  equivariant (σ : depthAutomorphisms (histGraph P k) histDepth histPre) (v a b : HV P k) :
    chain (σ.val v) (σ.val a, σ.val b) = chain v (a,b)

private theorem History.initial_prefix (b : History P k) : (History.initial P).IsPrefix b := by
  refine ⟨Fin.zero_le _, fun i hi => ?_⟩
  have he : i = 0 := le_antisymm hi (Fin.zero_le _)
  simp [he, History.initial, b.root_step]

private theorem spine_push_boundary (v : HV P k) (c : Chains (HV P k))
    (h : boundary c = Pi.single v 1 - rootMass) :
    boundary (pushChain (spineMap v.1) c) = boundary c := by
  classical
  funext x
  rw [pushChain_boundary, h]
  have he (a : HV P k) :
      (if spineMap v.1 a = x then (Pi.single (M := fun _ : HV P k => ℝ) v 1 a - rootMass a) else 0) =
      if a = x then (Pi.single (M := fun _ : HV P k => ℝ) v 1 a - rootMass a) else 0 := by
    by_cases hv : a = v
    · subst a
      rw [spineMap_fixed ((historyData P).refl v.1)]
    · by_cases hr : a.1.stage = 0
      · rw [spineMap_fixed (by rw [History.stage_zero hr]; exact History.initial_prefix _)]
      · simp [rootMass, hr, Pi.single_apply, hv]
  simp only [Pi.sub_apply, he]
  simp

private theorem spine_push_support (v a b : HV P k) (c : Chains (HV P k))
    (hs : Supported (histGraph P k) c)
    (hn : ¬(histPre a v ∧ histPre b v ∧ (a = b ∨ (histGraph P k).Adj a b))) :
    pushChain (spineMap v.1) c (a,b) = 0 := by
  classical
  unfold pushChain
  simp only [Finset.sum_apply, Pi.single_apply]
  apply Finset.sum_eq_zero
  intro e _
  by_cases he : (a,b) = (spineMap v.1 e.1, spineMap v.1 e.2)
  · rw [if_pos he]
    apply hs e
    intro ed
    apply hn
    have ha := congrArg Prod.fst he
    have hb := congrArg Prod.snd he
    change a = _ at ha
    change b = _ at hb
    rw [ha,hb]
    exact ⟨spineMap_on_spine _ _, spineMap_on_spine _ _, spineMap_edge _ ed⟩
  · simp [he]

private theorem obtain_localized (hq : 0 < q) (R : ℝ) (hR : R ≤ 4) (o : HV P k)
    (p : HV P k → Chains (HV P k))
    (hp : ∀ v, Supported (histGraph P k) (p v))
    (hb : ∀ v, boundary (p v) = Pi.single v 1 - Pi.single o 1)
    (hr : ∀ u v, (histGraph P k).Adj u v →
      dualNorm (triangleChain (G := histGraph P k)) (orientedEdge u v + p u - p v) ≤ R) :
    Nonempty (Localized P k (R + 12 * (13 * (n + 1)) / (k + 1 : ℝ)) (13 * (n + 1))) := by
  classical
  let G := histGraph P k
  let L : ℝ := 13 * (n + 1)
  let p₀ := centerRoot p
  have ps (v : HV P k) : Supported G (p₀ v) := by
    intro e he
    simp [p₀, centerRoot, meanChain, hp _ _ he]
  have pb (v : HV P k) : boundary (p₀ v) = Pi.single v 1 - rootMass :=
    centerRoot_boundary hq o p hb v
  have pm (v : HV P k) : mass (p₀ v) ≤ L := centerRoot_mass hq R hR p hr v
  have pr (u v : HV P k) (e : G.Adj u v) :
      dualNorm (triangleChain (G := G)) (orientedEdge u v + p₀ u - p₀ v) ≤ R := by
    convert hr u v e using 1
    unfold p₀ centerRoot
    abel
  have mu (σ : depthAutomorphisms G histDepth histPre) (v : HV P k) :
      rootMass (σ.val v) = rootMass v := by
    unfold rootMass
    have hd := σ.property.2.1 v
    change (σ.val v).1.stage.val = v.1.stage.val at hd
    rw [Fin.ext hd]
  let pp := symmetrize G histDepth histPre p₀
  let P₀ (v : HV P k) := pushChain (spineMap v.1) (pp v)
  have wb (v : HV P k) : boundary (P₀ v) = Pi.single v 1 - rootMass := by
    have he := symmetrize_boundary G histDepth histPre p₀ rootMass pb mu v
    exact (spine_push_boundary v _ he).trans he
  have wm (v : HV P k) : mass (P₀ v) ≤ L :=
    (mass_pushChain _ _).trans (symmetrize_mass_le G histDepth histPre p₀ L pm v)
  have wr (u v : HV P k) (e : G.Adj u v) :
      dualNorm (triangleChain (G := G)) (orientedEdge u v + P₀ u - P₀ v) ≤
      R + 12 * L / (k + 1 : ℝ) :=
    localize_residual pp R L (symmetrize_mass_le G histDepth histPre p₀ L pm)
      (symmetrize_equivariant G histDepth histPre p₀) (symmetrize_residual_le G histDepth histPre p₀ R pr)
      u v e
  refine ⟨⟨symmetrize G histDepth histPre P₀,
    symmetrize_boundary G histDepth histPre P₀ rootMass wb mu,
    symmetrize_mass_le G histDepth histPre P₀ L wm, ?_,
    symmetrize_residual_le G histDepth histPre P₀ _ wr,
    symmetrize_equivariant G histDepth histPre P₀⟩⟩
  intro v a b hn
  unfold symmetrize
  have hw (σ : depthAutomorphisms G histDepth histPre) : P₀ (σ.val v) (σ.val a,σ.val b) = 0 := by
    apply spine_push_support _ _ _ _ (symmetrize_supported G histDepth histPre p₀ ps _)
    intro h
    exact hn ⟨(σ.property.2.2 _ _).mp h.1, (σ.property.2.2 _ _).mp h.2.1,
      h.2.2.imp (fun e => σ.val.injective e) ((σ.property.1 _ _).mp)⟩
  simp [hw]

end LocalizedPotential

section Ages

variable {w n M k : ℕ} {hw : 1 ≤ w} {hM : 1 ≤ M}

private abbrev RollingHistory (hw : 1 ≤ w) (hM : 1 ≤ M) (n k : ℕ) :=
  History (concreteRetention w n M hw hM) k

private abbrev RollingVertex (hw : 1 ≤ w) (hM : 1 ≤ M) (n k : ℕ) :=
  RollingHistory hw hM n k × Fin (M ^ (w + 2))

private abbrev RollingG (hw : 1 ≤ w) (hM : 1 ≤ M) (n k : ℕ) :
    SimpleGraph (RollingVertex hw hM n k) :=
  rolling (historyData (concreteRetention w n M hw hM))

private noncomputable def liveStages (c : RollingHistory hw hM n k) (v : RollingVertex hw hM n k) :
    Finset (Fin (n + 1)) :=
  Finset.univ.filter fun i => i ≤ c.stage ∧ v.2 ∈ (c.step i).1 v.1.stage

private noncomputable def age (c : RollingHistory hw hM n k) (v : RollingVertex hw hM n k) :
    ℕ :=
  (liveStages c v).sup Fin.val

private theorem age_ge_of_live {c : RollingHistory hw hM n k} {v : RollingVertex hw hM n k}
    (i : Fin (n + 1)) (hi : i ≤ c.stage) (h : v.2 ∈ (c.step i).1 v.1.stage) :
    i.val ≤ age c v :=
  Finset.le_sup (f := Fin.val) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, h⟩)

private theorem age_le_stage (c : RollingHistory hw hM n k) (v : RollingVertex hw hM n k) :
    age c v ≤ c.stage.val := by
  apply Finset.sup_le
  intro i hi
  exact (Finset.mem_filter.mp hi).2.1

private theorem age_le_span (c : RollingHistory hw hM n k) (v : RollingVertex hw hM n k) :
    age c v ≤ v.1.stage.val + w := by
  apply Finset.sup_le
  intro i hi
  have ⟨hs, hm⟩ := (Finset.mem_filter.mp hi).2
  by_contra! hn
  have he := c.cardinal v.1.stage i hs
  change ((c.step i).1 v.1.stage).card = quota w M v.1.stage.val i.val at he
  rw [quota, ite_eq_right (not_le_of_gt hn)] at he
  exact (Finset.card_pos.mpr ⟨_, hm⟩).ne' he

private theorem birth_live {c : RollingHistory hw hM n k} {v : RollingVertex hw hM n k}
    (hv : v.1.IsPrefix c) : v.2 ∈ (c.step v.1.stage).1 v.1.stage := by
  have he := c.cardinal v.1.stage v.1.stage hv.1
  change ((c.step v.1.stage).1 v.1.stage).card = quota w M v.1.stage.val v.1.stage.val at he
  have hb : v.1.stage.val ≤ v.1.stage.val + w := by omega
  have hc : ((c.step v.1.stage).1 v.1.stage).card = Fintype.card (Fin (M ^ (w + 2))) := by
    simpa [quota, hb] using he
  have hfull : (c.step v.1.stage).1 v.1.stage = Finset.univ :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simpa [hc])
  rw [hfull]
  exact Finset.mem_univ _

private theorem birth_le_age {c : RollingHistory hw hM n k} {v : RollingVertex hw hM n k}
    (hv : v.1.IsPrefix c) : v.1.stage.val ≤ age c v :=
  age_ge_of_live v.1.stage hv.1 (birth_live hv)

private theorem age_ge_of_adj {c : RollingHistory hw hM n k} {u v : RollingVertex hw hM n k}
    (hv : v.1.IsPrefix c) (h : (RollingG hw hM n k).Adj u v)
    (hstage : u.1.stage ≤ v.1.stage) : v.1.stage.val ≤ age c u := by
  obtain ⟨hu, he | hr⟩ := rolling_earlier _ h hstage
  · exact (congrArg (fun b => (History.stage b).val) he) ▸ birth_le_age
      ((historyData (concreteRetention w n M hw hM)).trans hu hv)
  · apply age_ge_of_live v.1.stage hv.1
    rw [← hv.2 v.1.stage le_rfl]
    exact hr

private theorem age_edge {c : RollingHistory hw hM n k} {u v : RollingVertex hw hM n k}
    (hu : u.1.IsPrefix c) (hv : v.1.IsPrefix c) (h : (RollingG hw hM n k).Adj u v) :
    tagPair w 0 0 (.inl (age c u)) (.inl (age c v)) := by
  rcases le_total u.1.stage v.1.stage with h₀ | h₀
  · have h₁ := age_ge_of_adj hv h h₀
    have h₂ := birth_le_age hv
    have h₃ := age_le_span c u
    have h₄ := age_le_span c v
    change u.1.stage.val ≤ v.1.stage.val at h₀
    exact ⟨by omega, by omega⟩
  · have h₁ := age_ge_of_adj hu h.symm h₀
    have h₂ := birth_le_age hu
    have h₃ := age_le_span c u
    have h₄ := age_le_span c v
    change v.1.stage.val ≤ u.1.stage.val at h₀
    exact ⟨by omega, by omega⟩

private def tagAge (c : RollingHistory hw hM n k) (x y v : RollingVertex hw hM n k) :
    Tags := by
  classical
  exact if v = x then .inr false else if v = y then .inr true else .inl (age c v)

private theorem tagged_age_edge {c : RollingHistory hw hM n k} {x y u v : RollingVertex hw hM n k}
    (hx : x.1.IsPrefix c) (hy : y.1 = c) (hxy : x ≠ y)
    (hu : u.1.IsPrefix c) (hv : v.1.IsPrefix c) (h : (RollingG hw hM n k).Adj u v) :
    tagPair w x.1.stage.val c.stage.val (tagAge c x y u) (tagAge c x y v) := by
  classical
  have ageAdj (z t : RollingVertex hw hM n k) (hz : z.1.IsPrefix c) (ht : t.1.IsPrefix c)
      (hzt : (RollingG hw hM n k).Adj z t) :
      z.1.stage.val ≤ age c t := by
    rcases le_total z.1.stage t.1.stage with h' | h'
    · exact (show z.1.stage.val ≤ t.1.stage.val from h').trans (birth_le_age ht)
    · exact age_ge_of_adj hz hzt.symm h'
  have ageX (z : RollingVertex hw hM n k) (hz : z.1.IsPrefix c)
      (hadj : (RollingG hw hM n k).Adj x z) :
      x.1.stage.val ≤ age c z ∧ age c z ≤ c.stage.val :=
    ⟨ageAdj _ _ hx hz hadj, age_le_stage _ _⟩
  have hyP : y.1.IsPrefix c := hy.symm ▸ ⟨le_rfl, fun _ _ => rfl⟩
  have ageY (z : RollingVertex hw hM n k) (hz : z.1.IsPrefix c)
      (hadj : (RollingG hw hM n k).Adj y z) : age c z = c.stage.val :=
    le_antisymm (age_le_stage _ _) (by simpa only [hy] using ageAdj _ _ hyP hz hadj)
  by_cases hux : u = x
  · subst u
    by_cases hvy : v = y
    · subst v
      simp [tagAge, hxy, Ne.symm hxy, tagPair]
    · have hvx : v ≠ x := fun he => h.ne he.symm
      simpa [tagAge, hvx, hvy, tagPair] using ageX v hv h
  by_cases huy : u = y
  · subst u
    by_cases hvx : v = x
    · subst v
      simp [tagAge, hxy, Ne.symm hxy, tagPair]
    · have hvy : v ≠ y := fun he => h.ne he.symm
      simpa [tagAge, hux, hvx, hvy, tagPair] using ageY v hv h
  by_cases hvx : v = x
  · subst v
    simpa [tagAge, hux, huy, tagPair] using ageX u hu h.symm
  by_cases hvy : v = y
  · subst v
    simpa [tagAge, hux, huy, hvx, tagPair] using ageY u hu h.symm
  rw [tagAge, ite_eq_right hux, ite_eq_right huy, tagAge, ite_eq_right hvx, ite_eq_right hvy]
  exact age_edge hu hv h

private theorem alive_swap {c : RollingHistory hw hM n k} {b : RollingHistory hw hM n k}
    (hbc : b.IsPrefix c) {s t : Fin (M ^ (w + 2))}
    (hs : s ∈ (c.step c.stage).1 b.stage) (ht : t ∈ (c.step c.stage).1 b.stage) :
    ∃ σ : depthAutomorphisms (RollingG hw hM n k) histDepth histPre,
      (∀ a : RollingHistory hw hM n k, a.IsPrefix c → (σ.val (a,s)).1 = a) ∧
      σ.val (b,s) = (b,t) ∧
      (∀ a : RollingVertex hw hM n k, a.1.IsPrefix c →
        (a.1.stage ≠ b.stage ∨ (a.2 ≠ s ∧ a.2 ≠ t)) → σ.val a = a) ∧
      (∀ a : RollingVertex hw hM n k, a.1.IsPrefix c → age c (σ.val a) = age c a) := by
  classical
  let π : Fin (n+1) → Equiv.Perm (Fin (M^(w+2))) :=
    Function.update (fun _ => 1) b.stage (Equiv.swap s t)
  let σ : Equiv.Perm (RollingVertex hw hM n k) := labelPerm π
  have fixHistory (a : RollingHistory hw hM n k) (ha : a.IsPrefix c) : a.relabel π = a := by
    refine History.ext' (b := a.relabel π) (c := a) rfl ?_
    funext i
    by_cases hi : i ≤ a.stage
    · change relabelStep π (a.step i) = a.step i
      apply Prod.ext
      · funext j
        ext x
        simp only [relabelStep, Finset.mem_map_equiv]
        by_cases hj : j = b.stage
        · subst j
          have hsi : s ∈ (a.step i).1 b.stage := by
            rw [ha.2 i hi]
            exact c.nested _ _ _ (hi.trans ha.1) le_rfl hs
          have hti : t ∈ (a.step i).1 b.stage := by
            rw [ha.2 i hi]
            exact c.nested _ _ _ (hi.trans ha.1) le_rfl ht
          simp only [π, Function.update_self, Equiv.symm_swap]
          by_cases hxs : x = s
          · subst x
            simp [hsi, hti]
          · by_cases hxt : x = t
            · subst x
              simp [hsi, hti]
            · simp [Equiv.swap_apply_of_ne_of_ne hxs hxt]
        · simp [π, Function.update_of_ne hj, Equiv.Perm.one_def]
      · rfl
    · rw [(a.relabel π).beyond i (lt_of_not_ge hi), a.beyond i (lt_of_not_ge hi)]
  let τ : depthAutomorphisms (RollingG hw hM n k) histDepth histPre :=
    ⟨σ, labelPerm_adj π, (fun _ => rfl), fun _ _ => History.relabel_prefix π⟩
  refine ⟨τ, fun a ha => fixHistory a ha, ?_, ?_, ?_⟩
  · apply Prod.ext (fixHistory b hbc)
    simp [τ, σ, labelPerm, π]
  · intro a ha h
    apply Prod.ext (fixHistory a.1 ha)
    rcases h with hj | ⟨h₁,h₂⟩
    · simp [τ, σ, labelPerm, π, Function.update_of_ne hj]
    · by_cases hj : a.1.stage = b.stage
      · simp [τ, σ, labelPerm, π, hj, Equiv.swap_apply_of_ne_of_ne h₁ h₂]
      · simp [τ, σ, labelPerm, π, Function.update_of_ne hj]
  · intro a ha
    have e := fixHistory a.1 ha
    unfold age
    congr 1
    ext i
    simp only [liveStages, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [show (σ a).1 = a.1 from e]
    constructor <;> rintro ⟨hi,hx⟩ <;> refine ⟨hi, ?_⟩ <;>
      by_cases hj : a.1.stage = b.stage
    · change (π a.1.stage a.2) ∈ _ at hx
      rw [hj] at hx ⊢
      have hs' := c.nested b.stage i c.stage hi le_rfl hs
      have ht' := c.nested b.stage i c.stage hi le_rfl ht
      by_cases h₁ : a.2 = s
      · simpa [h₁] using hs'
      · by_cases h₂ : a.2 = t
        · simpa [h₂] using ht'
        · simpa [π, Equiv.swap_apply_of_ne_of_ne h₁ h₂] using hx
    · simpa [τ, σ, labelPerm, π, Function.update_of_ne hj] using hx
    · change (π a.1.stage a.2) ∈ _
      rw [hj] at hx ⊢
      have hs' := c.nested b.stage i c.stage hi le_rfl hs
      have ht' := c.nested b.stage i c.stage hi le_rfl ht
      by_cases h₁ : a.2 = s
      · simpa [h₁, π] using ht'
      · by_cases h₂ : a.2 = t
        · simpa [h₂, π] using hs'
        · simpa [π, Equiv.swap_apply_of_ne_of_ne h₁ h₂] using hx
    · simpa [τ, σ, labelPerm, π, Function.update_of_ne hj] using hx

private theorem sum_const_subset_bound {V : Type*} [DecidableEq V] (u : V → ℝ)
    (S T : Finset V) (M : ℕ) (hM : 0 < M)
    (hsub : T ⊆ S) (hcard : M * T.card ≤ S.card) (hpos : ∀ v, 0 ≤ u v)
    (hc : ∀ a ∈ S, ∀ b ∈ S, u a = u b) :
    ∑ v ∈ T, u v ≤ (∑ v ∈ S, u v) / M := by
  by_cases hs : S.Nonempty
  · obtain ⟨v,hv⟩ := hs
    have h₁ : ∑ i ∈ S, u i = (S.card : ℝ) * u v := by
      calc
        _ = ∑ i ∈ S, u v := Finset.sum_congr rfl fun i hi => hc i hi v hv
        _ = _ := by simp
    have h₂ : ∑ i ∈ T, u i = (T.card : ℝ) * u v := by
      calc
        _ = ∑ i ∈ T, u v := Finset.sum_congr rfl fun i hi => hc i (hsub hi) v hv
        _ = _ := by simp
    rw [h₁, h₂, le_div_iff₀ (Nat.cast_pos.mpr hM)]
    have hℝ : (M : ℝ) * T.card ≤ S.card := by exact_mod_cast hcard
    nlinarith [mul_le_mul_of_nonneg_right hℝ (hpos v)]
  · have hse := Finset.not_nonempty_iff_eq_empty.mp hs
    have hte : T = ∅ := Finset.subset_empty.mp (hse ▸ hsub)
    simp [hte, hse]

private def retainedVertices (c b : RollingHistory hw hM n k) :
    Finset (RollingVertex hw hM n k) :=
  ((c.step c.stage).1 b.stage).map ⟨Prod.mk b, fun _ _ h => congrArg Prod.snd h⟩

private theorem mem_retainedVertices {c b : RollingHistory hw hM n k} {v : RollingVertex hw hM n k} :
    v ∈ retainedVertices c b ↔ v.1 = b ∧ v.2 ∈ (c.step c.stage).1 b.stage := by
  simp only [retainedVertices, Finset.mem_map]
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ⟨rfl, ha⟩
  · rintro ⟨h,ha⟩
    exact ⟨v.2,ha,Prod.ext h.symm rfl⟩

private theorem surviving_load_const {R L : ℝ} {c b : RollingHistory hw hM n k}
    (P : Localized (concreteRetention w n M hw hM) k R L)
    (x : RollingVertex hw hM n k) (hx : x.1 = c) (hb : b.IsPrefix c)
    {u v : RollingVertex hw hM n k}
    (hu : u ∈ (retainedVertices c b).erase x) (hv : v ∈ (retainedVertices c b).erase x) :
    load (P.chain x) u = load (P.chain x) v := by
  obtain ⟨hun,hum⟩ := Finset.mem_erase.mp hu
  obtain ⟨hvn,hvm⟩ := Finset.mem_erase.mp hv
  obtain ⟨hu',hu''⟩ := mem_retainedVertices.mp hum
  obtain ⟨hv',hv''⟩ := mem_retainedVertices.mp hvm
  obtain ⟨σ,_,hm,hfix,_⟩ := alive_swap hb hu'' hv''
  have hxc : x.1.IsPrefix c := hx.symm ▸ ⟨le_rfl, fun _ _ => rfl⟩
  have hfx : σ.val x = x := by
    apply hfix x hxc
    by_cases hi : x.1.stage = b.stage
    · have he : b = x.1 := History.IsPrefix.eq_of_stage_eq (hx ▸ hb) hi.symm
      right
      exact ⟨fun h => hun (Prod.ext (hu'.trans he) h.symm),
        fun h => hvn (Prod.ext (hv'.trans he) h.symm)⟩
    · exact Or.inl hi
  have huv : σ.val u = v := by
    rw [show u = (b,u.2) from Prod.ext hu' rfl, hm]
    exact Prod.ext hv'.symm rfl
  have h := invariant_load σ.val (P.chain x) (fun a b => by
    have e := P.equivariant σ x a b
    rwa [hfx] at e) u
  rw [huv] at h
  exact h.symm

private theorem retentions_shrink {b c d : RollingHistory hw hM n k}
    (hbc : b.IsPrefix c) (hcd : c.IsPrefix d)
    (ht : d.stage.val = c.stage.val + 1) :
    M * (retainedVertices d b).card ≤ (retainedVertices c b).card := by
  rw [retainedVertices, retainedVertices, Finset.card_map, Finset.card_map,
    d.cardinal b.stage d.stage le_rfl, c.cardinal b.stage c.stage le_rfl]
  change M * quota w M b.stage.val d.stage.val ≤ quota w M b.stage.val c.stage.val
  rw [ht]
  by_cases h : c.stage.val + 1 ≤ b.stage.val + w
  · exact (quota_step w M _ _ hbc.1 h).symm.le
  · simp [quota, h]

private theorem retained_subset {b c d : RollingHistory hw hM n k}
    (hcd : c.IsPrefix d) : retainedVertices d b ⊆ retainedVertices c b := by
  intro v hv
  obtain ⟨he,h⟩ := mem_retainedVertices.mp hv
  refine mem_retainedVertices.mpr ⟨he, ?_⟩
  rw [hcd.2 c.stage le_rfl]
  exact d.nested b.stage c.stage d.stage hcd.1 le_rfl h

private theorem refined_load_by_block {R L : ℝ} {b c d : RollingHistory hw hM n k}
    (P : Localized (concreteRetention w n M hw hM) k R L)
    (x : RollingVertex hw hM n k) (hx : x.1 = c) (hbc : b.IsPrefix c) (hcd : c.IsPrefix d)
    (ht : d.stage.val = c.stage.val + 1) (hx' : x ∈ retainedVertices d c) :
    ∑ y ∈ (retainedVertices d b).erase x, load (P.chain x) y ≤
      (∑ y ∈ (retainedVertices c b).erase x, load (P.chain x) y) / M := by
  classical
  apply sum_const_subset_bound _ _ _ M (by omega)
  · exact Finset.erase_subset_erase x (retained_subset hcd)
  · have h := retentions_shrink hbc hcd ht
    by_cases hs : x ∈ retainedVertices c b
    · have he : c = b := hx.symm.trans (mem_retainedVertices.mp hs).1
      have ht' : x ∈ retainedVertices d b := he ▸ hx'
      rw [Finset.card_erase_of_mem ht', Finset.card_erase_of_mem hs]
      have hh := Finset.card_pos.mpr ⟨x, ht'⟩
      have hm : 0 < M := by omega
      calc
        M * ((retainedVertices d b).card - 1) = M * (retainedVertices d b).card - M :=
          by rw [Nat.mul_sub, Nat.mul_one]
        _ ≤ (retainedVertices c b).card - 1 := by omega
    · have ht' : x ∉ retainedVertices d b := fun hm => hs (retained_subset hcd hm)
      rwa [Finset.erase_eq_of_notMem ht', Finset.erase_eq_of_notMem hs]
  · exact load_nonneg _
  · exact fun a ha b hb => surviving_load_const P x hx hbc ha hb

private theorem age_stable {c d : RollingHistory hw hM n k} {v : RollingVertex hw hM n k}
    (hcd : c.IsPrefix d) (t : Fin (n + 1)) (ht : t.val = c.stage.val + 1)
    (htd : t ≤ d.stage) (hn : v.2 ∉ (d.step t).1 v.1.stage) :
    age d v = age c v := by
  have hSet : liveStages d v = liveStages c v := by
    ext i
    simp only [liveStages, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hi, hv⟩
      have hic : i ≤ c.stage := by
        by_contra! hlt
        have hti : t ≤ i := by
          change c.stage.val < i.val at hlt
          exact show t.val ≤ i.val by omega
        exact hn (d.nested _ _ _ hti hi hv)
      exact ⟨hic, hcd.2 i hic ▸ hv⟩
    · rintro ⟨hi,hv⟩
      exact ⟨hi.trans hcd.1, hcd.2 i hi ▸ hv⟩
  simp [age, hSet]

private theorem child_load_bound {R L : ℝ} {b c : RollingHistory hw hM n k}
    (P : Localized (concreteRetention w n M hw hM) k R L)
    (x y : RollingVertex hw hM n k) (hy : y.1 = c)
    (hb : b.IsPrefix c) (hdepth : b.stage < c.stage)
    (hspan : c.stage.val ≤ b.stage.val + w) (hx : x ∈ retainedVertices c b) :
    load (P.chain y) x ≤ 2 * L / M := by
  classical
  have hy' : y ∉ retainedVertices c b := fun hm =>
    hdepth.ne (congrArg History.stage ((mem_retainedVertices.mp hm).1.symm.trans hy))
  have hset : (retainedVertices c b).erase y = retainedVertices c b := Finset.erase_eq_of_notMem hy'
  have hs : ∀ a ∈ retainedVertices c b, load (P.chain y) a = load (P.chain y) x := fun a ha =>
    surviving_load_const P y hy hb (hset.symm ▸ ha) (hset.symm ▸ hx)
  have hcard : M ≤ (retainedVertices c b).card := by
    rw [retainedVertices, Finset.card_map, c.cardinal _ _ le_rfl]
    change M ≤ quota w M b.stage.val c.stage.val
    simp only [quota, hspan, ite_true]
    simpa using pow_le_pow_right' hM
      (show 1 ≤ w + 2 - (c.stage.val - b.stage.val) by omega)
  have hsum : ∑ a ∈ retainedVertices c b, load (P.chain y) a ≤ 2 * L := by
    calc
      _ ≤ ∑ a, load (P.chain y) a :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun a _ _ => load_nonneg _ a)
      _ ≤ _ := by rw [sum_load]; exact mul_le_mul_of_nonneg_left (P.mass_le y) (by norm_num)
  have hEval : ∑ a ∈ retainedVertices c b, load (P.chain y) a =
      ((retainedVertices c b).card : ℝ) * load (P.chain y) x := by
    calc
      _ = ∑ a ∈ retainedVertices c b, load (P.chain y) x :=
        Finset.sum_congr rfl hs
      _ = _ := by simp
  rw [hEval] at hsum
  apply (le_div_iff₀ (show (0 : ℝ) < M by exact_mod_cast (show 0 < M by omega))).2
  have hcard' : (M : ℝ) ≤ (retainedVertices c b).card := by exact_mod_cast hcard
  exact (by
    rw [mul_comm]
    exact (mul_le_mul_of_nonneg_right hcard' (load_nonneg _ _)).trans hsum)

private def retentionError (c d : RollingHistory hw hM n k) (x : RollingVertex hw hM n k) :
    Finset (RollingVertex hw hM n k) := by
  classical
  exact (Finset.univ.filter fun b : RollingHistory hw hM n k => b.IsPrefix c).biUnion
    (fun b => (retainedVertices d b).erase x)

private theorem retentionError_load_bound {R L : ℝ} {c d : RollingHistory hw hM n k}
    (P : Localized (concreteRetention w n M hw hM) k R L)
    (x : RollingVertex hw hM n k) (hx : x.1 = c) (hcd : c.IsPrefix d)
    (ht : d.stage.val = c.stage.val + 1) (hx' : x ∈ retainedVertices d c) :
    ∑ a ∈ retentionError c d x, load (P.chain x) a ≤ 2 * L / M := by
  classical
  let S := Finset.univ.filter fun b : RollingHistory hw hM n k => b.IsPrefix c
  have disj (e : RollingHistory hw hM n k) :
      (↑S : Set _).PairwiseDisjoint (fun b => (retainedVertices e b).erase x) := by
    intro a _ b _ hne
    apply Finset.disjoint_left.mpr
    intro z ha hb
    have ha' := (mem_retainedVertices.mp (Finset.mem_erase.mp ha).2).1
    have hb' := (mem_retainedVertices.mp (Finset.mem_erase.mp hb).2).1
    exact hne (ha'.symm.trans hb')
  change ∑ a ∈ S.biUnion _, load (P.chain x) a ≤ _
  rw [Finset.sum_biUnion (disj d)]
  calc
    _ ≤ ∑ b ∈ S, (∑ a ∈ (retainedVertices c b).erase x, load (P.chain x) a) / M :=
      Finset.sum_le_sum fun b hb =>
        refined_load_by_block P x hx (Finset.mem_filter.mp hb).2 hcd ht hx'
    _ = (∑ a ∈ S.biUnion (fun b => (retainedVertices c b).erase x), load (P.chain x) a) / M := by
      rw [Finset.sum_biUnion (disj c)]
      simp only [div_eq_mul_inv, Finset.sum_mul]
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun a _ _ => load_nonneg _ a)).trans ?_
      rw [sum_load]
      exact mul_le_mul_of_nonneg_left (P.mass_le x) (by norm_num)

private theorem sum_band {w : ℕ} (hw : 0 < w) (u v : ℕ) :
    ∑ r : Fin w, band r u v = 0 := by
  unfold band
  split
  · unfold bandForward
    split <;> simp [Finset.sum_add_distrib, sum_residue hw]
  · split
    · unfold bandForward
      split <;> simp [Finset.sum_add_distrib, sum_residue hw]
    · simp

private def ageCochain (r : Fin w) (b : RollingHistory hw hM n k) :
    Chains (RollingVertex hw hM n k) :=
  fun e => band r (age b e.1) (age b e.2)

private def testCochain (r : Fin w) (i : ℕ) (b : RollingHistory hw hM n k)
    (x y : RollingVertex hw hM n k) : Chains (RollingVertex hw hM n k) :=
  fun e => tagValue r i (tagAge b x y e.1) (tagAge b x y e.2)

private theorem testCochain_skew (r : Fin w) (i : ℕ) (b : RollingHistory hw hM n k)
    (x y u v : RollingVertex hw hM n k) : testCochain r i b x y (v,u) =
      -testCochain r i b x y (u,v) :=
  tagValue_skew r i _ _

private theorem testCochain_eval_residual {R L : ℝ} (r : Fin w) {b c : RollingHistory hw hM n k}
    (P : Localized (concreteRetention w n M hw hM) k R L)
    (x y : RollingVertex hw hM n k) (hx : x.1 = b) (hy : y.1 = c)
    (hbc : b.IsPrefix c) (hd : b.stage < c.stage) (hs : c.stage.val ≤ b.stage.val+w)
    (hedge : (RollingG hw hM n k).Adj x y) :
    1 + pairing (testCochain r c.stage.val c x y) (P.chain x) -
      pairing (testCochain r c.stage.val c x y) (P.chain y) ≤ R := by
  classical
  let G := RollingG hw hM n k
  let F := testCochain r c.stage.val c x y
  let f := pullCochain (spineMap c) F
  have hf : ∀ u v, f (v,u) = -f (u,v) := fun _ _ => testCochain_skew _ _ _ _ _ _ _
  have h₁ : Admissible (triangleChain (G := G)) f := by
    refine ⟨fun e => tagValue_abs _ _ _ _, fun ⟨⟨u,v,z⟩,huv,hvz,huz⟩ => ?_⟩
    change |pairing f (orientedEdge u v + orientedEdge v z - orientedEdge u z)| ≤ 1
    rw [pairing_triangle f hf]
    have hP (a d : RollingVertex hw hM n k) (e : G.Adj a d) :
        tagPair w b.stage.val c.stage.val (tagAge c x y (spineMap c a)) (tagAge c x y (spineMap c d)) := by
      rcases spineMap_edge c e with he | he
      · rw [he]
        cases tagAge c x y (spineMap c d)
        · exact ⟨by omega, by omega⟩
        · rename_i a
          cases a <;> trivial
      · have h := tagged_age_edge (hx.symm ▸ hbc) hy hedge.ne
          (spineMap_on_spine c a) (spineMap_on_spine c d) he
        simpa [hx] using h
    exact tagValue_defect r hs _ _ _ (hP u v huv) (hP v z hvz) (hP u z huz)
  have hconst (a : RollingVertex hw hM n k) (ha : a.1.IsPrefix c) :
      spineMap c a = a := spineMap_fixed ha
  have hread (a : RollingVertex hw hM n k) (ha : a.1.IsPrefix c) :
      pairing f (P.chain a) = pairing F (P.chain a) := by
    unfold pairing
    apply Finset.sum_congr rfl
    intro e _
    by_cases he : histPre e.1 a ∧ histPre e.2 a
    · simp [f, pullCochain, hconst _ ((historyData _).trans he.1 ha),
        hconst _ ((historyData _).trans he.2 ha)]
    · simp [P.support a e.1 e.2 (fun h => he ⟨h.1,h.2.1⟩)]
  have hx' : x.1.IsPrefix c := hx.symm ▸ hbc
  have hy' : y.1.IsPrefix c := hy.symm ▸ ⟨le_rfl, fun _ _ => rfl⟩
  have hEdge : f (x,y) = 1 := by simp [f, F, pullCochain, hconst _ hx', hconst _ hy',
    testCochain, tagAge, hedge.ne, Ne.symm hedge.ne, tagValue]
  have hfit := (abs_pairing_le_dualNorm h₁ (orientedEdge x y + P.chain x - P.chain y)).trans
    (P.residual x y hedge)
  rw [pairing_chain_sub, pairing_chain_add, pairing_orientedEdge _ _ _ hf,
    hread _ hx', hread _ hy', hEdge] at hfit
  exact (le_abs_self _).trans hfit

private theorem newest_neighbour_age {c : RollingHistory hw hM n k}
    {x a : RollingVertex hw hM n k} (hx : x.1 = c) (ha : a.1.IsPrefix c)
    (h : a = x ∨ (RollingG hw hM n k).Adj a x) : age c a = c.stage.val := by
  apply le_antisymm (age_le_stage _ _)
  rcases h with rfl | h
  · simpa [hx] using birth_le_age ha
  · have hx' : x.1.IsPrefix c := hx.symm ▸ ⟨le_rfl, fun _ _ => rfl⟩
    simpa [hx] using age_ge_of_adj hx' h (hx.symm ▸ ha.1)

private theorem parent_coarse {R L : ℝ} (r : Fin w) (i : ℕ) {b : RollingHistory hw hM n k}
    (P : Localized (concreteRetention w n M hw hM) k R L)
    (x y : RollingVertex hw hM n k) (hx : x.1 = b)
    (hi : b.stage.val < i) (hy : b.stage < y.1.stage) :
    pairing (testCochain r i b x y) (P.chain x) =
      pairing (ageCochain r b) (P.chain x) +
        (band r b.stage.val i + 1) * (1 - rootMass x) := by
  classical
  let A := band r b.stage.val i + 1
  let g : Chains (RollingVertex hw hM n k) := fun e =>
    A * ((if e.2 = x then 1 else 0) - (if e.1 = x then 1 else 0))
  have hdiag (a : ℕ) : band r a a = 0 := by simp [band]
  have he : pairing (testCochain r i b x y) (P.chain x) =
      pairing (ageCochain r b + g) (P.chain x) := by
    unfold pairing
    apply Finset.sum_congr rfl
    rintro ⟨a,d⟩ _
    by_cases h0 : P.chain x (a,d) = 0
    · simp [h0]
    have hs := not_not.mp (fun hn => h0 (P.support x a d hn))
    have ha : a.1.IsPrefix b := hx ▸ hs.1
    have hd : d.1.IsPrefix b := hx ▸ hs.2.1
    have hay : a ≠ y := fun h => (ha.1.trans_lt hy).ne (congrArg (fun v => v.1.stage) h)
    have hdy : d ≠ y := fun h => (hd.1.trans_lt hy).ne (congrArg (fun v => v.1.stage) h)
    congr 1
    by_cases hax : a = x <;> by_cases hdx : d = x
    · simp [testCochain, ageCochain, tagAge, tagValue, g, hax, hdx, hdiag]
    · subst a
      have h₁ := newest_neighbour_age hx hd (hs.2.2.imp Eq.symm SimpleGraph.Adj.symm)
      have h₂ := newest_neighbour_age hx ha (Or.inl rfl)
      simp [testCochain, ageCochain, tagAge, tagValue, g, hdx, hdy, h₁, h₂, A, hi.ne, hdiag]
    · subst d
      have h₁ := newest_neighbour_age hx ha hs.2.2
      have h₂ := newest_neighbour_age hx hd (Or.inl rfl)
      simp [testCochain, ageCochain, tagAge, tagValue, g, hax, hay, h₁, h₂, A, hi.ne, hdiag]
    · simp [testCochain, ageCochain, tagAge, tagValue, g, hax, hdx, hay, hdy]
  rw [he]
  have hlin : pairing (ageCochain r b + g) (P.chain x) =
      pairing (ageCochain r b) (P.chain x) + pairing g (P.chain x) := by
    simp [pairing, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  rw [hlin]
  have hg : pairing g (P.chain x) = A * boundary (P.chain x) x :=
    pairing_incident _ _ _
  rw [hg, P.boundary_eq]
  simp [A, Pi.single_apply]

private theorem parent_refinement {R L : ℝ} (r : Fin w) {b c : RollingHistory hw hM n k}
    (P : Localized (concreteRetention w n M hw hM) k R L)
    (x y : RollingVertex hw hM n k) (hx : x.1 = b) (hy : y.1 = c)
    (hbc : b.IsPrefix c) (hd : b.stage < c.stage) (hkeep : x ∈ retainedVertices c b) :
    |pairing (testCochain r c.stage.val c x y) (P.chain x) -
      pairing (testCochain r c.stage.val b x y) (P.chain x)| ≤ 12 * L / M := by
  classical
  let t : Fin (n + 1) := ⟨b.stage.val + 1, (Nat.succ_le_of_lt hd).trans_lt c.stage.isLt⟩
  have htc : t ≤ c.stage := Nat.succ_le_of_lt hd
  let d := c.prefix t htc
  have hbd : b.IsPrefix d := ⟨(show b.stage ≤ t from Nat.le_succ _), fun j hj => by
      change b.step j = if j ≤ t then c.step j else _
      rw [ite_eq_left (hj.trans (show b.stage ≤ t from Nat.le_succ _))]
      exact hbc.2 j hj⟩
  have hdc := c.prefix_spec t htc
  have hxkeep : x ∈ retainedVertices d b := retained_subset hdc hkeep
  let S := retentionError b d x
  have hconst (a : RollingVertex hw hM n k) (ha : a.1.IsPrefix b) (hn : a ∉ S) :
      tagAge c x y a = tagAge b x y a := by
    by_cases hax : a = x
    · simp [tagAge,hax]
    · by_cases hay : a = y
      · simp [tagAge,hax,hay]
      · have hno : a.2 ∉ (c.step t).1 a.1.stage := by
          intro hm
          apply hn
          apply Finset.mem_biUnion.mpr
          refine ⟨a.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩,
            Finset.mem_erase.mpr ⟨hax,mem_retainedVertices.mpr ⟨rfl,?_⟩⟩⟩
          simpa [d, History.prefix] using hm
        simp [tagAge,hax,hay,age_stable hbc t rfl htc hno]
  have hbound := abs_pairing_change_le (testCochain r c.stage.val c x y)
    (testCochain r c.stage.val b x y) (P.chain x) S 6 (by norm_num)
    (fun e => (abs_sub _ _).trans ((add_le_add (tagValue_abs _ _ _ _) (tagValue_abs _ _ _ _)).trans (by norm_num)))
    (fun a d ha hd hne => by
      have hs := not_not.mp (fun hn => hne (P.support x a d hn))
      simp [testCochain, hconst a (hx ▸ hs.1) ha, hconst d (hx ▸ hs.2.1) hd])
  exact hbound.trans ((mul_le_mul_of_nonneg_left (retentionError_load_bound P x hx hbd rfl hxkeep)
    (by norm_num)).trans_eq (by ring))

private theorem child_refinement {R L : ℝ} (r : Fin w) {b c : RollingHistory hw hM n k}
    (P : Localized (concreteRetention w n M hw hM) k R L)
    (x y : RollingVertex hw hM n k) (hy : y.1 = c) (hbc : b.IsPrefix c)
    (hd : b.stage < c.stage) (hs : c.stage.val ≤ b.stage.val + w) (hkeep : x ∈ retainedVertices c b) :
    |pairing (testCochain r c.stage.val c x y) (P.chain y) -
      pairing (ageCochain r c) (P.chain y)| ≤ 12 * L / M := by
  classical
  have hdiag : band r c.stage.val c.stage.val = 0 := by simp [band]
  have hbound := abs_pairing_change_le (testCochain r c.stage.val c x y)
    (ageCochain r c) (P.chain y) {x} 6 (by norm_num)
    (fun e => (abs_sub _ _).trans ((add_le_add (tagValue_abs _ _ _ _) (band_abs_le _ _ _)).trans (by norm_num)))
    (fun a d ha hd hne => by
      have ha' : a ≠ x := by simpa using ha
      have hd' : d ≠ x := by simpa using hd
      have H := not_not.mp (fun hn => hne (P.support y a d hn))
      by_cases hay : a = y <;> by_cases hdy : d = y
      · subst a; subst d
        have h := newest_neighbour_age hy (hy ▸ H.1) (Or.inl rfl)
        simp [testCochain, ageCochain, tagAge, tagValue, ha', h, hdiag]
      · subst a
        have h₁ := newest_neighbour_age hy (hy ▸ H.1) (Or.inl rfl)
        have h₂ := newest_neighbour_age hy (hy ▸ H.2.1) (H.2.2.imp Eq.symm SimpleGraph.Adj.symm)
        simp [testCochain, ageCochain, tagAge, tagValue, ha',hd',hdy,h₁,h₂,hdiag]
      · subst d
        have h₁ := newest_neighbour_age hy (hy ▸ H.1) H.2.2
        have h₂ := newest_neighbour_age hy (hy ▸ H.2.1) (Or.inl rfl)
        simp [testCochain, ageCochain, tagAge, tagValue, ha',hd',hay,h₁,h₂,hdiag]
      · simp [testCochain, ageCochain, tagAge, tagValue, ha',hd',hay,hdy])
  simp only [Finset.sum_singleton] at hbound
  exact hbound.trans ((mul_le_mul_of_nonneg_left (child_load_bound P x y hy hbc hd hs hkeep)
    (by norm_num)).trans_eq (by ring))


private theorem age_pairing_independent {R L : ℝ} (r : Fin w) (b : RollingHistory hw hM n k)
    (P : Localized (concreteRetention w n M hw hM) k R L) (s t : Fin (M^(w+2))) :
    pairing (ageCochain r b) (P.chain (b,s)) =
      pairing (ageCochain r b) (P.chain (b,t)) := by
  classical
  have hb : b.IsPrefix b := ⟨le_rfl, fun _ _ => rfl⟩
  obtain ⟨σ,_,hσ,_,ha⟩ := alive_swap hb (birth_live (v := (b,s)) hb) (birth_live (v := (b,t)) hb)
  unfold pairing
  rw [← Equiv.sum_comp (σ.val.prodCongr σ.val)
    (fun e : RollingVertex hw hM n k × RollingVertex hw hM n k =>
      ageCochain r b e * P.chain (b,t) e)]
  apply Finset.sum_congr rfl
  rintro ⟨a,d⟩ _
  change _ * _ = ageCochain r b (σ.val a,σ.val d) * P.chain (b,t) (σ.val a,σ.val d)
  rw [← hσ, P.equivariant]
  by_cases h : a.1.IsPrefix b ∧ d.1.IsPrefix b
  · simp [ageCochain, ha a h.1, ha d h.2]
  · simp [P.support (b,s) a d (fun hs => h ⟨hs.1,hs.2.1⟩)]

private theorem band_transfer {R L : ℝ} (r : Fin w) {b c : RollingHistory hw hM n k}
    (P : Localized (concreteRetention w n M hw hM) k R L)
    (x y : RollingVertex hw hM n k) (hx : x.1 = b) (hy : y.1 = c)
    (hbc : b.IsPrefix c) (hd : b.stage < c.stage) (hs : c.stage.val ≤ b.stage.val + w)
    (hkeep : x ∈ retainedVertices c b) :
    2 + band r b.stage.val c.stage.val + pairing (ageCochain r b) (P.chain x) -
      pairing (ageCochain r c) (P.chain y) ≤ R + 24 * L / M + 3 / (M ^ (w+2) : ℝ) := by
  classical
  have hne : x ≠ y := fun e => hd.ne (congrArg History.stage (hx.symm.trans ((congrArg Prod.fst e).trans hy)))
  have hEdge : (RollingG hw hM n k).Adj x y := by
    refine ⟨hne, Or.inr (Or.inl ⟨?_, ?_⟩)⟩
    · change x.1.IsPrefix y.1
      rw [hx,hy]
      exact hbc
    · change x.2 ∈ (y.1.step y.1.stage).1 x.1.stage
      rw [hx,hy]
      exact (mem_retainedVertices.mp hkeep).2
  have htest := testCochain_eval_residual r P x y hx hy hbc hd hs hEdge
  have h₁ := (abs_le.mp (parent_refinement r P x y hx hy hbc hd hkeep)).1
  have h₂ := (abs_le.mp (child_refinement r P x y hy hbc hd hs hkeep)).2
  rw [parent_coarse r _ P x y hx (show b.stage.val < c.stage.val from hd) (hy.symm ▸ hd)] at h₁
  have hroot : 0 ≤ rootMass x ∧ rootMass x ≤ ((M : ℝ) ^ (w+2))⁻¹ := by
    unfold rootMass
    split
    · rw [Nat.cast_pow]
      exact ⟨by positivity, le_rfl⟩
    · exact ⟨le_rfl, by positivity⟩
  have hfactor : (band r b.stage.val c.stage.val + 1) * rootMass x ≤
      3 / (M ^ (w+2) : ℝ) := by
    have hr := (abs_le.mp (band_abs_le r b.stage.val c.stage.val)).2
    calc
      _ ≤ 3 * rootMass x := mul_le_mul_of_nonneg_right (by linarith) hroot.1
      _ ≤ _ := by rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_left hroot.2 (by norm_num)
  rw [mul_sub, mul_one] at h₁
  have herr : (24 : ℝ) * L / M = 12 * L / M + 12 * L / M := by ring
  rw [herr]
  linarith

private theorem localized_band {R L : ℝ}
    (P : Localized (concreteRetention w n M hw hM) k R L) :
    ∃ H : Fin w → ℕ → ℝ, (∀ t, ∑ r, H r t = 0) ∧
      ∀ r u v, u < v → v ≤ u + w → v ≤ n →
        2 + band r u v + H r u - H r v ≤ R + 24 * L / M + 3 / (M ^ (w+2) : ℝ) := by
  classical
  let top := fullSpine w n M k hw hM
  let a (t : ℕ) (ht : t ≤ n) : RollingHistory hw hM n k :=
    top.prefix ⟨t, Nat.lt_succ_of_le ht⟩ ht
  have aq (t : ℕ) (ht : t ≤ n) : (a t ht).stage.val = t := rfl
  let zeroLabel : Fin (M^(w+2)) := ⟨0, pow_pos (by omega) _⟩
  let H (r : Fin w) (t : ℕ) : ℝ := if ht : t ≤ n then
    pairing (ageCochain r (a t ht)) (P.chain (a t ht,zeroLabel)) else 0
  refine ⟨H, ?_, ?_⟩
  · intro t
    by_cases ht : t ≤ n
    · unfold H
      simp only [dif_pos ht, pairing, ageCochain]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul, sum_band (show 0 < w by omega), zero_mul, Finset.sum_const_zero]
    · simp [H,ht]
  · intro r u v huv hwv hnv
    have hnu : u ≤ n := huv.le.trans hnv
    let b := a u hnu
    let c := a v hnv
    have hbc : b.IsPrefix c := by
      refine ⟨huv.le, fun i hi => ?_⟩
      have hi' : i ≤ c.stage := hi.trans huv.le
      change (if i ≤ b.stage then top.step i else _) = (if i ≤ c.stage then top.step i else _)
      rw [ite_eq_left hi, ite_eq_left hi']
    have hd : b.stage < c.stage := huv
    have hs : c.stage.val ≤ b.stage.val+w := hwv
    have hcard : 0 < ((c.step c.stage).1 b.stage).card := by
      rw [c.cardinal _ _ le_rfl]
      change 0 < quota w M u v
      simp [quota, hwv, pow_pos (show 0 < M by omega)]
    obtain ⟨s,hs'⟩ := Finset.card_pos.mp hcard
    let x : RollingVertex hw hM n k := (b,s)
    let y : RollingVertex hw hM n k := (c,zeroLabel)
    have hb := band_transfer r P x y rfl rfl hbc hd hs (mem_retainedVertices.mpr ⟨rfl,hs'⟩)
    change 2 + band r u v + pairing (ageCochain r b) (P.chain (b,s)) -
      pairing (ageCochain r c) (P.chain (c,zeroLabel)) ≤ _ at hb
    rw [age_pairing_independent r b P s zeroLabel] at hb
    simpa [H, hnu, hnv, b, c, a] using hb


end Ages

end

end SimpleGraph.ChordalReconstruction

namespace SimpleGraph

open ChordalReconstruction

/-- For every positive tolerance, a finite connected chordal graph has a triangle-flat
Banach-valued gain whose reconstruction error is at least four minus that tolerance. -/
theorem exists_chordal_banach_gain_lower_four (ε : ℝ) (hε : 0 < ε) :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V), G.IsChordal ∧ G.Connected ∧
      ∃ (E : Type) (N : NormedAddCommGroup E) (S : @NormedSpace ℝ E _ N.toSeminormedAddCommGroup),
        letI := N
        letI := S
        ∃ (_ : CompleteSpace E) (_ : FiniteDimensional ℝ E) (g : V → V → E),
          (∀ u v, g v u = -g u v) ∧
          (∀ u v z, G.Adj u v → G.Adj v z → G.Adj u z → ‖g u v + g v z - g u z‖ ≤ 1) ∧
          ∀ φ : V → E, ∃ u v, G.Adj u v ∧ 4 - ε ≤ ‖g u v - (φ v - φ u)‖ := by
  classical
  obtain ⟨m,hm,hparam⟩ := band_parameters ε hε
  let n := m * m + m + 1
  let L : ℝ := 13 * (n + 1)
  have hL : 0 < L := by positivity
  obtain ⟨M,hM⟩ := exists_nat_gt (max 1 (4 * (24 * L + 3) / ε))
  obtain ⟨k,hk⟩ := exists_nat_gt (4 * (12 * L) / ε)
  have hM₁ : (1 : ℝ) < M := (le_max_left _ _).trans_lt hM
  have hM' : 1 ≤ M := by exact_mod_cast hM₁.le
  have hM₂ : 4 * (24 * L + 3) < (M : ℝ) * ε :=
    (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hM)
  have hk' : 4 * (12 * L) < (k : ℝ) * ε := (div_lt_iff₀ hε).mp hk
  have hMerr : (24 * L + 3) / (M : ℝ) < ε / 4 := by
    apply (div_lt_iff₀ (show (0 : ℝ) < M by linarith)).2
    nlinarith
  have hkerr : 12 * L / ((k : ℝ) + 1) < ε / 4 := by
    apply (div_lt_iff₀ (show (0 : ℝ) < (k : ℝ) + 1 by positivity)).2
    nlinarith
  have hpow : (M : ℝ) ≤ (M : ℝ) ^ (m+2) := by
    simpa using pow_le_pow_right₀ hM₁.le (show 1 ≤ m+2 by omega)
  have hqerr : (3 : ℝ) / (M : ℝ) ^ (m+2) ≤ 3 / (M : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by linarith) hpow
  have hErr : 12 * L / ((k : ℝ) + 1) + 24 * L / (M : ℝ) +
      3 / (M : ℝ) ^ (m+2) ≤ ε / 2 := by
    rw [add_div] at hMerr
    linarith
  let P := concreteRetention m n M hm hM'
  let G : SimpleGraph (HV P k) := histGraph P k
  let x₀ : Fin (M^(m+2)) := ⟨0, pow_pos (by omega) _⟩
  let o : HV P k := (History.initial P,x₀)
  have hconn := rolling_connected (historyData (k := k) P) x₀
  refine ⟨HV P k, inferInstance, G, rolling_chordal _, hconn, ?_⟩
  apply gain_of_rooted_chain_obstruction G hconn o (4 - ε)
  intro p hsupport hboundary
  by_contra! hfail
  obtain ⟨p'⟩ := obtain_localized (P := P) x₀.isLt (4 - ε) (by linarith) o p hsupport hboundary
    (fun u v hu => (hfail u v hu).le)
  obtain ⟨H,hH,hband⟩ := localized_band p'
  apply band_contradiction ε hm hparam H hH
  intro r u v huv hwv hnv
  have h := hband r u v huv hwv hnv
  change 2 + band r u v + H r u - H r v ≤
    4 - ε + 12 * L / ((k : ℝ) + 1) + 24 * L / M + 3 / (M : ℝ) ^ (m+2) at h
  linarith

end SimpleGraph

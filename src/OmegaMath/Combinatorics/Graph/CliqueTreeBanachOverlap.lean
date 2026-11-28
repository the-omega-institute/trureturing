import OmegaBuild.Commands
import OmegaMath.Combinatorics.Graph.CliqueTreeL1Separator
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

compile_only_with_mathlib

/-! Omega original.

Weighted clique extension with bounds on successive separators.
-/

open scoped BigOperators
namespace SimpleGraph.CliqueTreeBanachOverlap
universe u v w
variable {V : Type u} {I : Type w} {G : SimpleGraph V} {T : SimpleGraph I} {K : I → Set V}
variable {E : Type v} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

open CliqueTreeL1Separator

noncomputable def wavg (S : Finset V) (w : V → ℝ) (f : V → E) : E :=
  ∑ t ∈ S, w t • f t

theorem wavg_sub (S : Finset V) (w : V → ℝ) (f h : V → E) :
    wavg S w f - wavg S w h = wavg S w (fun t => f t - h t) := by
  simp [wavg, smul_sub, Finset.sum_sub_distrib]

theorem wavg_const (S : Finset V) (w : V → ℝ) (hw : ∑ t ∈ S, w t = 1) (e : E) :
    wavg S w (fun _ => e) = e := by
  simp only [wavg, ← Finset.sum_smul, hw, one_smul]

theorem const_sub_wavg (S : Finset V) (w : V → ℝ) (hw : ∑ t ∈ S, w t = 1)
    (e : E) (f : V → E) :
    e - wavg S w f = wavg S w (fun t => e - f t) := by
  rw [← wavg_const S w hw e, wavg_sub]
  rw [wavg_const S w hw e]

theorem wavg_norm (S : Finset V) (w : V → ℝ) (f : V → E)
    (hw : ∀ t ∈ S, 0 ≤ w t) :
    ‖wavg S w f‖ ≤ ∑ t ∈ S, w t * ‖f t‖ := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t ht => ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw t ht)]

/-- Weighted extension with an explicit row certificate. All fresh vertices use
exactly the same weights, so their mutual errors stay at most epsilon. -/
theorem local_weighted [DecidableEq V] {S : Finset V} {A : Set V}
    (hSA : (S : Set V) ⊆ A) (hcl : G.IsClique A)
    (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε)
    (hrev : ∀ i j, g j i = -g i j) (htri : TriangleFlat G g ε)
    (p : V → E) (C : V → V → ℝ)
    (hfit : ∀ i ∈ S, ∀ j ∈ S, G.Adj i j →
      ‖g i j - (p j - p i)‖ ≤ C i j * ε)
    (w : V → ℝ) (hw : ∀ t ∈ S, 0 ≤ w t) (hmass : ∑ t ∈ S, w t = 1)
    (B : ℝ) (hrow : ∀ i ∈ S, ∑ t ∈ S.erase i, w t * (1 + C i t) ≤ B) :
    ∃ q : V → E, (∀ i ∈ S, q i = p i) ∧
      (∀ i ∈ S, ∀ v ∈ A, v ∉ S → ‖g i v - (q v - q i)‖ ≤ B * ε) ∧
      (∀ u ∈ A, u ∉ S → ∀ v ∈ A, v ∉ S → G.Adj u v →
        ‖g u v - (q v - q u)‖ ≤ ε) := by
  classical
  let b v := wavg S w (fun t => p t + g t v)
  let q v := if v ∈ S then p v else b v
  refine ⟨q, fun i hi => by simp [q, hi], ?_, ?_⟩
  · intro i hi v hv hvs
    have he : g i v - (q v - q i) =
        wavg S w (fun t => (p i + g i v) - (p t + g t v)) := by
      rw [← const_sub_wavg S w hmass]
      simp only [q, ite_eq_left hi, ite_eq_right hvs, b]
      abel
    rw [he]
    have hz : wavg S w (fun t => (p i + g i v) - (p t + g t v)) =
        wavg (S.erase i) w (fun t => (p i + g i v) - (p t + g t v)) := by
      simp only [wavg]
      exact (Finset.sum_subset (Finset.erase_subset _ _) (by
        intro t ht hnt
        have : t = i := by simpa [ht] using hnt
        subst t
        simp)).symm
    rw [hz]
    calc
      _ ≤ ∑ t ∈ S.erase i, w t * ‖(p i + g i v) - (p t + g t v)‖ :=
        wavg_norm _ _ _ (fun t ht => hw t (Finset.mem_of_mem_erase ht))
      _ ≤ ∑ t ∈ S.erase i, w t * ((1 + C i t) * ε) := by
        apply Finset.sum_le_sum
        intro t ht
        obtain ⟨hti, hts⟩ := Finset.mem_erase.mp ht
        apply mul_le_mul_of_nonneg_left _ (hw t hts)
        have hit := hcl (hSA hi) (hSA hts) hti.symm
        have hd := defect_bound g ε hε hrev htri (fun _ => hit)
          (fun hn => hcl hv (hSA hi) hn) (fun hn => hcl hv (hSA hts) hn)
        rw [show (p i + g i v) - (p t + g t v) =
          (g i t - (p t - p i)) - (g i t - (g v t - g v i)) by
            rw [hrev i v, hrev t v]; abel]
        exact (norm_sub_le _ _).trans (by linarith [hfit i hi t hts hit])
      _ = (∑ t ∈ S.erase i, w t * (1 + C i t)) * ε := by
        rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro t ht; ring
      _ ≤ B * ε := mul_le_mul_of_nonneg_right (hrow i hi) hε
  · intro u hu hus v hv hvs huv
    have he : g u v - (q v - q u) =
        wavg S w (fun t => g u v - (g t v - g t u)) := by
      simp only [q, ite_eq_right hus, ite_eq_right hvs, b]
      rw [wavg_sub, const_sub_wavg S w hmass]
      congr 1; funext t; abel
    rw [he]
    calc
      _ ≤ ∑ t ∈ S, w t * ‖g u v - (g t v - g t u)‖ := wavg_norm _ _ _ hw
      _ ≤ ∑ t ∈ S, w t * ε := by
        apply Finset.sum_le_sum
        intro t ht
        exact mul_le_mul_of_nonneg_left
          (defect_bound g ε hε hrev htri (fun _ => huv)
            (fun hn => hcl (hSA ht) hu hn) (fun hn => hcl (hSA ht) hv hn)) (hw t ht)
      _ = ε := by rw [← Finset.sum_mul, hmass, one_mul]

/-- The separator's old/old, old/fresh, and fresh/fresh residual coefficients. -/
def birthCost [DecidableEq V] (O : Finset V) (C : ℝ) (u v : V) : ℝ :=
  if u ∈ O then (if v ∈ O then 2 else C) else (if v ∈ O then C else 1)

/-- Two constant weights, one on each birth class. -/
def birthWeight [DecidableEq V] (O : Finset V) (a b : ℝ) (t : V) : ℝ := if t ∈ O then a else b

/-- Exact row sums, including deletion of the zero diagonal summand. -/
theorem birth_rows [DecidableEq V] (O F : Finset V) (hdis : Disjoint O F)
    (C a b : ℝ) :
    (∑ t ∈ O ∪ F, birthWeight O a b t = (O.card : ℝ) * a + F.card * b) ∧
    (∀ i ∈ O, ∑ t ∈ (O ∪ F).erase i,
      birthWeight O a b t * (1 + birthCost O C i t) =
      ((O.card : ℝ) - 1) * a * 3 + F.card * b * (1 + C)) ∧
    (∀ i ∈ F, ∑ t ∈ (O ∪ F).erase i,
      birthWeight O a b t * (1 + birthCost O C i t) =
      (O.card : ℝ) * a * (1 + C) + ((F.card : ℝ) - 1) * b * 2) := by
  classical
  have no (t : V) (ht : t ∈ F) : t ∉ O := fun ho => Finset.disjoint_left.mp hdis ho ht
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.sum_union hdis]
    rw [Finset.sum_congr rfl (fun t ht => show birthWeight O a b t = a by simp [birthWeight, ht]),
      Finset.sum_congr rfl (fun t ht => show birthWeight O a b t = b by simp [birthWeight, no t ht])]
    simp
  · intro i hi
    have he : (O ∪ F).erase i = O.erase i ∪ F := by
      ext t; simp only [Finset.mem_erase, Finset.mem_union];
      constructor
      · rintro ⟨hne, ht | ht⟩; exact Or.inl ⟨hne, ht⟩; exact Or.inr ht
      · rintro (⟨hne, ht⟩ | ht); exact ⟨hne, Or.inl ht⟩
        exact ⟨fun h => no i (h ▸ ht) hi, Or.inr ht⟩
    rw [he, Finset.sum_union (hdis.mono_left (Finset.erase_subset _ _))]
    have hc : ((O.erase i).card : ℝ) = O.card - 1 := by
      have h : ((O.erase i).card : ℝ) + 1 = O.card := by exact_mod_cast Finset.card_erase_add_one hi
      linarith
    rw [Finset.sum_congr rfl (fun t ht => show
        birthWeight O a b t * (1 + birthCost O C i t) = a * 3 by
          norm_num [birthWeight, birthCost, hi, Finset.mem_of_mem_erase ht]),
      Finset.sum_congr rfl (fun t ht => show
        birthWeight O a b t * (1 + birthCost O C i t) = b * (1 + C) by
          simp [birthWeight, birthCost, hi, no t ht])]
    simp only [Finset.sum_const, nsmul_eq_mul, hc]
    ring
  · intro i hi
    have he : (O ∪ F).erase i = O ∪ F.erase i := by
      ext t; simp only [Finset.mem_erase, Finset.mem_union];
      constructor
      · rintro ⟨hne, ht | ht⟩; exact Or.inl ht; exact Or.inr ⟨hne, ht⟩
      · rintro (ht | ⟨hne, ht⟩)
        exact ⟨fun h => no i hi (h ▸ ht), Or.inl ht⟩
        exact ⟨hne, Or.inr ht⟩
    rw [he, Finset.sum_union (hdis.mono_right (Finset.erase_subset _ _))]
    have hc : ((F.erase i).card : ℝ) = F.card - 1 := by
      have h : ((F.erase i).card : ℝ) + 1 = F.card := by exact_mod_cast Finset.card_erase_add_one hi
      linarith
    have no' (t : V) (ht : t ∈ F.erase i) : t ∉ O := no t (Finset.mem_of_mem_erase ht)
    rw [Finset.sum_congr rfl (fun t ht => show
        birthWeight O a b t * (1 + birthCost O C i t) = a * (1 + C) by
          simp [birthWeight, birthCost, no i hi, ht]),
      Finset.sum_congr rfl (fun t ht => show
        birthWeight O a b t * (1 + birthCost O C i t) = b * 2 by
          norm_num [birthWeight, birthCost, no i hi, no' t ht])]
    simp only [Finset.sum_const, nsmul_eq_mul, hc]
    ring

/-- All rational cases in the size-four-through-six, previous-size-at-most-two rule. -/
theorem following_small_numbers (i k : ℕ) (hi : i ≤ 2)
    (hlo : 4 ≤ i + k) (hhi : i + k ≤ 6) :
    let a : ℝ := 1 / 4
    let b : ℝ := (1 - (i : ℝ) / 4) / k
    0 ≤ a ∧ 0 ≤ b ∧ (i : ℝ) * a + k * b = 1 ∧
    (0 < i → ((i : ℝ) - 1) * a * 3 + k * b * (1 + 3/2) ≤ 2) ∧
    (i : ℝ) * a * (1 + 3/2) + ((k : ℝ) - 1) * b * 2 ≤ 2 := by
  have hk : k ≤ 6 := by omega
  interval_cases i <;> interval_cases k <;> norm_num at *

/-- All rational cases in the size-four-through-five, overlap-at-most-one rule. -/
theorem overlap_one_numbers (i k : ℕ) (hi : i ≤ 1)
    (hlo : 4 ≤ i + k) (hhi : i + k ≤ 5) :
    let a : ℝ := 1 / 3
    let b : ℝ := (1 - (i : ℝ) / 3) / k
    0 ≤ a ∧ 0 ≤ b ∧ (i : ℝ) * a + k * b = 1 ∧
    (0 < i → ((i : ℝ) - 1) * a * 3 + k * b * (1 + 2) ≤ 2) ∧
    (i : ℝ) * a * (1 + 2) + ((k : ℝ) - 1) * b * 2 ≤ 2 := by
  have hk : k ≤ 5 := by omega
  interval_cases i <;> interval_cases k <;> norm_num at *

/-- Local partition extension, retaining fresh--fresh control. -/
theorem partition_extension [DecidableEq V] (O F : Finset V) (hdis : Disjoint O F)
    {A : Set V} (hSA : ((O ∪ F : Finset V) : Set V) ⊆ A) (hcl : G.IsClique A)
    (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε)
    (hrev : ∀ i j, g j i = -g i j) (htri : TriangleFlat G g ε)
    (p : V → E) (C a b : ℝ)
    (hfit : ∀ i ∈ O ∪ F, ∀ j ∈ O ∪ F, G.Adj i j →
      ‖g i j - (p j - p i)‖ ≤ birthCost O C i j * ε)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hmass : (O.card : ℝ) * a + F.card * b = 1)
    (hold : 0 < O.card → ((O.card : ℝ) - 1) * a * 3 + F.card * b * (1 + C) ≤ 2)
    (hfresh : (O.card : ℝ) * a * (1 + C) + ((F.card : ℝ) - 1) * b * 2 ≤ 2) :
    ∃ q : V → E, (∀ i ∈ O ∪ F, q i = p i) ∧
      (∀ i ∈ O ∪ F, ∀ v ∈ A, v ∉ O ∪ F → ‖g i v - (q v - q i)‖ ≤ 2 * ε) ∧
      (∀ u ∈ A, u ∉ O ∪ F → ∀ v ∈ A, v ∉ O ∪ F → G.Adj u v →
        ‖g u v - (q v - q u)‖ ≤ ε) := by
  obtain ⟨hsum, hO, hF⟩ := birth_rows O F hdis C a b
  refine local_weighted hSA hcl g ε hε hrev htri p (birthCost O C) hfit
    (birthWeight O a b) (fun t ht => ?_) (hsum.trans hmass) 2 ?_
  · simp only [birthWeight]
    split_ifs <;> assumption
  · intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · rw [hO i hi]; exact hold (Finset.card_pos.mpr ⟨i, hi⟩)
    · rw [hF i hi]; exact hfresh

/-- The full information a bag keeps from its own attachment. -/
def BirthFit (g : V → V → E) (ε : ℝ) (A : Set V) (S : Finset V) (p : V → E) : Prop :=
  (∀ u ∈ A, ∀ v ∈ A, G.Adj u v → ‖g u v - (p v - p u)‖ ≤ 2 * ε) ∧
  (∀ u ∈ A, u ∉ S → ∀ v ∈ A, v ∉ S → G.Adj u v →
    ‖g u v - (p v - p u)‖ ≤ ε) ∧
  (S.card ≤ 2 → ∀ i ∈ S, ∀ v ∈ A, v ∉ S →
    ‖g i v - (p v - p i)‖ ≤ (3/2) * ε)

theorem finish_attachment {S : Finset V} {A : Set V}
    (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε) (hrev : ∀ i j, g j i = -g i j)
    (p q : V → E)
    (hfit : ∀ u ∈ S, ∀ v ∈ S, G.Adj u v → ‖g u v - (p v - p u)‖ ≤ 2 * ε)
    (heq : ∀ i ∈ S, q i = p i) (B : ℝ) (hB : B ≤ 2)
    (hsmall : S.card ≤ 2 → B ≤ 3/2)
    (hmix : ∀ i ∈ S, ∀ v ∈ A, v ∉ S → ‖g i v - (q v - q i)‖ ≤ B * ε)
    (hnn : ∀ u ∈ A, u ∉ S → ∀ v ∈ A, v ∉ S → G.Adj u v →
      ‖g u v - (q v - q u)‖ ≤ ε) : BirthFit (G := G) g ε A S q := by
  refine ⟨?_, hnn, fun hs i hi v hv hvs =>
    (hmix i hi v hv hvs).trans (mul_le_mul_of_nonneg_right (hsmall hs) hε)⟩
  intro u hu v hv huv
  by_cases hus : u ∈ S
  · by_cases hvs : v ∈ S
    · simpa only [heq u hus, heq v hvs] using hfit u hus v hvs huv
    · exact (hmix u hus v hv hvs).trans (mul_le_mul_of_nonneg_right hB hε)
  · by_cases hvs : v ∈ S
    · rw [← fit_reverse g hrev q u v]
      exact (hmix v hvs u hu hus).trans (mul_le_mul_of_nonneg_right hB hε)
    · exact (hnn u hu hus v hv hvs huv).trans (by linarith)

theorem local_uniform {S : Finset V} {A : Set V} (hS : S.Nonempty)
    (hSA : (S : Set V) ⊆ A) (hcl : G.IsClique A)
    (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε)
    (hrev : ∀ i j, g j i = -g i j) (htri : TriangleFlat G g ε)
    (p : V → E) (R : ℝ) (hR : 0 ≤ R)
    (hfit : ∀ i ∈ S, ∀ j ∈ S, G.Adj i j → ‖g i j - (p j - p i)‖ ≤ R * ε)
    (m : ℕ) (hm : S.card ≤ m) :
    ∃ q : V → E, (∀ i ∈ S, q i = p i) ∧
      (∀ i ∈ S, ∀ v ∈ A, v ∉ S →
        ‖g i v - (q v - q i)‖ ≤ ((1 - 1 / (m : ℝ)) * (1 + R)) * ε) ∧
      (∀ u ∈ A, u ∉ S → ∀ v ∈ A, v ∉ S → G.Adj u v →
        ‖g u v - (q v - q u)‖ ≤ ε) := by
  have hc : ∀ v ∈ A, ∃ c : E, ∀ i ∈ S, ‖p i + g i v - c‖ ≤ 1 * ((1 + R) * ε) := by
    intro v hv
    obtain ⟨a, ha⟩ := hS
    refine ⟨p a + g a v, ?_⟩
    intro i hi
    simpa only [one_mul] using
      (candidate_diameter hSA hcl g ε hε hrev htri p R hR hfit hv i hi a ha)
  simpa using local_blend hS hSA hcl g ε hε hrev htri p R hR hfit m hm 1 0
    (by norm_num) (by norm_num) hc

theorem birth_empty {S : Finset V} {A : Set V} (hS : ¬ S.Nonempty)
    (hcl : G.IsClique A) (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε)
    (hrev : ∀ i j, g j i = -g i j) (htri : TriangleFlat G g ε) (p : V → E) :
    ∃ q : V → E, (∀ i ∈ S, q i = p i) ∧ BirthFit (G := G) g ε A S q := by
  obtain ⟨q, heq, hfit⟩ := extend_empty hS hcl g ε hε hrev htri p 1 (by norm_num)
  refine ⟨q, heq, ?_, ?_, ?_⟩
  · intro u hu v hv huv; have := hfit u hu v hv huv; linarith
  · intro u hu hus v hv hvs huv; simpa using hfit u hu v hv huv
  · intro hs i hi; exact (hS ⟨i, hi⟩).elim

theorem birth_small {S : Finset V} {A : Set V} (hm : S.card ≤ 3)
    (hSA : (S : Set V) ⊆ A) (hcl : G.IsClique A)
    (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε)
    (hrev : ∀ i j, g j i = -g i j) (htri : TriangleFlat G g ε) (p : V → E)
    (hfit : ∀ i ∈ S, ∀ j ∈ S, G.Adj i j → ‖g i j - (p j - p i)‖ ≤ 2 * ε) :
    ∃ q : V → E, (∀ i ∈ S, q i = p i) ∧ BirthFit (G := G) g ε A S q := by
  by_cases hS : S.Nonempty
  · by_cases hs : S.card ≤ 2
    · obtain ⟨q, heq, hmix, hnn⟩ := local_uniform hS hSA hcl g ε hε hrev htri p 2
        (by norm_num) hfit 2 hs
      exact ⟨q, heq, finish_attachment g ε hε hrev p q hfit heq _ (by norm_num)
        (by norm_num) hmix hnn⟩
    · obtain ⟨q, heq, hmix, hnn⟩ := local_uniform hS hSA hcl g ε hε hrev htri p 2
        (by norm_num) hfit 3 hm
      exact ⟨q, heq, finish_attachment g ε hε hrev p q hfit heq _ (by norm_num)
        (fun h => (hs h).elim) hmix hnn⟩
  · exact birth_empty hS hcl g ε hε hrev htri p

/-- An arbitrary separator attached directly to a root bag whose errors are at most epsilon. -/
theorem birth_root {S : Finset V} {A : Set V}
    (hSA : (S : Set V) ⊆ A) (hcl : G.IsClique A)
    (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε)
    (hrev : ∀ i j, g j i = -g i j) (htri : TriangleFlat G g ε) (p : V → E)
    (hfit : ∀ i ∈ S, ∀ j ∈ S, G.Adj i j → ‖g i j - (p j - p i)‖ ≤ ε) :
    ∃ q : V → E, (∀ i ∈ S, q i = p i) ∧ BirthFit (G := G) g ε A S q := by
  have hfit2 : ∀ i ∈ S, ∀ j ∈ S, G.Adj i j → ‖g i j - (p j - p i)‖ ≤ 2 * ε := by
    intro i hi j hj hij; exact (hfit i hi j hj hij).trans (by linarith)
  by_cases hm : S.card ≤ 3
  · exact birth_small hm hSA hcl g ε hε hrev htri p hfit2
  · have hS : S.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨q, heq, hmix, hnn⟩ := local_uniform hS hSA hcl g ε hε hrev htri p 1
      (by norm_num) (by simpa using hfit) S.card (le_refl _)
    refine ⟨q, heq, finish_attachment g ε hε hrev p q hfit2 heq _ ?_ ?_ hmix hnn⟩
    · have : 0 ≤ 1 / (S.card : ℝ) := by positivity
      linarith
    · intro hs; omega

/-- Reading a parent's retained birth types on the next separator. -/
theorem birth_cost_fit [DecidableEq V] {S U : Finset V} {P : Set V}
    (hSP : (S : Set V) ⊆ P) (g : V → V → E) (ε : ℝ)
    (hrev : ∀ i j, g j i = -g i j) (p : V → E)
    (hp : BirthFit (G := G) g ε P U p) (C : ℝ)
    (hmix : ∀ i ∈ S, i ∈ U → ∀ v ∈ S, v ∉ U → G.Adj i v →
      ‖g i v - (p v - p i)‖ ≤ C * ε) :
    ∀ i ∈ S, ∀ j ∈ S, G.Adj i j →
      ‖g i j - (p j - p i)‖ ≤ birthCost (S ∩ U) C i j * ε := by
  intro i hi j hj hij
  by_cases hiU : i ∈ U
  · by_cases hjU : j ∈ U
    · simpa [birthCost, hi, hj, hiU, hjU] using hp.1 i (hSP hi) j (hSP hj) hij
    · simpa [birthCost, hi, hj, hiU, hjU] using hmix i hi hiU j hj hjU hij
  · by_cases hjU : j ∈ U
    · rw [← fit_reverse g hrev p i j]
      simpa [birthCost, hi, hj, hiU, hjU] using hmix j hj hjU i hi hiU hij.symm
    · simpa [birthCost, hi, hj, hiU, hjU] using hp.2.1 i (hSP hi) hiU j (hSP hj) hjU hij

/-- Both large-separator rules, including zero, one, or two inherited anchors. -/
theorem birth_large [DecidableEq V] {S U : Finset V} {P A : Set V}
    (hSP : (S : Set V) ⊆ P) (hSA : (S : Set V) ⊆ A) (hcl : G.IsClique A)
    (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε)
    (hrev : ∀ i j, g j i = -g i j) (htri : TriangleFlat G g ε) (p : V → E)
    (hp : BirthFit (G := G) g ε P U p)
    (hcase : (4 ≤ S.card ∧ S.card ≤ 6 ∧ U.card ≤ 2) ∨
      (4 ≤ S.card ∧ S.card ≤ 5 ∧ (S ∩ U).card ≤ 1)) :
    ∃ q : V → E, (∀ i ∈ S, q i = p i) ∧ BirthFit (G := G) g ε A S q := by
  classical
  let O := S ∩ U
  let F := S \ U
  have hdis : Disjoint O F := by
    apply Finset.disjoint_left.mpr
    intro t ht htf
    exact (Finset.mem_sdiff.mp htf).2 (Finset.mem_inter.mp ht).2
  have heq : O ∪ F = S := by ext t; simp [O, F]; tauto
  have hcard : O.card + F.card = S.card := by rw [← Finset.card_union_of_disjoint hdis, heq]
  have hglob : ∀ i ∈ S, ∀ j ∈ S, G.Adj i j → ‖g i j - (p j - p i)‖ ≤ 2 * ε :=
    fun i hi j hj hij => hp.1 i (hSP hi) j (hSP hj) hij
  have finish (C a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
      (hmass : (O.card : ℝ) * a + F.card * b = 1)
      (hold : 0 < O.card → ((O.card : ℝ) - 1) * a * 3 + F.card * b * (1 + C) ≤ 2)
      (hfresh : (O.card : ℝ) * a * (1 + C) + ((F.card : ℝ) - 1) * b * 2 ≤ 2)
      (hcost : ∀ i ∈ S, ∀ j ∈ S, G.Adj i j →
        ‖g i j - (p j - p i)‖ ≤ birthCost O C i j * ε) (hbig : 4 ≤ S.card) :
      ∃ q : V → E, (∀ i ∈ S, q i = p i) ∧ BirthFit (G := G) g ε A S q := by
    obtain ⟨q, hq, hmix, hnn⟩ := partition_extension O F hdis (by simpa only [heq] using hSA)
      hcl g ε hε hrev htri p C a b (by simpa only [heq] using hcost) ha hb hmass hold hfresh
    rw [heq] at hq hmix hnn
    exact ⟨q, hq, finish_attachment g ε hε hrev p q hglob hq 2 (le_refl _)
      (fun hs => by omega) hmix hnn⟩
  rcases hcase with ⟨hlo, hhi, hU⟩ | ⟨hlo, hhi, hO⟩
  · have hO : O.card ≤ 2 := (Finset.card_le_card Finset.inter_subset_right).trans hU
    obtain ⟨ha, hb, hmass, hold, hfresh⟩ := following_small_numbers O.card F.card hO
      (by omega) (by omega)
    refine finish (3/2) (1/4) ((1 - (O.card : ℝ) / 4) / F.card) ha hb hmass hold hfresh ?_ hlo
    exact birth_cost_fit hSP g ε hrev p hp (3/2)
      (fun i hi hiU v hv hvU _ => hp.2.2 hU i hiU v (hSP hv) hvU)
  · obtain ⟨ha, hb, hmass, hold, hfresh⟩ := overlap_one_numbers O.card F.card hO
      (by omega) (by omega)
    refine finish 2 (1/3) ((1 - (O.card : ℝ) / 3) / F.card) ha hb hmass hold hfresh ?_ hlo
    exact birth_cost_fit hSP g ε hrev p hp 2
      (fun i hi _ v hv _ hij => hp.1 i (hSP hi) v (hSP hv) hij)

omit [SeminormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Layer induction for a full bag property. Earlier sections are kept literally
unchanged, preserving every earlier bag's birth-type estimates. -/
theorem property_layers (P : I → (V → E) → Prop)
    (d : I → ℕ) (parent : I → I)
    (hpar : ∀ a, 0 < d a → T.Adj (parent a) a ∧ d a = d (parent a) + 1)
    (hedge : ∀ a b, T.Adj a b →
      parent b = a ∧ d b = d a + 1 ∨ parent a = b ∧ d a = d b + 1)
    (hstep : ∀ a, 0 < d a → ∀ p : V → E, P (parent a) p →
      ∃ q : V → E, (∀ x ∈ K (parent a) ∩ K a, q x = p x) ∧ P a q)
    (p₀ : V → E) (hinit : ∀ a, d a = 0 → P a p₀)
    (n : ℕ) (hn : ∀ a, d a ≤ n) :
    ∃ p : I → V → E, (∀ a, P a (p a)) ∧
      (∀ a b, T.Adj a b → ∀ x ∈ K a ∩ K b, p a x = p b x) := by
  classical
  have layers (j : ℕ) : ∃ p : I → V → E,
      (∀ a, d a ≤ j → P a (p a)) ∧
      (∀ a b, T.Adj a b → d a ≤ j → d b ≤ j →
        ∀ x ∈ K a ∩ K b, p a x = p b x) := by
    induction j with
    | zero =>
      exact ⟨fun _ => p₀, fun a ha => hinit a (Nat.eq_zero_of_le_zero ha), by simp⟩
    | succ j ih =>
      obtain ⟨p, hp, hag⟩ := ih
      have next (a : I) (ha : d a = j + 1) : ∃ q : V → E,
          (∀ x ∈ K (parent a) ∩ K a, q x = p (parent a) x) ∧ P a q := by
        obtain ⟨hadj, hdepth⟩ := hpar a (by omega)
        exact hstep a (by omega) (p (parent a)) (hp _ (by omega))
      let q (a : I) := if ha : d a = j + 1 then (next a ha).choose else p a
      have old (a : I) (ha : d a ≤ j) : q a = p a := dite_eq_right (by omega)
      have fresh (a : I) (ha : d a = j + 1) : q a = (next a ha).choose := dite_eq_left ha
      have agree (a b : I) (hab : T.Adj a b) (hb : d b ≤ j + 1)
          (hpar : parent b = a) (hdep : d b = d a + 1) (x : V) (hx : x ∈ K a ∩ K b) :
          q a x = q b x := by
        rw [old a (by omega)]
        by_cases h : d b ≤ j
        · rw [old b h]
          exact hag a b hab (by omega) h x hx
        · have hd : d b = j + 1 := by omega
          rw [fresh b hd]
          simpa only [hpar] using ((next b hd).choose_spec.1 x (hpar.symm ▸ hx)).symm
      refine ⟨q, fun a ha => ?_, fun a b hab ha hb x hx => ?_⟩
      · by_cases h : d a ≤ j
        · rw [old a h]; exact hp a h
        · have hd : d a = j + 1 := by omega
          rw [fresh a hd]; exact (next a hd).choose_spec.2
      · rcases hedge a b hab with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩
        · exact agree a b hab hb h₀ h₁ x hx
        · exact (agree b a hab.symm ha h₀ h₁ x ⟨hx.2, hx.1⟩).symm
  obtain ⟨p, hp, hag⟩ := layers n
  exact ⟨p, fun a => hp a (hn a), fun a b hab => hag a b hab (hn a) (hn b)⟩

/-- The root has no inherited vertices. Other bags inherit their parent intersection. -/
noncomputable def incoming [Finite V] (K : I → Set V) (r : I) (parent : I → I) (a : I) : Finset V := by
  classical
  exact if a = r then ∅ else bag (K (parent a) ∩ K a)

/-- The four allowed attachment cases. The root-attachment case has no size bound. -/
noncomputable def Allowed [Finite V] (K : I → Set V) (r : I) (parent : I → I) (a : I) : Prop := by
  classical
  let S := bag (K (parent a) ∩ K a)
  let U := incoming K r parent (parent a)
  exact parent a = r ∨ S.card ≤ 3 ∨
    (4 ≤ S.card ∧ S.card ≤ 6 ∧ U.card ≤ 2) ∨
    (4 ≤ S.card ∧ S.card ≤ 5 ∧ (S ∩ U).card ≤ 1)

/-- Global bound two for a rooted clique tree satisfying the four attachment rules.
The target may be any real seminormed vector space; completeness is unnecessary. -/
theorem rooted_banach_two [Finite V] [Finite I] (hK : IsCliqueTree T G K)
    (r : I) (parent : I → I)
    (hpar : ∀ a, 0 < T.dist r a →
      T.Adj (parent a) a ∧ T.dist r a = T.dist r (parent a) + 1)
    (hedge : ∀ a b, T.Adj a b →
      parent b = a ∧ T.dist r b = T.dist r a + 1 ∨
      parent a = b ∧ T.dist r a = T.dist r b + 1)
    (hsep : ∀ a, a ≠ r → Allowed K r parent a)
    (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε)
    (hrev : ∀ i j, g j i = -g i j) (htri : TriangleFlat G g ε) :
    ∃ φ : V → E, ∀ u v, G.Adj u v → ‖g u v - (φ v - φ u)‖ ≤ 2 * ε := by
  classical
  let := Fintype.ofFinite I
  let P (a : I) (p : V → E) := BirthFit (G := G) g ε (K a) (incoming K r parent a) p
  let p₀ (v : V) : E := if h : (K r).Nonempty then g h.choose v else 0
  have hstep : ∀ a, 0 < T.dist r a → ∀ p : V → E, P (parent a) p →
      ∃ q : V → E, (∀ x ∈ K (parent a) ∩ K a, q x = p x) ∧ P a q := by
    intro a ha p hp
    have hne : a ≠ r := by rintro rfl; simp at ha
    let S := bag (K (parent a) ∩ K a)
    have hSP : (S : Set V) ⊆ K (parent a) := fun x hx => (mem_bag.mp hx).1
    have hSA : (S : Set V) ⊆ K a := fun x hx => (mem_bag.mp hx).2
    have hinc : incoming K r parent a = S := by simp [incoming, hne, S]
    have hp' : BirthFit (G := G) g ε (K (parent a)) (incoming K r parent (parent a)) p := hp
    obtain ⟨q, heq, hq⟩ : ∃ q : V → E, (∀ i ∈ S, q i = p i) ∧
        BirthFit (G := G) g ε (K a) S q := by
      rcases hsep a hne with hroot | hsmall | hlarge | hover
      · apply birth_root hSA (hK.clique a) g ε hε hrev htri p
        intro i hi j hj hij
        exact hp'.2.1 i (hSP hi) (by simp [incoming, hroot])
          j (hSP hj) (by simp [incoming, hroot]) hij
      · exact birth_small hsmall hSA (hK.clique a) g ε hε hrev htri p
          (fun i hi j hj hij => hp'.1 i (hSP hi) j (hSP hj) hij)
      · exact birth_large hSP hSA (hK.clique a) g ε hε hrev htri p hp' (Or.inl hlarge)
      · exact birth_large hSP hSA (hK.clique a) g ε hε hrev htri p hp' (Or.inr hover)
    exact ⟨q, fun x hx => heq x (mem_bag.mpr hx), by simpa only [P, hinc] using hq⟩
  have hinit : ∀ a, T.dist r a = 0 → P a p₀ := by
    intro a ha
    have har : a = r := (hK.isTree.connected.dist_eq_zero_iff.mp ha).symm
    subst a
    have hfit : ∀ u ∈ K r, ∀ v ∈ K r, G.Adj u v →
        ‖g u v - (p₀ v - p₀ u)‖ ≤ ε := by
      intro u hu v hv huv
      have hn : (K r).Nonempty := ⟨u, hu⟩
      simp only [p₀, dite_eq_left hn]
      exact defect_bound g ε hε hrev htri (fun _ => huv)
        (fun h => hK.clique r hn.choose_spec hu h)
        (fun h => hK.clique r hn.choose_spec hv h)
    change BirthFit (G := G) g ε (K r) (incoming K r parent r) p₀
    simp only [incoming, ite_eq_left rfl]
    refine ⟨?_, ?_, ?_⟩
    · intro u hu v hv huv; exact (hfit u hu v hv huv).trans (by linarith)
    · intro u hu hus v hv hvs huv; exact hfit u hu v hv huv
    · intro hs i hi; simp at hi
  obtain ⟨p, hp, hag⟩ := property_layers P (T.dist r) parent hpar hedge hstep p₀ hinit
    (Finset.univ.sup (T.dist r)) (fun a => Finset.le_sup (f := T.dist r) (Finset.mem_univ a))
  obtain ⟨φ, hφ⟩ := glue_equal hK hag
  refine ⟨φ, fun u v huv => ?_⟩
  obtain ⟨a, hu, hv⟩ := hK.edge u v huv
  rw [hφ a u hu, hφ a v hv]
  exact (hp a).1 u hu v hv huv

/-- A parent map obtained from the unique simple root paths. -/
noncomputable def rootParent (hT : T.IsTree) (r : I) : I → I :=
  (rooted_layers hT r).choose

end SimpleGraph.CliqueTreeBanachOverlap

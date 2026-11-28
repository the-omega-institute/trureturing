import OmegaBuild.Commands
import D5.S3.Combinatorics.Graph.Chordal.CliqueTreeBanachPotential
import OmegaMath.Combinatorics.Graph.L1Jung

compile_only_with_mathlib

/-! Omega original.

The mean–Jung interpolation for arbitrary clique bags, and gluing through
running intersection.
-/

open scoped BigOperators
open MeasureTheory
namespace SimpleGraph.CliqueTreeL1Separator
universe u v w
variable {V : Type u} {I : Type w} {G : SimpleGraph V} {T : SimpleGraph I} {K : I → Set V}
variable {E : Type v} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def mean (S : Finset V) (f : V → E) : E :=
  (S.card : ℝ)⁻¹ • ∑ t ∈ S, f t
theorem mean_sub (S : Finset V) (f h : V → E) :
    mean S f - mean S h = mean S (fun t => f t - h t) := by
  simp [mean, Finset.sum_sub_distrib, smul_sub]
theorem const_sub_mean {S : Finset V} (hS : S.Nonempty) (e : E) (f : V → E) :
    e - mean S f = mean S (fun t => e - f t) := by
  have hn : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_ne_zero
  simp [mean, Finset.sum_sub_distrib, smul_sub, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, hn]
theorem mean_bound {S A : Finset V} (hAS : A ⊆ S)
    (f : V → E) (B : ℝ) (hz : ∀ t ∈ S, t ∉ A → f t = 0)
    (hb : ∀ t ∈ A, ‖f t‖ ≤ B) :
    ‖mean S f‖ ≤ ((A.card : ℝ) / S.card) * B := by
  classical
  have hp : 0 ≤ (S.card : ℝ)⁻¹ := by positivity
  have hs : ∑ t ∈ A, f t = ∑ t ∈ S, f t := Finset.sum_subset hAS hz
  rw [mean, ← hs, norm_smul, Real.norm_eq_abs, abs_of_nonneg hp]
  calc
    _ ≤ (S.card : ℝ)⁻¹ * (∑ t ∈ A, ‖f t‖) :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) hp
    _ ≤ (S.card : ℝ)⁻¹ * (∑ _t ∈ A, B) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hb) hp
    _ = _ := by simp [div_eq_mul_inv]; ring
theorem full_mean_bound {S : Finset V} (hS : S.Nonempty) {f : V → E} {B : ℝ}
    (hb : ∀ t ∈ S, ‖f t‖ ≤ B) : ‖mean S f‖ ≤ 1 * B := by
  have hn : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_ne_zero
  simpa only [div_self hn] using mean_bound (fun _ h => h : S ⊆ S) f B
    (fun _ ht hnt => (hnt ht).elim) hb
theorem diag_zero (g : V → V → E) (hrev : ∀ i j, g j i = -g i j)
    (x : V) : g x x = 0 := by
  have hz : (2 : ℝ) • g x x = 0 := by rw [two_smul, eq_neg_iff_add_eq_zero.mp (hrev x x)]
  calc
    g x x = (1 / 2 : ℝ) • ((2 : ℝ) • g x x) := by rw [smul_smul]; norm_num
    _ = 0 := by rw [hz, smul_zero]
abbrev TriangleFlat (G : SimpleGraph V) (g : V → V → E) (ε : ℝ) :=
  ∀ i j l, G.Adj i j → G.Adj j l → G.Adj i l → ‖g i j + g j l - g i l‖ ≤ ε
theorem defect_bound (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε)
    (hrev : ∀ i j, g j i = -g i j)
    (htri : TriangleFlat G g ε)
    {u v t : V} (huv : u ≠ v → G.Adj u v) (htu : t ≠ u → G.Adj t u)
    (htv : t ≠ v → G.Adj t v) : ‖g u v - (g t v - g t u)‖ ≤ ε := by
  by_cases h : u = v
  · subst v
    simpa [diag_zero g hrev] using hε
  by_cases hu : t = u
  · subst t
    simpa [diag_zero g hrev] using hε
  by_cases hv : t = v
  · subst t
    simpa [diag_zero g hrev, hrev u v] using hε
  convert htri t u v (htu hu) (huv h) (htv hv) using 1
  abel
noncomputable def bag [Finite V] (S : Set V) : Finset V :=
  S.toFinite.toFinset
@[simp] theorem mem_bag [Finite V] {x : V} {S : Set V} : x ∈ bag S ↔ x ∈ S := by
  simp [bag]
@[simp] theorem card_bag [Finite V] (S : Set V) : (bag S).card = S.ncard := by
  exact (Set.ncard_eq_toFinset_card S S.toFinite).symm
theorem erase_fraction [DecidableEq V] {S : Finset V} {u : V} (hu : u ∈ S) :
    ((S.erase u).card : ℝ) / S.card = 1 - 1 / (S.card : ℝ) := by
  have hn : (S.card : ℝ) ≠ 0 := by exact_mod_cast (show S.Nonempty from ⟨u, hu⟩).card_ne_zero
  have hc : ((S.erase u).card : ℝ) + 1 = S.card := by exact_mod_cast Finset.card_erase_add_one hu
  field_simp
  linarith
omit [NormedSpace ℝ E] in
theorem fit_reverse (g : V → V → E) (hrev : ∀ i j, g j i = -g i j)
    (p : V → E) (u v : V) :
    ‖g v u - (p u - p v)‖ = ‖g u v - (p v - p u)‖ := by
  rw [hrev u v, show -g u v - (p u - p v) = -(g u v - (p v - p u)) by abel, norm_neg]

/-- A mean is within `(1-1/m)D` of every one of at most `m` points. -/
theorem mean_radius {S : Finset V} (hS : S.Nonempty) (m : ℕ) (hm : S.card ≤ m)
    (x : V → E) (D : ℝ) (hD : 0 ≤ D)
    (hd : ∀ i ∈ S, ∀ j ∈ S, ‖x i - x j‖ ≤ D) {i : V} (hi : i ∈ S) :
    ‖x i - mean S x‖ ≤ (1 - 1 / (m : ℝ)) * D := by
  classical
  have hpos : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hmR : (S.card : ℝ) ≤ m := by exact_mod_cast hm
  rw [const_sub_mean hS]
  calc
    _ ≤ (((S.erase i).card : ℝ) / S.card) * D := by
      apply mean_bound (Finset.erase_subset _ _)
      · intro t ht hn
        have : t = i := by simpa [ht] using hn
        subst t
        exact sub_self _
      · intro t ht
        exact hd i hi t (Finset.mem_of_mem_erase ht)
    _ ≤ _ := by
      rw [erase_fraction hi]
      exact mul_le_mul_of_nonneg_right
        (by linarith [one_div_le_one_div_of_le hpos hmR]) hD

/-- Diameter of the separator candidates, including coincident anchors. -/
theorem candidate_diameter {S : Finset V} {A : Set V}
    (hSA : (S : Set V) ⊆ A) (hcl : G.IsClique A)
    (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε)
    (hrev : ∀ i j, g j i = -g i j) (htri : TriangleFlat G g ε)
    (p : V → E) (R : ℝ) (hR : 0 ≤ R)
    (hfit : ∀ i ∈ S, ∀ j ∈ S, G.Adj i j → ‖g i j - (p j - p i)‖ ≤ R * ε)
    {v : V} (hv : v ∈ A) :
    ∀ i ∈ S, ∀ j ∈ S,
      ‖(p i + g i v) - (p j + g j v)‖ ≤ (1 + R) * ε := by
  intro i hi j hj
  by_cases he : i = j
  · subst j
    simpa using mul_nonneg (show 0 ≤ 1 + R by linarith) hε
  have hij := hcl (hSA hi) (hSA hj) he
  have hd := defect_bound g ε hε hrev htri (fun _ => hij)
    (fun hn => hcl hv (hSA hi) hn) (fun hn => hcl hv (hSA hj) hn)
  rw [show (p i + g i v) - (p j + g j v) =
      (g i j - (p j - p i)) - (g i j - (g v j - g v i)) by
        rw [hrev i v, hrev j v]; abel]
  exact (norm_sub_le _ _).trans (by linarith [hfit i hi j hj hij])

/-- Sharp simultaneous interpolation estimates. Each fresh vertex has an independent
center; the new--new estimate uses any common old anchor. -/
theorem local_blend {S : Finset V} {A : Set V} (hS : S.Nonempty)
    (hSA : (S : Set V) ⊆ A) (hcl : G.IsClique A)
    (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε)
    (hrev : ∀ i j, g j i = -g i j) (htri : TriangleFlat G g ε)
    (p : V → E) (R : ℝ) (hR : 0 ≤ R)
    (hfit : ∀ i ∈ S, ∀ j ∈ S, G.Adj i j → ‖g i j - (p j - p i)‖ ≤ R * ε)
    (m : ℕ) (hm : S.card ≤ m) (J t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hc : ∀ v ∈ A, ∃ c : E, ∀ i ∈ S, ‖p i + g i v - c‖ ≤ J * ((1 + R) * ε)) :
    ∃ q : V → E, (∀ i ∈ S, q i = p i) ∧
      (∀ i ∈ S, ∀ v ∈ A, v ∉ S →
        ‖g i v - (q v - q i)‖ ≤
          ((1 - t) * (1 - 1 / (m : ℝ)) + t * J) * (1 + R) * ε) ∧
      (∀ u ∈ A, u ∉ S → ∀ v ∈ A, v ∉ S → G.Adj u v →
        ‖g u v - (q v - q u)‖ ≤ (1 + 2 * t * J * (1 + R)) * ε) := by
  classical
  let b (v : V) := mean S (fun i => p i + g i v)
  let c (v : V) := if hv : v ∈ A then (hc v hv).choose else b v
  have center (v : V) (hv : v ∈ A) (i : V) (hi : i ∈ S) :
      ‖p i + g i v - c v‖ ≤ J * ((1 + R) * ε) := by
    simpa only [c, dite_eq_left hv] using (hc v hv).choose_spec i hi
  let q (v : V) := if v ∈ S then p v else (1 - t) • b v + t • c v
  refine ⟨q, fun i hi => by simp [q, hi], ?_, ?_⟩
  · intro i hi v hv hvs
    have hb : ‖(p i + g i v) - b v‖ ≤ (1 - 1 / (m : ℝ)) * ((1 + R) * ε) :=
      mean_radius hS m hm _ _ (mul_nonneg (by linarith) hε)
        (candidate_diameter hSA hcl g ε hε hrev htri p R hR hfit hv) hi
    rw [show g i v - (q v - q i) =
        (1 - t) • ((p i + g i v) - b v) + t • ((p i + g i v) - c v) by
          simp only [q, ite_eq_left hi, ite_eq_right hvs]; module]
    calc
      _ ≤ ‖(1 - t) • ((p i + g i v) - b v)‖ +
          ‖t • ((p i + g i v) - c v)‖ := norm_add_le _ _
      _ ≤ (1 - t) * ((1 - 1 / (m : ℝ)) * ((1 + R) * ε)) +
          t * (J * ((1 + R) * ε)) := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (by linarith : 0 ≤ 1 - t), abs_of_nonneg ht]
        exact add_le_add (mul_le_mul_of_nonneg_left hb (by linarith))
          (mul_le_mul_of_nonneg_left (center v hv i hi) ht)
      _ = _ := by ring
  · intro u hu hus v hv hvs huv
    have base : ‖g u v - (b v - b u)‖ ≤ ε := by
      rw [show g u v - (b v - b u) =
          mean S (fun i => g u v - (g i v - g i u)) by
            dsimp [b]; rw [mean_sub, const_sub_mean hS]; congr 1; funext i; abel]
      simpa only [one_mul] using full_mean_bound hS (fun i hi =>
        defect_bound g ε hε hrev htri (fun _ => huv)
          (fun hn => hcl (hSA hi) hu hn) (fun hn => hcl (hSA hi) hv hn))
    obtain ⟨a, ha⟩ := hS
    have jung : ‖g u v - (c v - c u)‖ ≤ ε + 2 * (J * ((1 + R) * ε)) := by
      rw [show g u v - (c v - c u) =
          (g u v - (g a v - g a u)) +
            ((p a + g a v - c v) - (p a + g a u - c u)) by abel]
      have hd := defect_bound g ε hε hrev htri (fun _ => huv)
        (fun hn => hcl (hSA ha) hu hn) (fun hn => hcl (hSA ha) hv hn)
      exact (norm_add_le _ _).trans (by
        have hs := (norm_sub_le _ _).trans
          (add_le_add (center v hv a ha) (center u hu a ha))
        linarith)
    rw [show g u v - (q v - q u) =
        (1 - t) • (g u v - (b v - b u)) + t • (g u v - (c v - c u)) by
          simp only [q, ite_eq_right hus, ite_eq_right hvs]; module]
    calc
      _ ≤ ‖(1 - t) • (g u v - (b v - b u))‖ +
          ‖t • (g u v - (c v - c u))‖ := norm_add_le _ _
      _ ≤ (1 - t) * ε + t * (ε + 2 * (J * ((1 + R) * ε))) := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (by linarith : 0 ≤ 1 - t), abs_of_nonneg ht]
        exact add_le_add (mul_le_mul_of_nonneg_left base (by linarith))
          (mul_le_mul_of_nonneg_left jung ht)
      _ = _ := by ring

/-- A numerical invariant closes one clique attachment with the blend. -/
theorem extend_blend {S : Finset V} {A : Set V} (hS : S.Nonempty)
    (hSA : (S : Set V) ⊆ A) (hcl : G.IsClique A)
    (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε)
    (hrev : ∀ i j, g j i = -g i j) (htri : TriangleFlat G g ε)
    (p : V → E) (R : ℝ) (hR : 0 ≤ R)
    (hfit : ∀ i ∈ S, ∀ j ∈ S, G.Adj i j → ‖g i j - (p j - p i)‖ ≤ R * ε)
    (m : ℕ) (hm : S.card ≤ m) (J t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hc : ∀ v ∈ A, ∃ c : E, ∀ i ∈ S, ‖p i + g i v - c‖ ≤ J * ((1 + R) * ε))
    (hcross : ((1 - t) * (1 - 1 / (m : ℝ)) + t * J) * (1 + R) ≤ R)
    (hnew : 1 + 2 * t * J * (1 + R) ≤ R) :
    ∃ q : V → E, (∀ i ∈ S, q i = p i) ∧
      ∀ u ∈ A, ∀ v ∈ A, G.Adj u v → ‖g u v - (q v - q u)‖ ≤ R * ε := by
  obtain ⟨q, hq, hmix, hnn⟩ := local_blend hS hSA hcl g ε hε hrev htri p R hR hfit m hm J t ht ht1 hc
  refine ⟨q, hq, fun u hu v hv huv => ?_⟩
  by_cases hus : u ∈ S
  · by_cases hvs : v ∈ S
    · simpa only [hq u hus, hq v hvs] using hfit u hus v hvs huv
    · exact (hmix u hus v hv hvs).trans (by
        exact mul_le_mul_of_nonneg_right hcross hε)
  · by_cases hvs : v ∈ S
    · rw [← fit_reverse g hrev q u v]
      exact (hmix v hvs u hu hus).trans (by
        exact mul_le_mul_of_nonneg_right hcross hε)
    · exact (hnn u hu hus v hv hvs huv).trans (mul_le_mul_of_nonneg_right hnew hε)


/-- The four separator invariants. -/
noncomputable def coefficient (q : ℕ) : ℝ :=
  if q = 2 then 1 else if q = 3 then 5 / 3 else if q = 4 then 3 else 25 / 7

/-- Empty separators start an independent clique at error at most epsilon. -/
theorem extend_empty {S : Finset V} {A : Set V} (hS : ¬ S.Nonempty)
    (hcl : G.IsClique A) (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε)
    (hrev : ∀ i j, g j i = -g i j) (htri : TriangleFlat G g ε)
    (p : V → E) (R : ℝ) (hR : 1 ≤ R) :
    ∃ q : V → E, (∀ i ∈ S, q i = p i) ∧
      ∀ u ∈ A, ∀ v ∈ A, G.Adj u v → ‖g u v - (q v - q u)‖ ≤ R * ε := by
  classical
  by_cases hA : A.Nonempty
  · obtain ⟨a, ha⟩ := hA
    refine ⟨fun v => g a v, fun i hi => (hS ⟨i, hi⟩).elim, fun u hu v hv huv => ?_⟩
    exact (defect_bound g ε hε hrev htri (fun _ => huv)
      (fun hn => hcl ha hu hn) (fun hn => hcl ha hv hn)).trans
        (by simpa using mul_le_mul_of_nonneg_right hR hε)
  · exact ⟨p, fun _ _ => rfl, fun u hu => (hA ⟨u, hu⟩).elim⟩

/-- Mean-only invariant, independent of target geometry and bag cardinality. -/
theorem extend_mean_invariant {S : Finset V} {A : Set V} (hS : S.Nonempty)
    (hSA : (S : Set V) ⊆ A) (hcl : G.IsClique A)
    (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε)
    (hrev : ∀ i j, g j i = -g i j) (htri : TriangleFlat G g ε)
    (p : V → E) (R : ℝ) (hR : 1 ≤ R)
    (hfit : ∀ i ∈ S, ∀ j ∈ S, G.Adj i j → ‖g i j - (p j - p i)‖ ≤ R * ε)
    (m : ℕ) (hm : S.card ≤ m) (hinv : (1 - 1 / (m : ℝ)) * (1 + R) ≤ R) :
    ∃ q : V → E, (∀ i ∈ S, q i = p i) ∧
      ∀ u ∈ A, ∀ v ∈ A, G.Adj u v → ‖g u v - (q v - q u)‖ ≤ R * ε := by
  have hR0 : 0 ≤ R := by linarith
  refine extend_blend hS hSA hcl g ε hε hrev htri p R hR0 hfit m hm 1 0
    (by norm_num) (by norm_num) ?_ (by simpa using hinv) (by simpa using hR)
  intro v hv
  obtain ⟨a, ha⟩ := hS
  exact ⟨p a + g a v, fun i hi => by
    simpa only [one_mul] using
      candidate_diameter hSA hcl g ε hε hrev htri p R hR0 hfit hv i hi a ha⟩

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Closed L1 centers give the exact three- and five-anchor interpolation parameters. -/
theorem extend_small_separator {S : Finset V} {A : Set V}
    (hSA : (S : Set V) ⊆ A) (hcl : G.IsClique A)
    (q : ℕ) (hq : q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5) (hm : S.card ≤ q)
    (g : V → V → Lp ℝ 1 μ) (ε : ℝ) (hε : 0 ≤ ε)
    (hrev : ∀ i j, g j i = -g i j) (htri : TriangleFlat G g ε)
    (p : V → Lp ℝ 1 μ)
    (hfit : ∀ i ∈ S, ∀ j ∈ S, G.Adj i j →
      ‖g i j - (p j - p i)‖ ≤ coefficient q * ε) :
    ∃ p' : V → Lp ℝ 1 μ, (∀ i ∈ S, p' i = p i) ∧
      ∀ u ∈ A, ∀ v ∈ A, G.Adj u v →
        ‖g u v - (p' v - p' u)‖ ≤ coefficient q * ε := by
  classical
  have hR : 1 ≤ coefficient q := by rcases hq with rfl | rfl | rfl | rfl <;> norm_num [coefficient]
  by_cases hS : S.Nonempty
  · rcases hq with rfl | rfl | rfl | rfl
    · exact extend_mean_invariant hS hSA hcl g ε hε hrev htri p _ hR hfit 2 hm (by norm_num [coefficient])
    · refine extend_blend hS hSA hcl g ε hε hrev htri p _ (by norm_num [coefficient]) hfit
        3 hm (1/2) (1/4) (by norm_num) (by norm_num) ?_
        (by norm_num [coefficient]) (by norm_num [coefficient])
      intro v hv
      obtain ⟨c, hc⟩ := ChordalL1.exists_center_finset_odd 1 (by decide) S
        (fun i => p i + g i v) (mul_nonneg (by norm_num [coefficient]) hε)
        (by simpa using hm)
        (candidate_diameter hSA hcl g ε hε hrev htri p _ (by norm_num [coefficient]) hfit hv)
      exact ⟨c, fun i hi => by convert hc i hi using 1; norm_num⟩
    · exact extend_mean_invariant hS hSA hcl g ε hε hrev htri p _ hR hfit 4 hm (by norm_num [coefficient])
    · refine extend_blend hS hSA hcl g ε hε hrev htri p _ (by norm_num [coefficient]) hfit
        5 hm (3/4) (3/8) (by norm_num) (by norm_num) ?_
        (by norm_num [coefficient]) (by norm_num [coefficient])
      intro v hv
      obtain ⟨c, hc⟩ := ChordalL1.exists_center_finset_odd 2 (by decide) S
        (fun i => p i + g i v) (mul_nonneg (by norm_num [coefficient]) hε)
        (by simpa using hm)
        (candidate_diameter hSA hcl g ε hε hrev htri p _ (by norm_num [coefficient]) hfit hv)
      exact ⟨c, fun i hi => by convert hc i hi using 1; norm_num⟩
  · exact extend_empty hS hcl g ε hε hrev htri p _ hR


omit [SeminormedAddCommGroup E] [NormedSpace ℝ E] in
theorem glue_equal {p : I → V → E} (hK : IsCliqueTree T G K)
    (hag : ∀ a b, T.Adj a b → ∀ x ∈ K a ∩ K b, p a x = p b x) :
    ∃ φ : V → E, ∀ a x, x ∈ K a → φ x = p a x := by
  classical
  have along {a b} (q : T.Walk a b) (x : V) (hx : ∀ c ∈ q.support, x ∈ K c) :
      p a x = p b x := by
    induction q with
    | nil => rfl
    | cons hab q ih =>
      exact (hag _ _ hab x ⟨hx _ (by simp), hx _ (by simp)⟩).trans
        (ih (fun c hc => hx c (by simp [hc])))
  refine ⟨fun x => p (hK.cover x).choose x, fun a x hx => ?_⟩
  obtain ⟨q, hq⟩ := (hK.isTree.existsUnique_path (hK.cover x).choose a).exists
  exact along q x (hK.running q hq x (hK.cover x).choose_spec hx)
noncomputable def route (hT : T.IsTree) (r a : I) : T.Walk r a :=
  (hT.existsUnique_path r a).exists.choose
theorem route_path (hT : T.IsTree) (r a : I) : (route hT r a).IsPath :=
  (hT.existsUnique_path r a).exists.choose_spec
theorem path_eq_route (hT : T.IsTree) {r a : I} {p : T.Walk r a} (hp : p.IsPath) :
    p = route hT r a :=
  Subtype.mk.inj ((hT.isAcyclic.subsingleton_path r a).elim ⟨p, hp⟩ ⟨_, route_path hT r a⟩)
theorem path_length (hT : T.IsTree) {r a : I} {p : T.Walk r a} (hp : p.IsPath) :
    p.length = T.dist r a := by
  obtain ⟨q, hq, hlen⟩ := hT.connected.exists_path_of_dist r a
  rw [path_eq_route hT hp, ← path_eq_route hT hq, hlen]
theorem route_adj (hT : T.IsTree) (r : I) {a b : I} (h : T.Adj a b) :
    route hT r b = (route hT r a).concat h ∨
      route hT r a = (route hT r b).concat h.symm := by
  by_cases ha : a ∈ (route hT r b).support
  · exact Or.inl (hT.isAcyclic.path_concat (route_path ..) (route_path ..) h ha)
  · exact Or.inr (hT.isAcyclic.path_concat (route_path ..) (route_path ..) h.symm
      (hT.isAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath
        (route_path ..) (route_path ..) h ha))


/-- Rooted orientation of a finite clique tree, using its unique simple paths. -/
theorem rooted_layers (hT : T.IsTree) (r : I) :
    ∃ parent : I → I,
      (∀ a, 0 < T.dist r a → T.Adj (parent a) a ∧ T.dist r a = T.dist r (parent a) + 1) ∧
      (∀ a b, T.Adj a b →
        parent b = a ∧ T.dist r b = T.dist r a + 1 ∨
        parent a = b ∧ T.dist r a = T.dist r b + 1) := by
  classical
  let parent (a : I) := (route hT r a).penultimate
  have orient {a b : I} (h : T.Adj a b) (he : route hT r b = (route hT r a).concat h) :
      parent b = a ∧ T.dist r b = T.dist r a + 1 := by
    refine ⟨by simp [parent, he, Walk.penultimate_concat], ?_⟩
    rw [← path_length hT (route_path hT r b), he, Walk.length_concat,
      path_length hT (route_path hT r a)]
  refine ⟨parent, fun a ha => ?_, fun a b hab => ?_⟩
  · have hne : r ≠ a := by rintro rfl; simp at ha
    let p := route hT r a
    have hh := p.adj_penultimate (Walk.not_nil_of_ne hne)
    have hp : p.dropLast.IsPath := (route_path hT r a).dropLast
    have he : route hT r a = (route hT r p.penultimate).concat hh := by
      rw [← path_eq_route hT hp, Walk.concat_dropLast]
    exact ⟨hh, (orient hh he).2⟩
  · exact (route_adj hT r hab).elim (fun he => Or.inl (orient hab he))
      (fun he => Or.inr (orient hab.symm he))

omit [NormedSpace ℝ E] in
/-- Reusable rooted-layer glue: any invariant preserved on a complete attachment
propagates to the whole clique tree. Empty separators are permitted. -/
theorem invariant_layers (hK : IsCliqueTree T G K)
    (g : V → V → E) (ε R : ℝ)
    (hstep : ∀ a b, T.Adj a b → ∀ p : V → E,
      (∀ u ∈ K a ∩ K b, ∀ v ∈ K a ∩ K b, G.Adj u v →
        ‖g u v - (p v - p u)‖ ≤ R * ε) →
      ∃ q : V → E, (∀ x ∈ K a ∩ K b, q x = p x) ∧
        ∀ u ∈ K b, ∀ v ∈ K b, G.Adj u v → ‖g u v - (q v - q u)‖ ≤ R * ε)
    (d : I → ℕ) (parent : I → I)
    (hpar : ∀ a, 0 < d a → T.Adj (parent a) a ∧ d a = d (parent a) + 1)
    (hedge : ∀ a b, T.Adj a b →
      parent b = a ∧ d b = d a + 1 ∨ parent a = b ∧ d a = d b + 1)
    (p₀ : V → E)
    (hinit : ∀ a, d a = 0 → ∀ u ∈ K a, ∀ v ∈ K a, G.Adj u v →
      ‖g u v - (p₀ v - p₀ u)‖ ≤ R * ε)
    (n : ℕ) (hn : ∀ a, d a ≤ n) :
    ∃ φ : V → E, ∀ u v, G.Adj u v → ‖g u v - (φ v - φ u)‖ ≤ R * ε := by
  classical
  have layers (j : ℕ) : ∃ p : I → V → E,
      (∀ a, d a ≤ j → ∀ u ∈ K a, ∀ v ∈ K a, G.Adj u v →
        ‖g u v - (p a v - p a u)‖ ≤ R * ε) ∧
      (∀ a b, T.Adj a b → d a ≤ j → d b ≤ j →
        ∀ x ∈ K a ∩ K b, p a x = p b x) := by
    induction j with
    | zero =>
      exact ⟨fun _ => p₀, fun a ha => hinit a (Nat.eq_zero_of_le_zero ha), by simp⟩
    | succ j ih =>
      obtain ⟨p, hp, hag⟩ := ih
      have next (a : I) (ha : d a = j + 1) : ∃ q : V → E,
          (∀ x ∈ K (parent a) ∩ K a, q x = p (parent a) x) ∧
          (∀ u ∈ K a, ∀ v ∈ K a, G.Adj u v →
            ‖g u v - (q v - q u)‖ ≤ R * ε) := by
        obtain ⟨hadj, hdepth⟩ := hpar a (by omega)
        exact hstep (parent a) a hadj (p (parent a))
          (fun u hu v hv huv => hp _ (by omega) u hu.1 v hv.1 huv)
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
      refine ⟨q, fun a ha u hu v hv huv => ?_, fun a b hab ha hb x hx => ?_⟩
      · by_cases h : d a ≤ j
        · rw [old a h]
          exact hp a h u hu v hv huv
        · have hd : d a = j + 1 := by omega
          rw [fresh a hd]
          exact (next a hd).choose_spec.2 u hu v hv huv
      · rcases hedge a b hab with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩
        · exact agree a b hab hb h₀ h₁ x hx
        · exact (agree b a hab.symm ha h₀ h₁ x ⟨hx.2, hx.1⟩).symm
  obtain ⟨p, hp, hag⟩ := layers n
  obtain ⟨φ, hφ⟩ := glue_equal hK (fun a b hab => hag a b hab (hn a) (hn b))
  refine ⟨φ, fun u v huv => ?_⟩
  obtain ⟨a, hu, hv⟩ := hK.edge u v huv
  rw [hφ a u hu, hφ a v hv]
  exact hp a (hn a) u hu v hv huv

end SimpleGraph.CliqueTreeL1Separator

import OmegaBuild.Commands
import OmegaMath.Combinatorics.Graph.RollingCliqueHistories
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

compile_only_with_mathlib

/-! Omega original.

Potentials on span-one rolling clique graphs, obtained by averaging the full
retained separator at each parent transition.
-/
namespace Omega.RollingCliques.SpanOne
open SimpleGraph
open scoped BigOperators
noncomputable section

abbrev retention (M n : ℕ) (hM : 2 ≤ M) :=
  concreteRetention 1 n M (by omega) (by omega)
abbrev Block (M n k : ℕ) (hM : 2 ≤ M) := History (retention M n hM) k
abbrev Label (M : ℕ) := Fin (M ^ (1 + 2))
abbrev Vertex (M n k : ℕ) (hM : 2 ≤ M) := Block M n k hM × Label M
abbrev graph (M n k : ℕ) (hM : 2 ≤ M) : SimpleGraph (Vertex M n k hM) :=
  rolling (historyData (retention M n hM))

variable {M n k : ℕ} {hM : 2 ≤ M}

def previous (b : Block M n k hM) : Fin (n+1) :=
  ⟨b.stage.val - 1, (Nat.sub_le _ _).trans_lt b.stage.isLt⟩
def parent (b : Block M n k hM) : Block M n k hM :=
  b.prefix (previous b) (Nat.sub_le _ _)
def separator (b : Block M n k hM) : Finset (Label M) :=
  (b.step b.stage).1 (previous b)

theorem parent_lt (b : Block M n k hM) (hb : b.stage.val ≠ 0) :
    (parent b).stage.val < b.stage.val := by
  change b.stage.val - 1 < b.stage.val
  omega

theorem separator_card (b : Block M n k hM) (hb : b.stage.val ≠ 0) :
    (separator b).card = M^2 := by
  rw [separator, b.cardinal _ _ le_rfl]
  change quota 1 M (b.stage.val-1) b.stage.val = M^2
  have hi : b.stage.val ≤ b.stage.val - 1 + 1 := by omega
  have he : 1 + 2 - (b.stage.val - (b.stage.val - 1)) = 2 := by omega
  simp [quota, hi, he]

theorem internal_adj (b : Block M n k hM) {x y : Label M} (hxy : x ≠ y) :
    (graph M n k hM).Adj (b,x) (b,y) :=
  ⟨fun h => hxy (congrArg Prod.snd h), Or.inl rfl⟩

theorem separator_adj (b : Block M n k hM) (hb : b.stage.val ≠ 0)
    {p : Label M} (hp : p ∈ separator b) (x : Label M) :
    (graph M n k hM).Adj (parent b,p) (b,x) := by
  refine ⟨fun h => (parent_lt b hb).ne (congrArg (fun v => v.1.stage.val) h),
    Or.inr (Or.inl ⟨b.prefix_spec _ (Nat.sub_le _ _), ?_⟩)⟩
  exact hp

/-- Every edge between distinct birth blocks is an immediate-parent edge. -/
theorem edge_parent {a b : Block M n k hM} {x y : Label M}
    (hab : a.IsPrefix b) (hne : a ≠ b)
    (he : (graph M n k hM).Adj (a,x) (b,y)) :
    a = parent b ∧ x ∈ separator b ∧ b.stage.val ≠ 0 := by
  have hd := (historyData (retention M n hM)).depth_lt hab hne
  change a.stage.val < b.stage.val at hd
  have hx := (rolling_earlier (historyData (retention M n hM)) he hab.1).2.resolve_left hne
  change x ∈ (b.step b.stage).1 a.stage at hx
  have hcard := b.cardinal a.stage b.stage le_rfl
  change ((b.step b.stage).1 a.stage).card = quota 1 M a.stage.val b.stage.val at hcard
  have hgap : b.stage.val ≤ a.stage.val + 1 := by
    by_contra! hh
    have hz : ((b.step b.stage).1 a.stage).card = 0 := by
      simpa [quota, not_le.mpr hh] using hcard
    exact (Finset.card_pos.mpr ⟨x,hx⟩).ne' hz
  have hs : a.stage = previous b := Fin.ext (by change _ = b.stage.val - 1; omega)
  have heq : a = parent b := by
    apply History.ext' hs
    funext i
    by_cases hi : i ≤ a.stage
    · have hip : i ≤ previous b := hs ▸ hi
      simpa only [parent, History.prefix, hip, ite_true] using hab.2 i hi
    · have hip : ¬ i ≤ previous b := hs ▸ hi
      simp only [parent, History.prefix, hip, ite_false, a.beyond i (lt_of_not_ge hi)]
  refine ⟨heq, ?_, by omega⟩
  simpa only [separator, ← hs] using hx

section Average
variable {ι E : Type*} [DecidableEq ι] [SeminormedAddCommGroup E] [NormedSpace ℝ E]

def average (S : Finset ι) (f : ι → E) : E := (S.card : ℝ)⁻¹ • ∑ p ∈ S, f p

omit [DecidableEq ι] in
theorem average_sub (S : Finset ι) (f g : ι → E) :
    average S (fun p => f p - g p) = average S f - average S g := by
  simp only [average, Finset.sum_sub_distrib, smul_sub]

omit [DecidableEq ι] in
theorem average_const (S : Finset ι) (hS : S.Nonempty) (c : E) :
    average S (fun _ => c) = c := by
  have hc : (S.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hS).ne'
  simp only [average, Finset.sum_const]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hc, one_smul]

omit [DecidableEq ι] in
theorem norm_average_le (S : Finset ι) (f : ι → E) :
    ‖average S f‖ ≤ (S.card : ℝ)⁻¹ * ∑ p ∈ S, ‖f p‖ := by
  rw [average, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (Nat.cast_nonneg _)]
  exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)

omit [DecidableEq ι] in
theorem average_bound (S : Finset ι) (hS : S.Nonempty) (f : ι → E)
    (R : ℝ) (hf : ∀ p ∈ S, ‖f p‖ ≤ R) : ‖average S f‖ ≤ R := by
  have hc : (S.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hS).ne'
  calc
    _ ≤ (S.card : ℝ)⁻¹ * ∑ p ∈ S, ‖f p‖ := norm_average_le S f
    _ ≤ (S.card : ℝ)⁻¹ * ∑ _p ∈ S, R :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hf) (by positivity)
    _ = R := by simp [hc]

theorem average_bound_zero (S : Finset ι) (s : ι) (hs : s ∈ S) (f : ι → E)
    (R : ℝ) (hz : f s = 0) (hf : ∀ p ∈ S.erase s, ‖f p‖ ≤ R) :
    ‖average S f‖ ≤ (S.card : ℝ)⁻¹ * ((S.card : ℝ)-1) * R := by
  have he : ∑ p ∈ S, ‖f p‖ = ∑ p ∈ S.erase s, ‖f p‖ := by
    rw [← Finset.sum_erase_add _ _ hs, hz, norm_zero, add_zero]
  calc
    _ ≤ (S.card : ℝ)⁻¹ * ∑ p ∈ S, ‖f p‖ := norm_average_le S f
    _ = (S.card : ℝ)⁻¹ * ∑ p ∈ S.erase s, ‖f p‖ := by rw [he]
    _ ≤ (S.card : ℝ)⁻¹ * ∑ _p ∈ S.erase s, R :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hf) (by positivity)
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem hs,
        Nat.cast_sub (Finset.card_pos.mpr ⟨s,hs⟩), Nat.cast_one]
      ring
end Average

section Defect
variable {V E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

theorem skew_diagonal (g : V → V → E) (hrev : ∀ u v, g v u = -g u v) (u : V) :
    g u u = 0 := by
  have he : (2 : ℝ) • g u u = 0 := by
    simpa only [two_smul] using (add_eq_zero_iff_eq_neg.mpr (hrev u u))
  exact (smul_eq_zero.mp he).resolve_left (by norm_num)

/-- The triangle estimate also covers repeated vertices. -/
theorem defect_le (G : SimpleGraph V) (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε)
    (hrev : ∀ u v, g v u = -g u v)
    (htri : ∀ u v z, G.Adj u v → G.Adj v z → G.Adj u z →
      ‖g u v + g v z - g u z‖ ≤ ε)
    (u v z : V) (huv : u = v ∨ G.Adj u v) (hvz : v = z ∨ G.Adj v z)
    (huz : u = z ∨ G.Adj u z) : ‖g u v + g v z - g u z‖ ≤ ε := by
  rcases huv with rfl | huv
  · simpa [skew_diagonal g hrev] using hε
  rcases hvz with rfl | hvz
  · simpa [skew_diagonal g hrev] using hε
  rcases huz with rfl | huz
  · rw [hrev v u, skew_diagonal g hrev u]
    simpa using hε
  exact htri u v z huv hvz huz
end Defect

section Potential
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

def zeroLabel (m : ℕ) (hm : 2 ≤ m) : Label m :=
  ⟨0, pow_pos (Nat.lt_of_lt_of_le (by decide : 0 < 2) hm) _⟩

/-- Transport at the root; average transport from all retained parent labels thereafter. -/
def potential (g : Vertex M n k hM → Vertex M n k hM → E)
    (b : Block M n k hM) (x : Label M) : E :=
  if hb : b.stage.val = 0 then g (b,zeroLabel M hM) (b,x)
  else (M^2 : ℝ)⁻¹ • ∑ p ∈ separator b,
    (potential g (parent b) p + g (parent b,p) (b,x))
termination_by b.stage.val
decreasing_by exact parent_lt b hb

theorem potential_root (g : Vertex M n k hM → Vertex M n k hM → E)
    (b : Block M n k hM) (hb : b.stage.val = 0) (x : Label M) :
    potential g b x = g (b,zeroLabel M hM) (b,x) := by
  rw [potential, dite_eq_left hb]

theorem potential_child (g : Vertex M n k hM → Vertex M n k hM → E)
    (b : Block M n k hM) (hb : b.stage.val ≠ 0) (x : Label M) :
    potential g b x = (M^2 : ℝ)⁻¹ • ∑ p ∈ separator b,
      (potential g (parent b) p + g (parent b,p) (b,x)) := by
  rw [potential, dite_eq_right hb]

theorem separator_nonempty (b : Block M n k hM) (hb : b.stage.val ≠ 0) :
    (separator b).Nonempty := by
  rw [← Finset.card_pos, separator_card b hb]
  exact pow_pos (by omega) _

theorem potential_child_average (g : Vertex M n k hM → Vertex M n k hM → E)
    (b : Block M n k hM) (hb : b.stage.val ≠ 0) (x : Label M) :
    potential g b x = average (separator b) (fun p =>
      potential g (parent b) p + g (parent b,p) (b,x)) := by
  rw [potential_child g b hb, average, separator_card b hb, Nat.cast_pow]

/-- Internal residuals have norm at most the original triangle budget at every depth. -/
theorem internal_bound (g : Vertex M n k hM → Vertex M n k hM → E)
    (ε : ℝ) (hε : 0 ≤ ε) (hrev : ∀ u v, g v u = -g u v)
    (htri : ∀ u v z, (graph M n k hM).Adj u v →
      (graph M n k hM).Adj v z → (graph M n k hM).Adj u z →
      ‖g u v + g v z - g u z‖ ≤ ε)
    (b : Block M n k hM) (x y : Label M) :
    ‖potential g b y - potential g b x - g (b,x) (b,y)‖ ≤ ε := by
  classical
  have clique (a c : Label M) : (b,a) = (b,c) ∨ (graph M n k hM).Adj (b,a) (b,c) := by
    by_cases h : a = c
    · exact Or.inl (congrArg (Prod.mk b) h)
    · exact Or.inr (internal_adj b h)
  by_cases hb : b.stage.val = 0
  · rw [potential_root g b hb y, potential_root g b hb x]
    have ht := defect_le (graph M n k hM) g ε hε hrev htri
      (b,zeroLabel M hM) (b,x) (b,y) (clique _ _) (clique _ _) (clique _ _)
    calc
      _ = ‖-(g (b,zeroLabel M hM) (b,x) + g (b,x) (b,y) -
          g (b,zeroLabel M hM) (b,y))‖ := congrArg norm (by abel)
      _ = _ := norm_neg _
      _ ≤ ε := ht
  · let S := separator b
    let A (p : Label M) := potential g (parent b) p + g (parent b,p) (b,y)
    let B (p : Label M) := potential g (parent b) p + g (parent b,p) (b,x)
    have he : potential g b y - potential g b x - g (b,x) (b,y) =
        average S (fun p => (A p - B p) - g (b,x) (b,y)) := by
      rw [average_sub, average_const S (separator_nonempty b hb), average_sub]
      rw [← potential_child_average g b hb y, ← potential_child_average g b hb x]
    rw [he]
    apply average_bound S (separator_nonempty b hb)
    intro p hp
    have ht := defect_le (graph M n k hM) g ε hε hrev htri
      (parent b,p) (b,x) (b,y) (Or.inr (separator_adj b hb hp x))
      (clique _ _) (Or.inr (separator_adj b hb hp y))
    calc
      _ = ‖-(g (parent b,p) (b,x) + g (b,x) (b,y) - g (parent b,p) (b,y))‖ :=
        congrArg norm (by dsimp [A,B]; abel)
      _ = _ := norm_neg _
      _ ≤ ε := ht

/-- One vanishing summand and two triangle budgets on each other separator label. -/
theorem cross_bound (g : Vertex M n k hM → Vertex M n k hM → E)
    (ε : ℝ) (hε : 0 ≤ ε) (hrev : ∀ u v, g v u = -g u v)
    (htri : ∀ u v z, (graph M n k hM).Adj u v →
      (graph M n k hM).Adj v z → (graph M n k hM).Adj u z →
      ‖g u v + g v z - g u z‖ ≤ ε)
    (b : Block M n k hM) (hb : b.stage.val ≠ 0)
    (s x : Label M) (hs : s ∈ separator b) :
    ‖potential g b x - potential g (parent b) s - g (parent b,s) (b,x)‖ ≤
      (2 - 2 / (M : ℝ)^2) * ε := by
  classical
  let S := separator b
  let f (p : Label M) :=
    (potential g (parent b) p + g (parent b,p) (b,x)) -
    (potential g (parent b) s + g (parent b,s) (b,x))
  have he : average S f =
      potential g b x - potential g (parent b) s - g (parent b,s) (b,x) := by
    rw [average_sub, average_const S (separator_nonempty b hb),
      ← potential_child_average g b hb x]
    abel
  have hz : f s = 0 := sub_self _
  have hf (p : Label M) (hp : p ∈ S.erase s) : ‖f p‖ ≤ 2 * ε := by
    have hps : p ≠ s := (Finset.mem_erase.mp hp).1
    have hpS : p ∈ separator b := (Finset.mem_erase.mp hp).2
    have hi := internal_bound g ε hε hrev htri (parent b) s p
    have ht := htri (parent b,s) (parent b,p) (b,x)
      (internal_adj (parent b) hps.symm) (separator_adj b hb hpS x)
      (separator_adj b hb hs x)
    calc
      ‖f p‖ = ‖(potential g (parent b) p - potential g (parent b) s -
          g (parent b,s) (parent b,p)) +
          (g (parent b,s) (parent b,p) + g (parent b,p) (b,x) -
            g (parent b,s) (b,x))‖ := congrArg norm (by dsimp [f]; abel)
      _ ≤ _ := norm_add_le _ _
      _ ≤ ε + ε := add_le_add hi ht
      _ = 2 * ε := by ring
  have hav := average_bound_zero S s hs f (2 * ε) hz hf
  rw [he] at hav
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  have hc : (S.card : ℝ)⁻¹ * ((S.card : ℝ)-1) * (2 * ε) =
      (2 - 2 / (M : ℝ)^2) * ε := by
    dsimp [S]
    rw [separator_card b hb, Nat.cast_pow]
    field_simp
  exact hav.trans_eq hc

/-- Explicit, depth-independent sharp upper coefficient on the actual history graph.
The theorem holds for all M≥2, hence in particular for every even M≥2. -/
theorem potential_bound (g : Vertex M n k hM → Vertex M n k hM → E)
    (ε : ℝ) (hε : 0 ≤ ε) (hrev : ∀ u v, g v u = -g u v)
    (htri : ∀ u v z, (graph M n k hM).Adj u v →
      (graph M n k hM).Adj v z → (graph M n k hM).Adj u z →
      ‖g u v + g v z - g u z‖ ≤ ε)
    (u v : Vertex M n k hM) (huv : (graph M n k hM).Adj u v) :
    ‖g u v - (potential g v.1 v.2 - potential g u.1 u.2)‖ ≤
      (2 - 2 / (M : ℝ)^2) * ε := by
  have hm : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hcoef : 1 ≤ 2 - 2 / (M : ℝ)^2 := by
    have hp : (0 : ℝ) < (M : ℝ)^2 := by positivity
    have hsq : (2 : ℝ) ≤ (M : ℝ)^2 := by nlinarith
    have hd : 2 / (M : ℝ)^2 ≤ (1 : ℝ) := (div_le_one hp).mpr hsq
    linarith
  have earlier (a b : Vertex M n k hM) (hab : (graph M n k hM).Adj a b)
      (hp : a.1.IsPrefix b.1) :
      ‖potential g b.1 b.2 - potential g a.1 a.2 - g a b‖ ≤
        (2 - 2 / (M : ℝ)^2) * ε := by
    rcases a with ⟨a,s⟩
    rcases b with ⟨b,t⟩
    change a.IsPrefix b at hp
    change ‖potential g b t - potential g a s - g (a,s) (b,t)‖ ≤ _
    by_cases he : a = b
    · subst a
      have hi := internal_bound g ε hε hrev htri b s t
      exact hi.trans ((one_mul ε).symm.trans_le (mul_le_mul_of_nonneg_right hcoef hε))
    · obtain ⟨heq,hkeep,hpos⟩ := edge_parent hp he hab
      subst a
      exact cross_bound g ε hε hrev htri b hpos s t hkeep
  rcases huv.2 with he | hp | hp
  · have h := earlier u v huv (he ▸ (historyData (retention M n hM)).refl u.1)
    calc
      _ = ‖-(potential g v.1 v.2 - potential g u.1 u.2 - g u v)‖ := congrArg norm (by abel)
      _ = _ := norm_neg _
      _ ≤ _ := h
  · have h := earlier u v huv hp.1
    calc
      _ = ‖-(potential g v.1 v.2 - potential g u.1 u.2 - g u v)‖ := congrArg norm (by abel)
      _ = _ := norm_neg _
      _ ≤ _ := h
  · have h := earlier v u huv.symm hp.1
    calc
      _ = ‖potential g u.1 u.2 - potential g v.1 v.2 - g v u‖ := by
        rw [hrev v u]
        congr 1
        abel
      _ ≤ _ := h

end Potential
end
end Omega.RollingCliques.SpanOne

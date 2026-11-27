/- GID: D5/S3/Combinatorics/Graph/Chordal/MultiIdentitySimplicialBanach
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Chordal/MultiIdentitySimplicialBanach
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Old triangle differences and two retained identities sharpen chordal gain bounds. -/
import D5.S3.Combinatorics.Graph.Chordal.EliminationForest
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Module
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Tactic.IntervalCases
/-! # Chordal gain reconstruction by retained simplicial identities -/
namespace SimpleGraph
open scoped BigOperators
namespace MultiIdentity
variable {V E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
private structure Predecessors (G : SimpleGraph V) where
  rank : V → ℕ
  injective : Function.Injective rank
  set : V → Finset V
  mem : ∀ x v, x ∈ set v ↔ rank x < rank v ∧ G.Adj x v
  clique : ∀ v, G.IsClique (set v : Set V)
private theorem predecessor_order [Finite V] {G : SimpleGraph V} (hG : G.IsChordal) :
    Nonempty (Predecessors G) := by
  classical
  let := Fintype.ofFinite V
  obtain ⟨ord, h⟩ := hG.exists_isPEO
  let N := (Finset.univ : Finset V).sup ord
  have hN (v : V) : ord v ≤ N := Finset.le_sup (Finset.mem_univ v)
  let rank (v : V) := N - ord v
  have less (x v : V) : rank x < rank v ↔ ord v < ord x := by
    dsimp [rank]
    have := hN x
    have := hN v
    omega
  let P (v : V) := Finset.univ.filter fun x => rank x < rank v ∧ G.Adj x v
  refine ⟨⟨rank, ?_, P, by simp [P], ?_⟩⟩
  · intro x v he
    apply h.injective
    dsimp [rank] at he
    have := hN x
    have := hN v
    omega
  · intro v x hx y hy hne
    simp only [P, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, less] at hx hy
    exact h.isClique_later v ⟨hx.1, hx.2.symm⟩ ⟨hy.1, hy.2.symm⟩ hne
private theorem Predecessors.card_le {G : SimpleGraph V} (O : Predecessors G) {k : ℕ}
    (hG : ∀ C : Set V, G.IsClique C → C.ncard ≤ k + 1) (v : V) :
    (O.set v).card ≤ k := by
  classical
  have hc : G.IsClique (insert v (O.set v : Set V)) := by
    intro x hx y hy hne
    rcases hx with rfl | hx
    · exact ((O.mem _ _).mp (hy.resolve_left hne.symm)).2.symm
    · rcases hy with rfl | hy
      · exact ((O.mem _ _).mp hx).2
      · exact O.clique v hx hy hne
  have h := hG _ hc
  rw [Set.ncard_insert_of_notMem (show v ∉ (O.set v : Set V) from fun hv =>
    (lt_irrefl _ ((O.mem _ _).mp hv).1)), Set.ncard_coe_finset] at h
  omega
private theorem Predecessors.earlier {G : SimpleGraph V} (O : Predecessors G)
    {x c v : V} (hx : x ∈ O.set v) (hc : c ∈ O.set v) (h : O.rank x < O.rank c) :
    x ∈ O.set c :=
  (O.mem x c).mpr ⟨h, O.clique v hx hc (fun e => h.ne (congrArg O.rank e))⟩
private theorem weighted_norm {A : Finset V} {q : V → ℝ} {f : V → E} {B : ℝ}
    (hq : ∀ x ∈ A, 0 ≤ q x) (hf : ∀ x ∈ A, ‖f x‖ ≤ B) :
    ‖∑ x ∈ A, q x • f x‖ ≤ (∑ x ∈ A, q x) * B := by
  apply (norm_sum_le _ _).trans
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun x hx => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hq x hx)]
    exact mul_le_mul_of_nonneg_left (hf x hx) (hq x hx)
private noncomputable def potential {G : SimpleGraph V} (O : Predecessors G)
    (w : V → V → ℝ) (g : V → V → E) (v : V) : E :=
  ∑ x ∈ (O.set v).attach, w v (x : V) • (potential O w g (x : V) + g x v)
termination_by O.rank v
decreasing_by exact ((O.mem _ _).mp x.property).1
private theorem potential_eq {G : SimpleGraph V} (O : Predecessors G)
    (w : V → V → ℝ) (g : V → V → E) (v : V) :
    potential O w g v = ∑ x ∈ O.set v, w v x • (potential O w g x + g x v) := by
  rw [potential]
  exact Finset.sum_attach _ (fun x => w v x • (potential O w g x + g x v))
private def residual (g : V → V → E) (p : V → E) (x y : V) : E := g x y - (p y - p x)
private theorem residual_reverse {g : V → V → E} {p : V → E}
    (hskew : ∀ x y, g y x = -g x y) (x y : V) :
    residual g p y x = -residual g p x y := by
  unfold residual
  rw [hskew x y]
  abel
private theorem residual_diag {g : V → V → E} {p : V → E}
    (hskew : ∀ x y, g y x = -g x y) (x : V) : residual g p x x = 0 := by
  have hr := residual_reverse (p := p) hskew x x
  have hz : (2 : ℝ) • residual g p x x = 0 := by
    rw [two_smul, ← sub_neg_eq_add, ← hr, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)
private theorem retained {G : SimpleGraph V} (O : Predecessors G)
    (w : V → V → ℝ) (g : V → V → E) (hskew : ∀ x y, g y x = -g x y)
    (v : V) (hw : ∑ x ∈ O.set v, w v x = 1) :
    ∑ x ∈ O.set v, w v x • residual g (potential O w g) v x = 0 := by
  let p := potential O w g
  change ∑ x ∈ O.set v, w v x • residual g p v x = 0
  have h (x : V) : residual g p v x = p v - (p x + g x v) := by
    rw [residual_reverse hskew x v]
    unfold residual
    abel
  simp only [h, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hw, one_smul]
  exact sub_eq_zero.mpr (potential_eq O w g v)
private def defect (g : V → V → E) (x y z : V) : E := g x y + g y z - g x z
private theorem triangle_identity (g : V → V → E) (p : V → E) (x y z : V) :
    residual g p x y + residual g p y z - residual g p x z = defect g x y z := by
  unfold residual defect
  abel
private theorem step_formula [DecidableEq V] {G : SimpleGraph V} (O : Predecessors G)
    (w : V → V → ℝ) (g : V → V → E) (hskew : ∀ x y, g y x = -g x y)
    {c v : V} (hc : c ∈ O.set v) (hw : ∑ x ∈ O.set v, w v x = 1) :
    let r := residual g (potential O w g)
    r c v = (∑ x ∈ (O.set v).erase c, w v x • r c x) -
      ∑ x ∈ (O.set v).erase c, w v x • defect g c x v := by
  dsimp only
  let p := potential O w g
  let r := residual g p
  change r c v = (∑ x ∈ (O.set v).erase c, w v x • r c x) - _
  have h (x : V) : r c x - defect g c x v = r c v + r v x := by
    have h := triangle_identity g p c x v
    change r c x + r x v - r c v = _ at h
    rw [show r v x = -r x v from residual_reverse hskew x v, ← h]
    abel
  have hz : defect g c c v = 0 := by
    simpa [r, residual_diag hskew c] using (triangle_identity g p c c v).symm
  rw [← Finset.sum_sub_distrib]
  simp only [← smul_sub]
  have he : (∑ x ∈ O.set v, w v x • (r c x - defect g c x v)) =
      ∑ x ∈ (O.set v).erase c, w v x • (r c x - defect g c x v) := by
    rw [← (O.set v).sum_erase_add _ hc]
    simp [r, residual_diag hskew c, hz]
  rw [← he]
  simp only [h, smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hw, one_smul]
  rw [show (∑ x ∈ O.set v, w v x • r v x) = 0 from retained O w g hskew v hw, add_zero]
private structure OldBounds {G : SimpleGraph V} (O : Predecessors G)
    (r : V → V → E) (R ε : ℝ) (v : V) : Prop where
  edge : ∀ x y, O.rank x < O.rank v → O.rank y < O.rank v → G.Adj x y → ‖r x y‖ ≤ R * ε
  triangle : ∀ x y z, G.Adj x y → G.Adj y z → G.Adj x z → ‖r x y + r y z - r x z‖ ≤ ε
  diag : ∀ x, r x x = 0
private theorem OldBounds.diameter {G : SimpleGraph V} {O : Predecessors G}
    {r : V → V → E} {R ε : ℝ} (h : OldBounds O r R ε v) (hε : 0 ≤ ε) (hR : 0 ≤ R)
    {c x y : V} (hc : O.rank c < O.rank v) (hx : x ∈ O.set c) (hy : y ∈ O.set c) :
    ‖r c x - r c y‖ ≤ (R + 1) * ε := by
  by_cases he : x = y
  · subst y
    simpa using mul_nonneg (by linarith : 0 ≤ R + 1) hε
  have hx' := (O.mem _ _).mp hx
  have hy' := (O.mem _ _).mp hy
  have hxy := O.clique c hx hy he
  have ht := h.triangle c x y hx'.2.symm hxy hy'.2.symm
  have hr := h.edge x y (hx'.1.trans hc) (hy'.1.trans hc) hxy
  rw [show r c x - r c y = (r c x + r x y - r c y) - r x y by abel]
  exact (norm_sub_le _ _).trans (by linarith)
private theorem ordered_fit [DecidableEq V] {G : SimpleGraph V} (O : Predecessors G)
    (w : V → V → ℝ) (g : V → V → E) {R ε : ℝ}
    (hskew : ∀ x y, g y x = -g x y)
    (htri : ∀ x y z, G.Adj x y → G.Adj y z → G.Adj x z → ‖defect g x y z‖ ≤ ε)
    (htotal : ∀ v, (O.set v).Nonempty → ∑ x ∈ O.set v, w v x = 1)
    (hpos : ∀ v x, x ∈ O.set v → 0 ≤ w v x)
    (hstep : ∀ (r : V → V → E) (v c : V), c ∈ O.set v → OldBounds O r R ε v →
      (∀ a, (O.set a).Nonempty → ∑ x ∈ O.set a, w a x • r a x = 0) →
      ‖∑ x ∈ (O.set v).erase c, w v x • r c x‖ +
        (1 - w v c) * ε ≤ R * ε) :
    ∃ p : V → E, ∀ x y, G.Adj x y → ‖residual g p x y‖ ≤ R * ε := by
  let p := potential O w g
  let r := residual g p
  have hz (a : V) (ha : (O.set a).Nonempty) : ∑ x ∈ O.set a, w a x • r a x = 0 :=
    retained O w g hskew a (htotal a ha)
  have ordered (n : ℕ) : ∀ v, O.rank v = n → ∀ c ∈ O.set v, ‖r c v‖ ≤ R * ε := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hn c hc
      have old (x y : V) (hx : O.rank x < O.rank v) (hy : O.rank y < O.rank v)
          (hxy : G.Adj x y) : ‖r x y‖ ≤ R * ε := by
        rcases lt_or_gt_of_ne (fun h => hxy.ne (O.injective h)) with hlt | hlt
        · exact ih _ (hn ▸ hy) y rfl x ((O.mem x y).mpr ⟨hlt, hxy⟩)
        · rw [show r x y = -r y x from residual_reverse hskew y x, norm_neg]
          exact ih _ (hn ▸ hx) x rfl y ((O.mem y x).mpr ⟨hlt, hxy.symm⟩)
      have hold : OldBounds O r R ε v := ⟨old, fun x y z hxy hyz hxz => by
        rw [triangle_identity]; exact htri x y z hxy hyz hxz, residual_diag hskew⟩
      have hsum := htotal v ⟨c, hc⟩
      have hm := (O.set v).sum_erase_add (w v) hc
      rw [hsum] at hm
      change ‖residual g (potential O w g) c v‖ ≤ _
      rw [step_formula O w g hskew hc hsum]
      apply (norm_sub_le _ _).trans
      apply le_trans (add_le_add_right (weighted_norm (fun x hx => hpos v x (Finset.mem_of_mem_erase hx))
        (fun x hx => htri c x v (O.clique v hc (Finset.mem_of_mem_erase hx)
          (Finset.ne_of_mem_erase hx).symm) ((O.mem _ _).mp (Finset.mem_of_mem_erase hx)).2
          ((O.mem _ _).mp hc).2)) _)
      rw [eq_sub_of_add_eq hm]
      exact hstep r v c hc hold hz
  refine ⟨p, fun x y hxy => ?_⟩
  rcases lt_or_gt_of_ne (fun h => hxy.ne (O.injective h)) with hlt | hlt
  · exact ordered _ y rfl x ((O.mem x y).mpr ⟨hlt, hxy⟩)
  · rw [residual_reverse hskew y x, norm_neg]
    exact ordered _ x rfl y ((O.mem y x).mpr ⟨hlt, hxy.symm⟩)
private theorem direct_step [DecidableEq V] {G : SimpleGraph V} {O : Predecessors G}
    {r : V → V → E} {w : V → V → ℝ} {v c : V} {R ε : ℝ}
    (h : OldBounds O r R ε v) (hc : c ∈ O.set v) (hε : 0 ≤ ε)
    (ht : ∑ x ∈ O.set v, w v x = 1) (hw : ∀ x ∈ O.set v, 0 ≤ w v x)
    (hb : (1 - w v c) * (R + 1) ≤ R) :
    ‖∑ x ∈ (O.set v).erase c, w v x • r c x‖ + (1 - w v c) * ε ≤ R * ε := by
  have hm := (O.set v).sum_erase_add (w v) hc
  rw [ht] at hm
  have hn := weighted_norm (fun x hx => hw x (Finset.mem_of_mem_erase hx))
    (fun x hx => h.edge c x ((O.mem _ _).mp hc).1 ((O.mem _ _).mp (Finset.mem_of_mem_erase hx)).1
      (O.clique v hc (Finset.mem_of_mem_erase hx) (Finset.ne_of_mem_erase hx).symm))
  rw [eq_sub_of_add_eq hm] at hn
  nlinarith only [hn, mul_le_mul_of_nonneg_right hb hε]
/-- Match the positive and negative masses. An auxiliary vector may have an
additional one-sided distance cost to the negative support. -/
private theorem balanced_norm {A : Finset V} {h e : V → ℝ} {C : V → E} {D : ℝ}
    (hz : ∑ x ∈ A, h x = 0) (hD : 0 ≤ D) (he : ∀ x ∈ A, 0 ≤ e x)
    (hd : ∀ x ∈ A, ∀ y ∈ A, 0 < h x → h y < 0 → ‖C x - C y‖ ≤ D + e x) :
    ‖∑ x ∈ A, h x • C x‖ ≤ (∑ x ∈ A, max (-h x) 0)*D +
      ∑ x ∈ A, max (h x) 0 * e x := by
  let pos (x : V) := max (h x) 0
  let neg (x : V) := max (-h x) 0
  let M := ∑ x ∈ A, neg x
  have hp (x : V) : 0 ≤ pos x := le_max_right _ _
  have hn (x : V) : 0 ≤ neg x := le_max_right _ _
  have hh (x : V) : h x = pos x - neg x := by
    by_cases h₀ : 0 ≤ h x
    · simp [pos, neg, max_eq_left h₀, max_eq_right (neg_nonpos.mpr h₀)]
    · have h₁ := le_of_not_ge h₀
      simp [pos, neg, max_eq_right h₁, max_eq_left (neg_nonneg.mpr h₁)]
  have hm : ∑ x ∈ A, pos x = M := by
    have hsum : ∑ x ∈ A, h x = ∑ x ∈ A, (pos x - neg x) :=
      Finset.sum_congr rfl fun x _ => hh x
    rw [hz, Finset.sum_sub_distrib] at hsum
    exact sub_eq_zero.mp hsum.symm
  have hM : 0 ≤ M := Finset.sum_nonneg fun x _ => hn x
  by_cases hzero : M = 0
  · have hpz := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hp x)).mp (hm.trans hzero)
    have hnz := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hn x)).mp hzero
    have hs : (∑ x ∈ A, h x • C x) = 0 := Finset.sum_eq_zero fun x hx => by
      rw [hh x, hpz x hx, hnz x hx, sub_zero, zero_smul]
    rw [hs, norm_zero]
    exact add_nonneg (mul_nonneg hM hD) (Finset.sum_nonneg fun x hx => mul_nonneg (hp x) (he x hx))
  let q (y : V) := neg y / M
  have hq (y : V) : 0 ≤ q y := div_nonneg (hn y) hM
  have hqt : ∑ y ∈ A, q y = 1 := by
    simp only [q, div_eq_mul_inv, ← Finset.sum_mul, show (∑ y ∈ A, neg y) = M from rfl,
      mul_inv_cancel₀ hzero]
  have hmatch :
      (∑ x ∈ A, h x • C x) =
        ∑ x ∈ A, pos x • ∑ y ∈ A, q y • (C x - C y) := by
    have hs : (M • ∑ y ∈ A, q y • C y) = ∑ y ∈ A, neg y • C y := by
      simp only [Finset.smul_sum, smul_smul]
      apply Finset.sum_congr rfl
      intro y _
      rw [mul_comm, show q y * M = neg y from div_mul_cancel₀ _ hzero]
    simp only [hh, sub_smul, Finset.sum_sub_distrib, smul_sub, ← Finset.sum_smul,
      hqt, one_smul, hm, hs]
  rw [hmatch]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ x ∈ A, pos x * (D + e x) := by
      apply Finset.sum_le_sum
      intro x hx
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hp x)]
      by_cases hxp : 0 < h x
      · apply mul_le_mul_of_nonneg_left _ (hp x)
        apply (norm_sum_le _ _).trans
        rw [← one_mul (D + e x), ← hqt, Finset.sum_mul]
        apply Finset.sum_le_sum
        intro y hy
        by_cases hyn : h y < 0
        · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hq y)]
          exact mul_le_mul_of_nonneg_left (hd x hx y hy hxp hyn) (hq y)
        · simp [q, neg, max_eq_right (neg_nonpos.mpr (le_of_not_gt hyn))]
      · simp [pos, max_eq_right (le_of_not_gt hxp)]
    _ = _ := by simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hm]; rfl
private theorem sum_extend [DecidableEq V] {A B : Finset V} (hAB : A ⊆ B)
    {M : Type*} [AddCommMonoid M] (f : V → M) :
    (∑ x ∈ B, if x ∈ A then f x else 0) = ∑ x ∈ A, f x := by
  rw [← Finset.sum_filter]
  congr 1
  ext x
  simp only [Finset.mem_filter]
  exact ⟨And.right, fun hx => ⟨hAB hx, hx⟩⟩
private theorem second_identity [DecidableEq V] {G : SimpleGraph V} {O : Predecessors G}
    {r : V → V → E} {R ε : ℝ} {v c a : V}
    (hold : OldBounds O r R ε v) (hR : 0 ≤ R) (hε : 0 ≤ ε)
    (hc : O.rank c < O.rank v) (ha : a ∈ O.set c) {h β : V → ℝ}
    (hh : ∑ x ∈ O.set c, h x = 0) (hcharge : 0 ≤ h a)
    (hβ : ∀ x ∈ O.set a, 0 ≤ β x) (hβsum : ∑ x ∈ O.set a, β x = 1)
    (hretain : ∑ x ∈ O.set a, β x • r a x = 0)
    (hneg : ∀ x ∈ O.set c, h x < 0 → x ∈ O.set a) :
    let b (x : V) := if x ∈ O.set a then β x else 0
    let h' (x : V) := (if x = a then 0 else h x) + h a * b x
    ‖∑ x ∈ O.set c, h x • r c x‖ ≤
      (∑ x ∈ O.set c, max (-h' x) 0) * ((R+1)*ε) + h a * ε := by
  dsimp only
  let Q := O.set c
  let B := O.set a
  let A := Q ∪ B
  let charge' := h a
  let C := r c
  let X (x : V) := if x ∈ Q then C x else C a + r a x
  let b (x : V) := if x ∈ B then β x else 0
  let u (x : V) := if x = a then 0 else h x
  let f (x : V) := (if x ∈ Q then u x else 0) + charge' * b x
  let e (x : V) : ℝ := if x ∈ Q then 0 else ε
  let δ (x : V) := C a + r a x - X x
  have hQA : Q ⊆ A := Finset.subset_union_left
  have hBA : B ⊆ A := Finset.subset_union_right
  have hD : 0 ≤ (R+1)*ε := mul_nonneg (by linarith) hε
  have hδ (x : V) (hx : x ∈ B) : ‖δ x‖ ≤ ε + -e x := by
    by_cases hxQ : x ∈ Q
    · have ht := hold.triangle c a x ((O.mem _ _).mp ha).2.symm
        ((O.mem _ _).mp hx).2.symm ((O.mem _ _).mp hxQ).2.symm
      simpa [δ, X, e, C, hxQ] using ht
    · simp [δ, X, e, hxQ]
  have hbn (x : V) : 0 ≤ b x := by
    by_cases hx : x ∈ B
    · simpa [b, hx] using hβ x hx
    · simp [b, hx]
  have hbext : ∑ x ∈ A, b x = 1 := (sum_extend hBA β).trans hβsum
  have hu : (∑ x ∈ Q, u x) + charge' = 0 := by
    rw [← Q.sum_erase_add _ ha, show u a = 0 by simp [u], add_zero]
    rw [← Q.sum_erase_add _ ha] at hh
    rw [← hh]
    exact congrArg (· + charge') (Finset.sum_congr rfl fun x hx => by simp [u, Finset.ne_of_mem_erase hx])
  have hf : ∑ x ∈ A, f x = 0 := by
    simp only [f, Finset.sum_add_distrib, sum_extend hQA, ← Finset.mul_sum, hbext, mul_one, hu]
  have hfext (x : V) (hx : x ∉ Q) : f x = charge' * b x := by simp [f, hx]
  have hneg' (y : V) (hy : f y < 0) : y ∈ Q ∧ y ∈ B := by
    have hyQ : y ∈ Q := by
      by_contra h
      exact hy.not_ge (hfext y h ▸ mul_nonneg hcharge (hbn y))
    have hp : h y < 0 := by
      by_contra! hp
      have hu' : 0 ≤ u y := by
        by_cases ha' : y = a <;> simp [u, ha', hp]
      exact hy.not_ge (by simpa [f, hyQ] using add_nonneg hu' (mul_nonneg hcharge (hbn y)))
    exact ⟨hyQ, hneg y hyQ hp⟩
  have hdist (x y : V) (hx : x ∈ A) (hyf : f y < 0) :
      ‖X x - X y‖ ≤ (R+1)*ε + e x := by
    obtain ⟨hyQ, hyB⟩ := hneg' y hyf
    by_cases hxQ : x ∈ Q
    · simpa [X, C, e, hxQ, hyQ] using hold.diameter hε hR hc hxQ hyQ
    · have hxB := (Finset.mem_union.mp hx).resolve_left hxQ
      have ha' := ((O.mem _ _).mp ha).1.trans hc
      rw [show X x - X y = (r a x - r a y) + δ y by simp [X, δ, hxQ]; abel]
      exact (norm_add_le _ _).trans (by
        have h := add_le_add (hold.diameter hε hR ha' hxB hyB) (hδ y hyB)
        simpa [e, hyQ, hxQ] using h)
  have he (x : V) : 0 ≤ e x := by by_cases hx : x ∈ Q <;> simp [e, hx, hε]
  have hnorm := balanced_norm hf hD (fun x _ => he x) (fun x hx y _ _ hy => hdist x y hx hy)
  have hmass :
      (∑ x ∈ A, max (-f x) 0) =
        ∑ x ∈ Q, max (-(u x + charge' * b x)) 0 := by
    rw [← sum_extend hQA]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x ∈ Q
    · simp [f, hx]
    · rw [hfext x hx, ite_eq_right hx, max_eq_right (neg_nonpos.mpr (mul_nonneg hcharge (hbn x)))]
  have hextra (x : V) : max (f x) 0 * e x = charge' * b x * e x := by
    by_cases hx : x ∈ Q
    · simp [e, hx]
    · rw [hfext x hx, max_eq_left (mul_nonneg hcharge (hbn x))]
  have hsumX : ∑ x ∈ A, f x • X x =
      (∑ x ∈ Q, u x • C x) + ∑ x ∈ B, (charge' * β x) • X x := by
    simp only [f, add_smul, Finset.sum_add_distrib]
    congr 1
    · rw [← sum_extend hQA]
      exact Finset.sum_congr rfl fun x _ => by by_cases hx : x ∈ Q <;> simp [X, hx]
    · rw [← sum_extend hBA]
      exact Finset.sum_congr rfl fun x _ => by by_cases hx : x ∈ B <;> simp [b, hx]
  have hsplit : ∑ x ∈ Q, h x • C x = (∑ x ∈ Q, u x • C x) + charge' • C a := by
    rw [← Q.sum_erase_add _ ha, ← Q.sum_erase_add (fun x => u x • C x) ha]
    simp only [u, ite_eq_left rfl, zero_smul, add_zero]
    exact congrArg (· + charge' • C a) (Finset.sum_congr rfl fun x hx => by simp [Finset.ne_of_mem_erase hx])
  have hδeq : ∑ x ∈ B, (charge' * β x) • δ x =
      charge' • C a - ∑ x ∈ B, (charge' * β x) • X x := by
    simp only [δ, ← smul_smul, ← Finset.smul_sum, smul_sub, smul_add, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, ← Finset.sum_smul]
    rw [show (∑ x ∈ B, β x) = 1 from hβsum, show (∑ x ∈ B, β x • r a x) = 0 from hretain]
    simp
  have hδnorm : ‖∑ x ∈ B, (charge' * β x) • δ x‖ ≤
      ∑ x ∈ B, (charge' * β x) * (ε + -e x) := (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun x hx => by
      have h := mul_nonneg hcharge (hβ x hx)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg h]
      exact mul_le_mul_of_nonneg_left (hδ x hx) h)
  have hcharges : (∑ x ∈ A, max (f x) 0 * e x) +
      ∑ x ∈ B, (charge' * β x) * (ε + -e x) = charge' * ε := by
    simp only [hextra, mul_add, mul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    have heq : (∑ x ∈ A, charge' * b x * e x) = ∑ x ∈ B, charge' * β x * e x := by
      rw [← sum_extend hBA]
      exact Finset.sum_congr rfl fun x _ => by by_cases hx : x ∈ B <;> simp [b, hx]
    rw [heq, ← Finset.sum_mul, ← Finset.mul_sum, hβsum, mul_one]
    ring
  rw [hsplit, show (∑ x ∈ Q, u x • C x) + charge' • C a =
      (∑ x ∈ A, f x • X x) + ∑ x ∈ B, (charge' * β x) • δ x by rw [hsumX, hδeq]; abel]
  apply (norm_add_le _ _).trans
  rw [hmass] at hnorm
  linarith only [hnorm, hδnorm, hcharges]
private noncomputable def regroupWeight [DecidableEq V] (k : ℕ) (s t : ℝ)
    (P : Finset V) (a x : V) : ℝ :=
  if P.card = k then if x = a then t else s else 1 / (P.card : ℝ)
private theorem regroup_total [DecidableEq V] {k : ℕ} {s t : ℝ} {P : Finset V}
    {a : V} (ha : a ∈ P) (ht : ((k : ℝ) - 1) * s + t = 1) :
    ∑ x ∈ P, regroupWeight k s t P a x = 1 := by
  by_cases hc : P.card = k
  · rw [← P.sum_erase_add _ ha]
    have hcard : ((P.erase a).card : ℝ) + 1 = k := by
      exact_mod_cast (Finset.card_erase_add_one ha).trans hc
    have hs : ∑ x ∈ P.erase a, regroupWeight k s t P a x = ((P.erase a).card : ℝ) * s := by
      calc
        _ = ∑ _ ∈ P.erase a, s := Finset.sum_congr rfl fun x hx => by
          simp [regroupWeight, hc, Finset.ne_of_mem_erase hx]
        _ = _ := by simp [nsmul_eq_mul]
    rw [hs]
    simp only [regroupWeight, hc, ite_true]
    rw [show ((P.erase a).card : ℝ) = (k : ℝ) - 1 by linarith]
    exact ht
  · have hp : (P.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr ⟨a, ha⟩
    simp [regroupWeight, hc, nsmul_eq_mul, hp]
private theorem regroup_sum [DecidableEq V] {k : ℕ} {s t : ℝ} {A P : Finset V}
    (hAP : A ⊆ P) (hA : A.card + 1 = k) (hPk : P.card ≤ k)
    {b : V} (hb : b ∈ P) {f : V → E} {B D : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hst : t ≤ s) (ht : 0 ≤ t) (hf : ∀ x ∈ P, ‖f x‖ ≤ B)
    (hd : ∀ x ∈ P, ∀ y ∈ P, ‖f x - f y‖ ≤ D)
    (hz : ∑ x ∈ P, regroupWeight k s t P b x • f x = 0) :
    ‖∑ x ∈ A, s • f x‖ ≤ (s-t)*D + t*B := by
  have hc := Finset.card_le_card hAP
  by_cases hP : P.card = k
  · obtain ⟨z, hzP, hzA⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := A) (t := P) (by omega)
    have hEq : insert z A = P := Finset.eq_of_subset_of_card_le
      (Finset.insert_subset hzP hAP) (by rw [Finset.card_insert_of_notMem hzA]; omega)
    have hsum : ∑ x ∈ P, s • f x = (s-t) • f b := by
      rw [← P.sum_erase_add _ hb] at hz ⊢
      simp only [regroupWeight, hP, ite_true] at hz
      have he : ∑ x ∈ P.erase b, (if x = b then t else s) • f x =
          ∑ x ∈ P.erase b, s • f x :=
        Finset.sum_congr rfl fun x hx => by simp [Finset.ne_of_mem_erase hx]
      rw [he, add_eq_zero_iff_eq_neg] at hz
      rw [hz, sub_smul, neg_add_eq_sub]
    rw [← hEq, Finset.sum_insert hzA, add_comm] at hsum
    have he : (∑ x ∈ A, s • f x) = (s-t) • (f b - f z) - t • f z := by
      rw [eq_sub_of_add_eq hsum]
      module
    rw [he]
    apply (norm_sub_le _ _).trans
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hst), abs_of_nonneg ht]
    exact add_le_add (mul_le_mul_of_nonneg_left (hd b hb z hzP) (sub_nonneg.mpr hst))
      (mul_le_mul_of_nonneg_left (hf z hzP) ht)
  · have he : A = P := Finset.eq_of_subset_of_card_le hAP (by omega)
    have hp : (P.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr ⟨b, hb⟩
    simp only [regroupWeight, hP, ite_false, ← Finset.smul_sum] at hz
    have hzero : ∑ x ∈ P, f x = 0 := (smul_eq_zero.mp hz).resolve_left (by simp [hp])
    simp only [he, ← Finset.smul_sum, hzero, smul_zero, norm_zero]
    positivity
private theorem regroup_fit {G : SimpleGraph V} (O : Predecessors G) {k : ℕ}
    (hk : 2 ≤ k) (hcard : ∀ v, (O.set v).card ≤ k) {R ε : ℝ} (hε : 0 ≤ ε)
    (hR : 1 ≤ R) (hmin : (k : ℝ) - 2 ≤ R) (hmax : R ≤ (k : ℝ) - 1)
    (hquad : 2 * ((k : ℝ) - 1) ≤ R * (R + 1))
    (g : V → V → E) (hskew : ∀ x y, g y x = -g x y)
    (htri : ∀ x y z, G.Adj x y → G.Adj y z → G.Adj x z → ‖defect g x y z‖ ≤ ε) :
    ∃ p : V → E, ∀ x y, G.Adj x y → ‖residual g p x y‖ ≤ R * ε := by
  classical
  let s := 1 / (R + 1)
  let t := 1 - ((k : ℝ) - 1) * s
  have hD : 0 < R + 1 := by linarith
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hsD : s * (R+1) = 1 := div_mul_cancel₀ _ hD.ne'
  have ht : 0 ≤ t := by
    apply nonneg_of_mul_nonneg_left _ hD
    dsimp only [t]
    rw [sub_mul, mul_assoc, hsD]
    linarith
  have hts : t ≤ s := by
    apply le_of_mul_le_mul_right _ hD
    dsimp only [t]
    rw [sub_mul, mul_assoc, hsD]
    linarith
  have hst : ((k : ℝ) - 1) * s + t = 1 := by dsimp [t]; ring
  have hbudget : (s-t)*(R+1) + t*R + (1-t) ≤ R := by
    have h := mul_le_mul_of_nonneg_right hquad hs
    rw [mul_assoc R (R + 1) s, mul_comm (R + 1) s, hsD, mul_one] at h
    nlinarith only [h, hst, hsD]
  let newest (v : V) := if h : (O.set v).Nonempty then
    (Finset.exists_max_image (O.set v) O.rank h).choose else v
  have hn (v : V) (hv : (O.set v).Nonempty) :
      newest v ∈ O.set v ∧ ∀ x ∈ O.set v, O.rank x ≤ O.rank (newest v) := by
    simpa [newest, hv] using (Finset.exists_max_image (O.set v) O.rank hv).choose_spec
  let w (v : V) := regroupWeight k s t (O.set v) (newest v)
  have htotal (v : V) (hv : (O.set v).Nonempty) : ∑ x ∈ O.set v, w v x = 1 :=
    regroup_total (hn v hv).1 hst
  have hnonneg (v x : V) : 0 ≤ w v x := by
    simp only [w, regroupWeight]
    split_ifs <;> positivity
  apply ordered_fit O w g hskew htri htotal (fun v x _ => hnonneg v x)
  intro r v c hc hold hz
  by_cases special : (O.set v).card = k ∧ c = newest v
  · obtain ⟨hv, he⟩ := special
    let A := (O.set v).erase c
    have hsub : A ⊆ O.set c := by
      intro x hx
      have hx' := Finset.mem_of_mem_erase hx
      exact O.earlier hx' hc (lt_of_le_of_ne ((hn v ⟨c, hc⟩).2 x hx' |>.trans_eq (congrArg O.rank he.symm))
        (fun e => Finset.ne_of_mem_erase hx (O.injective e)))
    have hA : A.card + 1 = k := (Finset.card_erase_add_one hc).trans hv
    have hPc : (O.set c).Nonempty := Finset.card_pos.mp (by have := Finset.card_le_card hsub; omega)
    have hcold := ((O.mem _ _).mp hc).1
    have hsum := regroup_sum hsub hA (hcard c) (hn c hPc).1
      (mul_nonneg (by linarith) hε) (mul_nonneg hD.le hε) hts ht
      (fun x hx => hold.edge c x hcold (((O.mem _ _).mp hx).1.trans hcold) ((O.mem _ _).mp hx).2.symm)
      (fun x hx y hy => hold.diameter hε (by linarith) hcold hx hy) (hz c hPc)
    have hw (x : V) (hx : x ∈ A) : w v x = s := by
      simp [w, regroupWeight, hv, ← he, Finset.ne_of_mem_erase hx]
    rw [show w v c = t by simp [w, regroupWeight, hv, he],
      Finset.sum_congr rfl (fun x hx => by rw [hw x hx])]
    nlinarith only [hsum, mul_le_mul_of_nonneg_right hbudget hε]
  · apply direct_step hold hc hε (htotal v ⟨c, hc⟩) (fun x _ => hnonneg v x)
    by_cases hv : (O.set v).card = k
    · have hne : c ≠ newest v := fun e => special ⟨hv, e⟩
      simp only [w, regroupWeight, hv, ite_true, hne, ite_false]
      nlinarith only [hsD]
    · have hp : 0 < ((O.set v).card : ℝ) := by exact_mod_cast (Finset.card_pos.mpr ⟨c, hc⟩)
      have hb : ((O.set v).card : ℝ) + 1 ≤ (k : ℝ) := by
        exact_mod_cast (show (O.set v).card + 1 ≤ k by have := hcard v; omega)
      have hi : 1 ≤ (1 / ((O.set v).card : ℝ)) * (R + 1) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hp]
        linarith
      simp only [w, regroupWeight, hv, ite_false]
      nlinarith only [hi]
/-- Position in an earlier clique, numbered from zero. -/
private noncomputable def position {G : SimpleGraph V} (O : Predecessors G)
    (P : Finset V) (x : V) : ℕ := (P.filter fun y => O.rank y < O.rank x).card
private theorem position_prefix {G : SimpleGraph V} (O : Predecessors G)
    (P : Finset V) {a x : V} (h : O.rank x < O.rank a) :
    position O (P.filter fun y => O.rank y < O.rank a) x = position O P x := by
  unfold position
  congr 1
  ext y
  simp only [Finset.mem_filter]
  exact ⟨fun ⟨⟨hy, _⟩, hyx⟩ => ⟨hy, hyx⟩, fun ⟨hy, hyx⟩ => ⟨⟨hy, hyx.trans h⟩, hyx⟩⟩
private theorem position_lt {G : SimpleGraph V} (O : Predecessors G) {P : Finset V}
    {x : V} (hx : x ∈ P) : position O P x < P.card :=
  Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, fun h => by
    have hm : x ∈ P.filter (fun y => O.rank y < O.rank x) := h.symm ▸ hx
    exact (lt_irrefl _) (Finset.mem_filter.mp hm).2⟩)
private theorem position_strict {G : SimpleGraph V} (O : Predecessors G) {P : Finset V}
    {x y : V} (hx : x ∈ P) (h : O.rank x < O.rank y) :
    position O P x < position O P y := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨fun z hz => ?_, fun he => ?_⟩
  · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1, (Finset.mem_filter.mp hz).2.trans h⟩
  · have hz : x ∈ P.filter (fun z => O.rank z < O.rank y) := Finset.mem_filter.mpr ⟨hx, h⟩
    have hm : x ∈ P.filter (fun z => O.rank z < O.rank x) := he.symm ▸ hz
    exact (lt_irrefl _) (Finset.mem_filter.mp hm).2
private theorem position_injective {G : SimpleGraph V} (O : Predecessors G) (P : Finset V) :
    Set.InjOn (position O P) (P : Set V) := by
  intro x hx y hy h
  apply O.injective
  rcases lt_trichotomy (O.rank x) (O.rank y) with hxy | he | hyx
  · exact ((position_strict O hx hxy).ne h).elim
  · exact he
  · exact ((position_strict O hy hyx).ne h.symm).elim
private theorem positions {G : SimpleGraph V} (O : Predecessors G) (P : Finset V) :
    P.image (position O P) = Finset.range P.card := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_range.mpr (position_lt O hx)
  · rw [Finset.card_range, Finset.card_image_of_injOn (position_injective O P)]
private noncomputable def profile (s t : ℝ) (d i : ℕ) : ℝ :=
  if d ≤ 3 then 1 / (d : ℝ) else if i < 3 then s else if i = 3 then t else 0
private theorem profile_total {G : SimpleGraph V} (O : Predecessors G) {P : Finset V}
    (hp : P.Nonempty) {s t : ℝ} (hst : 3*s + t = 1) :
    ∑ x ∈ P, profile s t P.card (position O P x) = 1 := by
  classical
  rw [← Finset.sum_image (f := profile s t P.card) (position_injective O P), positions]
  by_cases hd : P.card ≤ 3
  · have hn : (P.card : ℝ) ≠ 0 := by exact_mod_cast hp.card_ne_zero
    simp [profile, hd, nsmul_eq_mul, hn]
  · have h (i : ℕ) (hi : 4 ≤ i) : profile s t P.card i = 0 := by
      simp [profile, hd, show ¬ i < 3 by omega, show i ≠ 3 by omega]
    have split : ∑ i ∈ Finset.range P.card, profile s t P.card i =
        ∑ i ∈ Finset.range 4, profile s t P.card i := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro i _ hi
      exact h i (by simpa [Finset.mem_range] using hi)
    rw [split]
    norm_num [Finset.sum_range_succ, profile, hd]
    linarith
private theorem profile_antitone {s t : ℝ} (ht : 0 ≤ t) (hts : t ≤ s) (d : ℕ) :
    Antitone (profile s t d) := by
  intro i j h
  unfold profile
  split_ifs <;> first | omega | linarith
private noncomputable def selectedWeight (s t : ℝ) (T : Finset ℕ) (i : ℕ) : ℝ :=
  if i ∈ T then profile s t 4 ((Finset.range i).filter (· ∈ T)).card else 0
private noncomputable def coefficient (s t : ℝ) (d j : ℕ) (T : Finset ℕ) (i : ℕ) : ℝ :=
  selectedWeight s t T i - (if j = 3 then 3*s else 1) * profile s t d i
private def eliminate (k d j : ℕ) (T : Finset ℕ) : Prop :=
  (k = 5 ∧ d = 5 ∧ j = 3 ∧ 3 ∈ T ∧ 4 ∈ T) ∨
    (k = 6 ∧ d = 6 ∧ ((j = 3 ∧ 4 ∈ T ∧ 5 ∈ T) ∨
      (j = 4 ∧ ((Finset.range 3).filter (· ∈ T)).card = 1)))
private instance (k d j : ℕ) (T : Finset ℕ) : Decidable (eliminate k d j T) := by
  unfold eliminate
  infer_instance
private theorem eliminate_spec {k d j : ℕ} {T : Finset ℕ}
    (h : eliminate k d j T) : k = d ∧ 5 ≤ d := by
  rcases h with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ <;> decide
private noncomputable def remaining (s t : ℝ) (d j : ℕ) (T : Finset ℕ) (i : ℕ) : ℝ :=
  if i = d-1 then 0 else coefficient s t d j T i +
    coefficient s t d j T (d-1) * profile s t d (i+1)

set_option maxHeartbeats 6000000 in
/-- The finite cases concern only the ranks in a predecessor clique. In an
elimination case, every mandatory predecessor can shift by one position. -/
private theorem profile_budget {k d j : ℕ} (hk : k = 5 ∨ k = 6)
    (hj : 3 ≤ j) (hjd : j ≤ d) (hjk : j < k) (hdk : d ≤ k)
    (T : Finset ℕ) (hT : T ⊆ Finset.range d) (hTcard : T.card = j)
    {s : ℝ} (hs : 1/4 ≤ s) (hst : s ≤ 1/3)
    (hsix : k = 5 → 12*s^2 = 1 ∧ 2/7 ≤ s ∧ s ≤ 3/10)
    (hseven : k = 6 → 9*s^2 - 10*s + 2 = 0 ∧ s ≤ 5/19) :
    let t := 1 - 3*s
    let e := if j = 3 then 3*s else 1
    if eliminate k d j T then
      0 ≤ coefficient s t d j T (d-1) ∧
      (∑ i ∈ Finset.range d, max (-(remaining s t d j T i)) 0) +
        s * (e + coefficient s t d j T (d-1)) ≤ 1-s
    else (∑ i ∈ Finset.range d, max (-(coefficient s t d j T i)) 0) + s*e ≤ 1-s := by
  classical
  have he : (Finset.range d).filter (· ∈ T) = T := by
    ext i
    exact ⟨fun h => (Finset.mem_filter.mp h).2, fun h => Finset.mem_filter.mpr ⟨hT h, h⟩⟩
  rw [← he] at hTcard ⊢
  clear he
  have hp : (k = 5 ∧ 12*s^2 = 1 ∧ 2/7 ≤ s ∧ s ≤ 3/10) ∨
      (k = 6 ∧ 9*s^2 - 10*s + 2 = 0 ∧ 1/4 ≤ s ∧ s ≤ 5/19) := by
    rcases hk with hk | hk
    · exact Or.inl ⟨hk, hsix hk⟩
    · exact Or.inr ⟨hk, (hseven hk).1, hs, (hseven hk).2⟩
  have hd : 3 ≤ d := hj.trans hjd
  rcases hp with ⟨rfl, hq, hlow, hhigh⟩ | ⟨rfl, hq, hlow, hhigh⟩ <;> interval_cases d <;>
    by_cases h0 : 0 ∈ T <;> by_cases h1 : 1 ∈ T <;> by_cases h2 : 2 ∈ T <;>
    by_cases h3 : 3 ∈ T <;> by_cases h4 : 4 ∈ T <;>
    (first | have h5 : 5 ∉ T := fun h => by have := Finset.mem_range.mp (hT h); omega
           | by_cases h5 : 5 ∈ T) <;>
    norm_num [Finset.range_add_one, Finset.filter_insert, Finset.filter_singleton, h0, h1, h2, h3, h4, h5,
      Finset.card_insert_of_notMem] at hTcard
  all_goals
    subst j <;> norm_num at hj <;> norm_num at hjd <;> norm_num at hjk <;>
      simp only [Finset.sum_range_succ, Finset.sum_range_zero] <;>
      norm_num [Finset.range_add_one, Finset.filter_insert, Finset.filter_singleton, h0, h1, h2, h3,
        h4, h5, Finset.card_insert_of_notMem, eliminate, remaining, coefficient, selectedWeight,
        profile] <;> ring_nf <;> try simp (disch := nlinarith only [hs, hst, hq, hlow, hhigh]) [max_def]
  all_goals (try constructor) <;> (try split_ifs) <;> nlinarith
private theorem position_image {G : SimpleGraph V} (O : Predecessors G)
    {S Q : Finset V} (hSQ : S ⊆ Q) {x : V} (hx : x ∈ Q) :
    ((Finset.range (position O Q x)).filter (· ∈ S.image (position O Q))).card =
      position O S x := by
  have h : (Finset.range (position O Q x)).filter (fun i : ℕ => i ∈ S.image (position O Q)) =
      (S.filter (fun z => O.rank z < O.rank x)).image (position O Q) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hi, z, hz, rfl⟩
      refine ⟨z, ⟨hz, ?_⟩, rfl⟩
      by_contra! hr
      rcases hr.eq_or_lt with he | hlt
      · exact hi.ne (congrArg (position O Q) (O.injective he.symm))
      · exact (position_strict O hx hlt).asymm hi
    · rintro ⟨z, ⟨hzS, hzx⟩, rfl⟩
      exact ⟨position_strict O (hSQ hzS) hzx, z, hzS, rfl⟩
  exact h ▸ (Finset.card_image_of_injOn ((position_injective O Q).mono fun _ hz =>
    hSQ (Finset.mem_filter.mp hz).1))
private theorem position_one_insertion [DecidableEq V] {G : SimpleGraph V} (O : Predecessors G)
    {Q B : Finset V} {a : V} (ha : a ∈ Q) (hBA : Q.erase a ⊆ B)
    (hcard : B.card ≤ Q.card) {x : V} :
    position O B x ≤ position O Q x + 1 := by
  have he : (B \ (Q.erase a)).card ≤ 1 := by
    rw [Finset.card_sdiff_of_subset hBA]
    have h := Finset.card_erase_add_one ha
    omega
  have hsub : B.filter (fun y => O.rank y < O.rank x) ⊆
      Q.filter (fun y => O.rank y < O.rank x) ∪ (B \ (Q.erase a)) := by
    intro y hy
    obtain ⟨hyB, hyx⟩ := Finset.mem_filter.mp hy
    by_cases hz : y ∈ Q.erase a
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase hz, hyx⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hyB, hz⟩)
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by
    change position O Q x + (B \ (Q.erase a)).card ≤ _
    omega))
private theorem align_sum {F : Type*} [AddCommMonoid F] [DecidableEq V]
    {S P Q : Finset V} (hSP : S ⊆ P) (hSQ : S ⊆ Q) {w b : V → ℝ}
    (hw : ∀ x ∈ P, x ∉ S → w x = 0) (hb : ∀ x ∈ Q, b x = if x ∈ S then w x else 0)
    (f : V → ℝ → F) (hf : ∀ x, f x 0 = 0) :
    ∑ x ∈ P, f x (w x) = ∑ x ∈ Q, f x (b x) := by
  rw [← Finset.sum_subset hSP (f := fun x => f x (w x)), ← sum_extend hSQ]
  · exact Finset.sum_congr rfl fun x hx => by rw [hb x hx]; by_cases h : x ∈ S <;> simp [h, hf]
  · intro x hx hnot
    rw [hw x hx hnot, hf]
private theorem profile_fit {G : SimpleGraph V} (O : Predecessors G) {k : ℕ}
    (hk : k = 5 ∨ k = 6) (hcard : ∀ v, (O.set v).card ≤ k) {R s ε : ℝ}
    (hε : 0 ≤ ε) (hR : 2 ≤ R) (hsD : s * (R+1) = 1) (hs : 1/4 ≤ s) (hst : s ≤ 1/3)
    (hsix : k = 5 → 12*s^2 = 1 ∧ 2/7 ≤ s ∧ s ≤ 3/10)
    (hseven : k = 6 → 9*s^2 - 10*s + 2 = 0 ∧ s ≤ 5/19)
    (g : V → V → E) (hskew : ∀ x y, g y x = -g x y)
    (htri : ∀ x y z, G.Adj x y → G.Adj y z → G.Adj x z → ‖defect g x y z‖ ≤ ε) :
    ∃ p : V → E, ∀ x y, G.Adj x y → ‖residual g p x y‖ ≤ R * ε := by
  classical
  let t := 1 - 3*s
  have hpos : 0 < s := by linarith
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hts : t ≤ s := by dsimp [t]; linarith
  let w (v x : V) := profile s t (O.set v).card (position O (O.set v) x)
  have htotal (v : V) (hv : (O.set v).Nonempty) : ∑ x ∈ O.set v, w v x = 1 :=
    profile_total O hv (by dsimp [t]; ring)
  have hnonneg (v x : V) : 0 ≤ w v x := by
    unfold w profile
    split_ifs <;> positivity
  apply ordered_fit O w g hskew htri htotal (fun v x _ => hnonneg v x)
  intro r v c hc hold hz
  let P := O.set v
  let Q := O.set c
  let S := P.filter fun x => O.rank x < O.rank c
  let j := position O P c
  let d := Q.card
  by_cases hP : P.card ≤ 3
  · apply direct_step hold hc hε (htotal v ⟨c, hc⟩) (fun x _ => hnonneg v x)
    have hP0 : 0 < (P.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr ⟨c, hc⟩
    have hP3 : (P.card : ℝ) ≤ 3 := by exact_mod_cast hP
    simp only [w, profile, show (O.set v).card ≤ 3 from hP, ite_true]
    have hi : 1 ≤ (1 / (P.card : ℝ)) * (R+1) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hP0]
      linarith
    nlinarith only [hi]
  by_cases hj : j < 3
  · apply direct_step hold hc hε (htotal v ⟨c, hc⟩) (fun x _ => hnonneg v x)
    change (1 - profile s t P.card j) * (R+1) ≤ R
    simp only [profile, hP, ite_false, hj, ite_true]
    nlinarith only [hsD]
  have hSQ : S ⊆ Q := fun x hx =>
    let h := Finset.mem_filter.mp hx
    O.earlier h.1 hc h.2
  let T := S.image (position O Q)
  have hT : T ⊆ Finset.range d := by
    intro i hi
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_range.mpr (position_lt O (hSQ hx))
  have hTcard : T.card = j := by
    rw [Finset.card_image_of_injOn ((position_injective O Q).mono hSQ)]
    rfl
  have hjd : j ≤ d := Finset.card_le_card hSQ
  have hjk : j < k := (position_lt O hc).trans_le (hcard v)
  let b (x : V) := selectedWeight s t T (position O Q x)
  have hb (x : V) (hx : x ∈ Q) : b x = if x ∈ S then w v x else 0 := by
    have he : position O Q x ∈ T ↔ x ∈ S := by
      refine ⟨?_, fun h => Finset.mem_image.mpr ⟨x, h, rfl⟩⟩
      rintro h
      obtain ⟨y, hy, he⟩ := Finset.mem_image.mp h
      rwa [position_injective O Q (hSQ hy) hx he] at hy
    by_cases hxS : x ∈ S
    · have hxold := (Finset.mem_filter.mp hxS).2
      change selectedWeight s t T (position O Q x) =
        (if x ∈ S then profile s t P.card (position O P x) else 0)
      rw [selectedWeight, ite_eq_left (he.mpr hxS), ite_eq_left hxS]
      rw [show ((Finset.range (position O Q x)).filter (· ∈ T)).card =
        position O S x from position_image O hSQ hx, position_prefix O P hxold]
      simp [profile, hP]
    · simp only [b, selectedWeight, not_congr he |>.mpr hxS, ite_false, hxS]
  have hSE : S ⊆ P.erase c := fun x hx =>
    let h := Finset.mem_filter.mp hx
    Finset.mem_erase.mpr ⟨fun e => h.2.ne (congrArg O.rank e), h.1⟩
  have hw0 (x : V) (hx : x ∈ P.erase c) (hxS : x ∉ S) : w v x = 0 := by
    have hn : ¬ O.rank x < O.rank c :=
      fun h => hxS (Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase hx, h⟩)
    have hr := lt_of_le_of_ne (le_of_not_gt hn)
      (fun he => Finset.ne_of_mem_erase hx (O.injective he.symm))
    have hp : j < position O P x := position_strict O hc hr
    change profile s t P.card (position O P x) = 0
    simp [profile, hP, show ¬ position O P x < 3 by omega, show position O P x ≠ 3 by omega]
  let μ : ℝ := if j = 3 then 3*s else 1
  have hμ : 1 - w v c = μ := by
    change 1 - profile s t P.card j = μ
    by_cases h : j = 3 <;> simp [profile, hP, hj, h, μ, t]
  let h (x : V) := coefficient s t d j T (position O Q x)
  have hformula (x : V) : h x = b x - μ*w c x := rfl
  have hQ : Q.Nonempty := Finset.card_pos.mp (by omega)
  have hz' : ∑ x ∈ Q, h x • r c x = ∑ x ∈ Q, b x • r c x := by
    simp only [hformula, sub_smul, Finset.sum_sub_distrib, ← smul_smul, ← Finset.smul_sum,
      show (∑ x ∈ Q, w c x • r c x) = 0 from hz c hQ, smul_zero, sub_zero]
  have hmassV : ∑ x ∈ Q, b x = μ := by
    have ha : (∑ x ∈ P.erase c, w v x) = ∑ x ∈ Q, b x :=
      align_sum hSE hSQ hw0 hb (fun _ z => z) (fun _ => rfl)
    rw [← ha]
    have h := P.sum_erase_add (w v) hc
    rw [htotal v ⟨c, hc⟩] at h
    linarith only [h, hμ]
  have hh : ∑ x ∈ Q, h x = 0 := by
    simp only [hformula, Finset.sum_sub_distrib, ← Finset.mul_sum, hmassV]
    rw [show (∑ x ∈ Q, w c x) = 1 from htotal c hQ, mul_one, sub_self]
  have hD : 0 ≤ (R+1)*ε := mul_nonneg (by linarith) hε
  have hcold := ((O.mem _ _).mp hc).1
  have hbudget := profile_budget hk (by omega : 3 ≤ j) hjd hjk (hcard c) T hT hTcard hs hst hsix hseven
  change ‖∑ x ∈ P.erase c, w v x • r c x‖ + (1 - w v c)*ε ≤ _
  have ha : (∑ x ∈ P.erase c, w v x • r c x) = ∑ x ∈ Q, b x • r c x :=
    align_sum hSE hSQ hw0 hb (fun x z => z • r c x) (fun _ => zero_smul _ _)
  rw [ha, ← hz', hμ]
  have hclose {M charge : ℝ} (hb : M + s*(μ+charge) ≤ 1-s)
      (hn : ‖∑ x ∈ Q, h x • r c x‖ ≤ M*((R+1)*ε) + charge*ε) :
      ‖∑ x ∈ Q, h x • r c x‖ + μ*ε ≤ R*ε := by
    have hb' : M*(R+1) + (μ+charge) ≤ R := by
      apply le_of_mul_le_mul_left _ hpos
      nlinarith only [hb, hsD, congrArg (· * M) hsD]
    nlinarith only [hn, mul_le_mul_of_nonneg_right hb' hε]
  by_cases he : eliminate k d j T
  · obtain ⟨hek, hd⟩ := eliminate_spec he
    simp only [he, ite_true] at hbudget
    obtain ⟨a, ha, hpa⟩ := Finset.mem_image.mp (by
      rw [positions]; exact Finset.mem_range.mpr (by omega : d-1 < d) :
      d-1 ∈ Q.image (position O Q))
    have hQa : Q.erase a ⊆ O.set a := by
      intro x hx
      have hxQ := Finset.mem_of_mem_erase hx
      have hp := position_lt O hxQ
      have hr : O.rank x < O.rank a := by
        by_contra! hn
        have hlt := lt_of_le_of_ne hn (fun heq => Finset.ne_of_mem_erase hx (O.injective heq.symm))
        have := position_strict O ha hlt
        omega
      exact O.earlier hxQ ha hr
    have haNonempty : (O.set a).Nonempty := Finset.card_pos.mp (by
      have := Finset.card_le_card hQa
      have := Finset.card_erase_add_one ha
      omega)
    have hala : 0 ≤ h a := by simpa only [h, hpa] using hbudget.1
    refine hclose (M := ∑ i ∈ Finset.range d, max (-(remaining s t d j T i)) 0)
      (charge := h a) (by simpa only [h, hpa] using hbudget.2) ?_
    refine (second_identity hold (by linarith) hε hcold ha hh hala
      (fun x _ => hnonneg a x) (htotal a haNonempty) (hz a haNonempty)
      (fun x hx hn => hQa (Finset.mem_erase.mpr ⟨fun e => hn.not_ge (by simpa only [e] using hala), hx⟩))).trans ?_
    apply add_le_add_left
    apply mul_le_mul_of_nonneg_right _ hD
    rw [← positions O Q, Finset.sum_image (position_injective O Q)]
    apply Finset.sum_le_sum
    intro x hx
    by_cases hxa : x = a
    · subst x
      have hna : a ∉ O.set a := fun ha => (lt_irrefl _) ((O.mem _ _).mp ha).1
      simp [hna, remaining, hpa]
    · have hxB := hQa (Finset.mem_erase.mpr ⟨hxa, hx⟩)
      have hdim : 3 < (O.set a).card := by
        have hc := Finset.card_le_card hQa
        have he' := Finset.card_erase_add_one ha
        change 5 ≤ Q.card at hd
        omega
      have hp := position_one_insertion O ha hQa (show (O.set a).card ≤ d from hek ▸ hcard a) (x := x)
      have hw : profile s t d (position O Q x + 1) ≤ w a x := by
        simpa only [w, profile, Nat.not_le.mpr hdim, show ¬ d ≤ 3 by omega, ite_false] using
          profile_antitone ht hts (O.set a).card hp
      have hdne : position O Q x ≠ d-1 := fun e =>
        hxa (position_injective O Q hx ha (e.trans hpa.symm))
      simp only [ite_eq_right hxa, ite_eq_left hxB, remaining, ite_eq_right hdne]
      rw [← hpa]
      change max (-(h x + h a * w a x)) 0 ≤
        max (-(h x + h a * profile s t d (position O Q x + 1))) 0
      exact max_le_max_right _ (neg_le_neg (add_le_add le_rfl (mul_le_mul_of_nonneg_left hw hala)))
  · simp only [he, ite_false] at hbudget
    refine hclose (M := ∑ i ∈ Finset.range d, max (-(coefficient s t d j T i)) 0) (charge := 0)
      (by simpa only [zero_add, add_zero] using hbudget) ?_
    rw [← positions O Q, Finset.sum_image (position_injective O Q), zero_mul, add_zero]
    simpa using balanced_norm (e := fun _ => 0) hh hD (fun _ _ => le_rfl)
      (fun x hx y hy _ _ => by simpa using hold.diameter hε (by linarith) hcold hx hy)
end MultiIdentity
open MultiIdentity
/-- The old triangle of the newest predecessor bounds the difference of the two
residuals left after using its retained identity. -/
theorem IsChordal.exists_regrouped_simplicial_banach_gain_potential
    {V : Type*} [Finite V] {G : SimpleGraph V} (hG : G.IsChordal)
    (k : ℕ) (hk : 2 ≤ k) (hclique : ∀ C : Set V, G.IsClique C → C.ncard ≤ k + 1)
    (R : ℝ) (hmin : max 1 ((k : ℝ) - 2) ≤ R) (hmax : R ≤ (k : ℝ) - 1)
    (hquad : 2 * ((k : ℝ) - 1) ≤ R * (R + 1))
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε) (hskew : ∀ x y, g y x = -g x y)
    (htri : ∀ x y z, G.Adj x y → G.Adj y z → G.Adj x z → ‖g x y + g y z - g x z‖ ≤ ε) :
    ∃ φ : V → E, ∀ u v, G.Adj u v → ‖g u v - (φ v - φ u)‖ ≤ R * ε := by
  classical
  obtain ⟨O⟩ := predecessor_order hG
  exact regroup_fit O hk (O.card_le hclique) hε ((le_max_left _ _).trans hmin)
    ((le_max_right _ _).trans hmin) hmax hquad g hskew htri
/-- Two retained weighted identities give a radius of `2 * sqrt 3 - 1`. -/
theorem IsChordal.exists_multiIdentity_cliqueSix_banach_gain_potential
    {V : Type*} [Finite V] {G : SimpleGraph V} (hG : G.IsChordal)
    (hclique : ∀ C : Set V, G.IsClique C → C.ncard ≤ 6)
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε) (hskew : ∀ x y, g y x = -g x y)
    (htri : ∀ x y z, G.Adj x y → G.Adj y z → G.Adj x z → ‖g x y + g y z - g x z‖ ≤ ε) :
    ∃ φ : V → E, ∀ u v, G.Adj u v → ‖g u v - (φ v - φ u)‖ ≤ (2 * Real.sqrt 3 - 1) * ε := by
  classical
  obtain ⟨O⟩ := predecessor_order hG
  let x := Real.sqrt 3
  let s := 1 / (2*x)
  have hsq : x^2 = 3 := Real.sq_sqrt (by norm_num)
  have hx : 0 ≤ x := Real.sqrt_nonneg _
  have hl : 5/3 ≤ x := by nlinarith
  have hu : x ≤ 7/4 := by nlinarith
  have hp : 0 < 2*x := by linarith
  have hsD : s*(2*x) = 1 := div_mul_cancel₀ _ hp.ne'
  have hsL : 2/7 ≤ s := (le_div_iff₀ hp).mpr (by linarith)
  have hsU : s ≤ 3/10 := (div_le_iff₀ hp).mpr (by linarith)
  have hsQ : 12*s^2 = 1 := by dsimp [s]; field_simp; nlinarith
  exact profile_fit O (k := 5) (Or.inl rfl) (O.card_le hclique) hε (by linarith)
    (by convert hsD using 1 <;> ring) (by linarith) (by linarith)
    (fun _ => ⟨hsQ, hsL, hsU⟩) (by omega) g hskew htri
/-- Two retained weighted identities bound the gain error for clique size seven. -/
theorem IsChordal.exists_multiIdentity_cliqueSeven_banach_gain_potential
    {V : Type*} [Finite V] {G : SimpleGraph V} (hG : G.IsChordal)
    (hclique : ∀ C : Set V, G.IsClique C → C.ncard ≤ 7)
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε) (hskew : ∀ x y, g y x = -g x y)
    (htri : ∀ x y z, G.Adj x y → G.Adj y z → G.Adj x z → ‖g x y + g y z - g x z‖ ≤ ε) :
    ∃ φ : V → E, ∀ u v, G.Adj u v → ‖g u v - (φ v - φ u)‖ ≤ ((3 + Real.sqrt 7) / 2) * ε := by
  classical
  obtain ⟨O⟩ := predecessor_order hG
  let x := Real.sqrt 7
  let R := (3+x)/2
  let s := (5-x)/9
  have hsq : x^2 = 7 := Real.sq_sqrt (by norm_num)
  have hx : 0 ≤ x := Real.sqrt_nonneg _
  have hl : 50/19 ≤ x := by nlinarith
  have hu : x ≤ 11/4 := by nlinarith
  have hsD : s*(R+1) = 1 := by dsimp [s, R]; nlinarith
  have hsQ : 9*s^2 - 10*s + 2 = 0 := by dsimp [s]; nlinarith
  exact profile_fit O (k := 6) (Or.inr rfl) (O.card_le hclique) hε (by dsimp [R]; linarith)
    hsD (by dsimp [s]; linarith) (by dsimp [s]; linarith)
    (by omega) (fun _ => ⟨hsQ, by dsimp [s]; linarith⟩) g hskew htri
end SimpleGraph

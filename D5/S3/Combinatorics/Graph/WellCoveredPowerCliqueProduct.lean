/- GID: D5/S3/Combinatorics/Graph/WellCoveredPowerCliqueProduct
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/WellCoveredPowerCliqueProduct
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Prod, mathlib/module/Mathlib.Combinatorics.SimpleGraph.Diam]
   utility: none
   digest: Clique products preserve well-covered powers and increase diameter, refuting the diameter bound. -/

import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Finite
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Fintype.Powerset

open SimpleGraph

namespace WellCoveredPowerCliqueProduct

noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

def power (G : SimpleGraph V) (d : ℕ) : SimpleGraph V where
  Adj u v := u ≠ v ∧ G.dist u v ≤ d
  symm := ⟨by intro u v h; exact ⟨h.1.symm, by simpa [G.dist_comm] using h.2⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

def IsMaximalIndep (G : SimpleGraph V) (I : Finset V) : Prop :=
  (∀ u ∈ I, ∀ v ∈ I, u ≠ v → ¬ G.Adj u v) ∧
  (∀ v ∉ I, ∃ u ∈ I, G.Adj v u)

def WellCovered (G : SimpleGraph V) : Prop :=
  ∀ I J : Finset V, IsMaximalIndep G I → IsMaximalIndep G J → I.card = J.card

def WCP (G : SimpleGraph V) : Prop :=
  G.Connected ∧ ∀ d : ℕ, 1 ≤ d → WellCovered (power G d)

omit [Fintype V] [DecidableEq V] in
theorem distance_cliqueProduct {G : SimpleGraph V} (h : G.Connected) {t : ℕ}
    (x y : V × Fin t) :
    (G □ (⊤ : SimpleGraph (Fin t))).dist x y =
      G.dist x.1 y.1 + (if x.2 = y.2 then 0 else 1) := by
  classical
  rw [SimpleGraph.dist, SimpleGraph.edist_boxProd]
  rw [ENat.toNat_add (SimpleGraph.edist_ne_top_iff_reachable.mpr (h x.1 y.1)) (by rw [SimpleGraph.edist_top]; split_ifs <;> simp)]
  change G.dist x.1 y.1 + (⊤ : SimpleGraph (Fin t)).dist x.2 y.2 = _
  rw [SimpleGraph.dist_top]

omit [Fintype V] in
theorem projection_injective {G : SimpleGraph V} (hc : G.Connected) {t d : ℕ}
    (hd : 1 ≤ d) {I : Finset (V × Fin t)}
    (hI : IsMaximalIndep (power (G □ (⊤ : SimpleGraph (Fin t))) d) I) :
    Set.InjOn Prod.fst (I : Set (V × Fin t)) := by
  intro x hx y hy he
  by_contra hn
  apply hI.1 x hx y hy hn
  refine ⟨hn, ?_⟩
  rw [distance_cliqueProduct hc, he]
  simp only [SimpleGraph.dist_self, zero_add]
  split_ifs <;> omega

theorem projection_maximal {G : SimpleGraph V} (hc : G.Connected) {t d : ℕ}
    (ht : Fintype.card V < t) (hd : 1 ≤ d) {I : Finset (V × Fin t)}
    (hI : IsMaximalIndep (power (G □ (⊤ : SimpleGraph (Fin t))) d) I) :
    IsMaximalIndep (power G (d - 1)) (I.image Prod.fst) := by
  classical
  have hinj := projection_injective hc hd hI
  have hcard : I.card ≤ Fintype.card V := by
    rw [← Finset.card_image_of_injOn hinj]
    exact Finset.card_le_univ _
  constructor
  · intro u hu v hv huv hadj
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
    apply hI.1 x hx y hy (fun h => huv (congrArg Prod.fst h))
    refine ⟨fun h => huv (congrArg Prod.fst h), ?_⟩
    rw [distance_cliqueProduct hc]
    have hdist := hadj.2
    split_ifs <;> omega
  · intro w hw
    by_contra hn
    have hfar : ∀ x ∈ I, d ≤ G.dist w x.1 := by
      intro x hx
      have hne : w ≠ x.1 := by
        intro he
        apply hw
        exact Finset.mem_image.mpr ⟨x, hx, he.symm⟩
      have hn' : ¬ (power G (d - 1)).Adj w x.1 := by
        intro ha
        exact hn ⟨x.1, Finset.mem_image.mpr ⟨x, hx, rfl⟩, ha⟩
      change ¬ (w ≠ x.1 ∧ G.dist w x.1 ≤ d - 1) at hn'
      have hn'' : ¬ G.dist w x.1 ≤ d - 1 := fun hle => hn' ⟨hne, hle⟩
      omega
    have hlabel : (I.image Prod.snd).card < (Finset.univ : Finset (Fin t)).card := by
      have := Finset.card_image_le (s := I) (f := Prod.snd)
      simpa using lt_of_le_of_lt (le_trans this hcard) ht
    obtain ⟨a, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hlabel
    have hnew : (w, a) ∉ I := by
      intro hx
      exact hw (Finset.mem_image.mpr ⟨(w, a), hx, rfl⟩)
    obtain ⟨x, hx, hadj⟩ := hI.2 (w, a) hnew
    have hne : a ≠ x.2 := by
      intro he
      exact ha (Finset.mem_image.mpr ⟨x, hx, he.symm⟩)
    have hdist := hadj.2
    rw [distance_cliqueProduct hc] at hdist
    simp only [hne, ↓reduceIte] at hdist
    have := hfar x hx
    omega

theorem wellCovered_power_zero {G : SimpleGraph V} (hc : G.Connected) :
    WellCovered (power G 0) := by
  classical
  have hall : ∀ I, IsMaximalIndep (power G 0) I → I = Finset.univ := by
    intro I hI
    apply Finset.eq_univ_of_forall
    intro v
    by_contra hv
    obtain ⟨u, _, ha⟩ := hI.2 v hv
    exact ha.1 ((hc.dist_eq_zero_iff).mp (Nat.le_zero.mp ha.2))
  intro I J hI hJ
  rw [hall I hI, hall J hJ]

theorem wcp_cliqueProduct {G : SimpleGraph V} (h : WCP G) {t : ℕ}
    (ht : Fintype.card V < t) : WCP (G □ (⊤ : SimpleGraph (Fin t))) := by
  classical
  have hp : 0 < t := lt_of_le_of_lt (Nat.zero_le _) ht
  let : NeZero t := ⟨Nat.ne_of_gt hp⟩
  refine ⟨h.1.boxProd SimpleGraph.connected_top, ?_⟩
  intro d hd I J hI hJ
  have hbase : WellCovered (power G (d - 1)) := by
    by_cases hd' : d = 1
    · simpa [hd'] using wellCovered_power_zero h.1
    · exact h.2 (d - 1) (by omega)
  have hc := hbase _ _ (projection_maximal h.1 ht hd hI)
    (projection_maximal h.1 ht hd hJ)
  simpa only [Finset.card_image_of_injOn (projection_injective h.1 hd hI),
    Finset.card_image_of_injOn (projection_injective h.1 hd hJ)] using hc

omit [DecidableEq V] in
theorem diam_cliqueProduct {G : SimpleGraph V} (h : G.Connected) {t : ℕ}
    (ht : 2 ≤ t) : (G □ (⊤ : SimpleGraph (Fin t))).diam = G.diam + 1 := by
  classical
  have : Nonempty V := h.nonempty
  have : NeZero t := ⟨by omega⟩
  have hc : (G □ (⊤ : SimpleGraph (Fin t))).Connected :=
    h.boxProd SimpleGraph.connected_top
  have hf := (SimpleGraph.connected_iff_ediam_ne_top).mp h
  have hpf := (SimpleGraph.connected_iff_ediam_ne_top).mp hc
  apply Nat.le_antisymm
  · obtain ⟨x, y, hxy⟩ := (G □ (⊤ : SimpleGraph (Fin t))).exists_dist_eq_diam
    rw [← hxy, distance_cliqueProduct h]
    have := G.dist_le_diam hf (u := x.1) (v := y.1)
    split_ifs <;> omega
  · obtain ⟨u, v, huv⟩ := G.exists_dist_eq_diam
    let a : Fin t := ⟨0, by omega⟩
    let b : Fin t := ⟨1, by omega⟩
    have hab : a ≠ b := by intro he; have := congrArg Fin.val he; simp [a, b] at this
    have hh := (G □ (⊤ : SimpleGraph (Fin t))).dist_le_diam hpf (u := (u, a)) (v := (v, b))
    rw [distance_cliqueProduct h, huv] at hh
    simpa [hab] using hh


instance (G : SimpleGraph V) [DecidableRel G.Adj] (I : Finset V) :
    Decidable (IsMaximalIndep G I) := by
  unfold IsMaximalIndep; infer_instance

theorem distance_certificate {V : Type*} [Nonempty V] (G : SimpleGraph V)
    (m : V → V → ℕ)
    (hz : ∀ u v, m u v = 0 ↔ u = v)
    (he : ∀ u v w, G.Adj u v → m u w ≤ m v w + 1)
    (hd : ∀ u v, m u v ≠ 0 → ∃ w, G.Adj u w ∧ m w v + 1 = m u v) :
    G.Connected ∧ ∀ u v, G.dist u v = m u v := by
  have walks : ∀ n u v, m u v = n → ∃ p : G.Walk u v, p.length = n := by
    intro n
    induction n with
    | zero =>
      intro u v huv
      have huv' := (hz u v).mp huv
      subst v
      exact ⟨.nil, rfl⟩
    | succ n ih =>
      intro u v huv
      obtain ⟨w, huw, hwv⟩ := hd u v (by omega)
      obtain ⟨p, hp⟩ := ih w v (by omega)
      exact ⟨p.cons huw, by simp [hp]⟩
  have conn : G.Connected := by
    rw [SimpleGraph.connected_iff]
    exact ⟨fun u v => ⟨(walks (m u v) u v rfl).choose⟩, inferInstance⟩
  refine ⟨conn, fun u v => ?_⟩
  have lower : ∀ {a b} (p : G.Walk a b), m a b ≤ p.length := by
    intro a b p
    induction p with
    | nil => simp [(hz _ _).mpr rfl]
    | @cons a b c hab p ih =>
      have h := he a b c hab
      simp only [Walk.length_cons]
      omega
  obtain ⟨p, hp⟩ := walks (m u v) u v rfl
  apply le_antisymm
  · simpa [hp] using G.dist_le p
  · obtain ⟨q, hq⟩ := conn.exists_walk_length_eq_dist u v
    simpa [hq] using lower q

def cycleMetric (n : ℕ) (u v : Fin n) : ℕ :=
  min (Nat.dist u.val v.val) (n - Nat.dist u.val v.val)

def cycle (n : ℕ) : SimpleGraph (Fin n) where
  Adj u v := cycleMetric n u v = 1
  symm := ⟨by intro u v; simp [cycleMetric, Nat.dist_comm]⟩
  loopless := ⟨by intro u; simp [cycleMetric]⟩

instance (n : ℕ) : DecidableRel (cycle n).Adj := by
  dsimp [cycle]; infer_instance

theorem cycle_seven_metric : (cycle 7).Connected ∧
    ∀ u v, (cycle 7).dist u v = cycleMetric 7 u v := by
  apply distance_certificate
  · decide +kernel
  · decide +kernel
  · decide +kernel


def metricPower (n d : ℕ) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ cycleMetric n u v ≤ d
  symm := ⟨by intro u v h; exact ⟨h.1.symm, by simpa [cycleMetric, Nat.dist_comm] using h.2⟩⟩
  loopless := ⟨by simp⟩

instance (n d : ℕ) : DecidableRel (metricPower n d).Adj := by
  dsimp [metricPower]; infer_instance

theorem cycle_seven_power (d : ℕ) : power (cycle 7) d = metricPower 7 d := by
  ext u v
  simp only [power, metricPower, cycle_seven_metric.2 u v]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
theorem cycle_seven_card_one :
    ∀ I : Finset (Fin 7), IsMaximalIndep (metricPower 7 1) I → I.card = 3 := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
theorem cycle_seven_card_two :
    ∀ I : Finset (Fin 7), IsMaximalIndep (metricPower 7 2) I → I.card = 2 := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
theorem cycle_seven_card_three :
    ∀ I : Finset (Fin 7), IsMaximalIndep (metricPower 7 3) I → I.card = 1 := by
  decide +kernel

theorem cycle_seven_wcp : WCP (cycle 7) := by
  refine ⟨cycle_seven_metric.1, fun d hd => ?_⟩
  rw [cycle_seven_power]
  rcases eq_or_lt_of_le hd with h | h
  · subst d
    intro I J hi hj
    rw [cycle_seven_card_one I hi, cycle_seven_card_one J hj]
  · by_cases h2 : d = 2
    · subst d
      intro I J hi hj
      rw [cycle_seven_card_two I hi, cycle_seven_card_two J hj]
    · have hd3 : 3 ≤ d := by omega
      have heq : metricPower 7 d = metricPower 7 3 := by
        have hb : ∀ u v : Fin 7, cycleMetric 7 u v ≤ 3 := by decide +kernel
        ext u v
        simp only [metricPower]
        constructor
        · intro huv; exact ⟨huv.1, hb _ _⟩
        · intro huv; exact ⟨huv.1, (hb _ _).trans hd3⟩
      rw [heq]
      intro I J hi hj
      rw [cycle_seven_card_three I hi, cycle_seven_card_three J hj]

theorem cycle_seven_diam : (cycle 7).diam = 3 := by
  have hb : ∀ u v : Fin 7, cycleMetric 7 u v ≤ 3 := by decide +kernel
  apply le_antisymm
  · obtain ⟨u, v, huv⟩ := (cycle 7).exists_dist_eq_diam
    rw [← huv, cycle_seven_metric.2 u v]
    exact hb u v
  · have h := (cycle 7).dist_le_diam ((cycle 7).connected_iff_ediam_ne_top.mp cycle_seven_metric.1) (u := (0 : Fin 7)) (v := (3 : Fin 7))
    rw [cycle_seven_metric.2] at h
    exact h


theorem exists_wcp_diameter (D : ℕ) (hD : 3 ≤ D) :
    ∃ (V : Type) (_hF : Fintype V) (_hE : DecidableEq V) (G : SimpleGraph V),
      WCP G ∧ G.diam = D := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hD
  induction k with
  | zero =>
    exact ⟨Fin 7, inferInstance, inferInstance, cycle 7,
      cycle_seven_wcp, by simpa using cycle_seven_diam⟩
  | succ k ih =>
    obtain ⟨V, hF, hE, G, hG, hdiam⟩ := ih (by omega)
    let := hF
    let := hE
    have : Nonempty V := hG.1.nonempty
    have hp : 0 < Fintype.card V := Fintype.card_pos
    let t := Fintype.card V + 1
    refine ⟨V × Fin t, inferInstance, inferInstance,
      G □ (⊤ : SimpleGraph (Fin t)), wcp_cliqueProduct hG (by dsimp [t]; omega), ?_⟩
    rw [diam_cliqueProduct hG.1 (by dsimp [t]; omega), hdiam]
    omega

def claim : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    WCP G → G.diam ≤ 3

theorem result : ¬ claim := by
  intro h
  obtain ⟨V, hF, hE, G, hG, hdiam⟩ := exists_wcp_diameter 4 (by omega)
  let := hF
  let := hE
  let := Classical.decRel G.Adj
  have := h V G hG
  omega

end

end WellCoveredPowerCliqueProduct

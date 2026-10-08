/- GID: D5/S3/Combinatorics/DihedralRamsey/MonotoneRamseyLayers
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DihedralRamsey/MonotoneRamseyLayers
   mirror-E: none(waiver:longest-monotone-path-layers)
   anchors: [mathlib/module/Mathlib.Order.RelSeries, mathlib/module/Mathlib.Tactic.Linarith]
   utility: none
   digest: Longest increasing paths give bounded edge-increasing labels. -/

import D5.S3.Combinatorics.DihedralRamsey.MonotoneRamseyCopies
import D5.S3.Combinatorics.DihedralRamsey.DihedralRamseyBlocks
import Mathlib.Order.RelSeries
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DihedralRamsey

open DihedralRamseyDefs CyclicRamseyDefs MonotoneRamseyDefs Finset

/-- The longest increasing-path label strictly grows across every forward edge. -/
theorem monotone_path_labels {a n : ℕ} (ha : 2 ≤ a) (G : SimpleGraph (Fin n))
    (havoid : ¬∃ ψ : Fin a → Fin n, StrictMono ψ ∧
      ∀ i j, (monoPath a).Adj i j → G.Adj (ψ i) (ψ j)) :
    ∃ r : Fin n → Fin (a - 1), ∀ u v, u < v → G.Adj u v → r u < r v := by
  classical
  let R : SetRel (Fin n) (Fin n) := {uv | uv.1 < uv.2 ∧ G.Adj uv.1 uv.2}
  have mono : ∀ p : RelSeries R, StrictMono p := by
    intro p
    exact Fin.strictMono_iff_lt_succ.mpr (fun i => (p.step i).1)
  have bound : ∀ p : RelSeries R, p.length < n := by
    intro p
    have h := Fintype.card_le_of_injective p (mono p).injective
    simp only [Fintype.card_fin] at h
    omega
  have short : ∀ p : RelSeries R, p.length < a - 1 := by
    intro p
    by_contra h
    have hp : a - 1 ≤ p.length := by omega
    apply havoid
    let ψ : Fin a → Fin n := fun i => p ⟨i.val, by omega⟩
    have hψ : StrictMono ψ := by
      intro i j hij
      exact mono p (show (⟨i.val, by omega⟩ : Fin (p.length + 1)) < ⟨j.val, by omega⟩
        from hij)
    refine ⟨ψ, hψ, ?_⟩
    intro i j hij
    have hrel := (SimpleGraph.fromRel_adj _ _ _).mp hij
    rcases hrel.2 with h | h
    · have hi : i.val < p.length := by omega
      have hstep := (p.step ⟨i.val, hi⟩).2
      convert hstep using 1
      · rfl
      · exact congrArg p (Fin.ext (by simpa using h))
    · have hj : j.val < p.length := by omega
      have hstep := (p.step ⟨j.val, hj⟩).2
      apply SimpleGraph.Adj.symm
      convert hstep using 1
      · rfl
      · exact congrArg p (Fin.ext (by simpa using h))
  let T : Fin n → Finset ℕ := fun v => (range n).filter fun k =>
    ∃ p : RelSeries R, p.length = k ∧ p.last = v
  have nonempty : ∀ v, (T v).Nonempty := by
    intro v
    refine ⟨0, mem_filter.mpr ⟨mem_range.mpr (Fin.pos v), ?_⟩⟩
    exact ⟨RelSeries.singleton R v, rfl, rfl⟩
  let r : Fin n → Fin (a - 1) := fun v =>
    ⟨(T v).max' (nonempty v), by
      obtain ⟨p, hp, _⟩ := (mem_filter.mp ((T v).max'_mem (nonempty v))).2
      exact hp ▸ short p⟩
  refine ⟨r, ?_⟩
  intro u v huv huvG
  obtain ⟨p, hp, hend⟩ := (mem_filter.mp ((T u).max'_mem (nonempty u))).2
  let q := p.snoc v (show (p.last, v) ∈ R from hend ▸ ⟨huv, huvG⟩)
  have hq : q.length ∈ T v := by
    apply mem_filter.mpr
    exact ⟨mem_range.mpr (bound q), q, rfl, by simp [q]⟩
  have hle := (T v).le_max' q.length hq
  change (T u).max' (nonempty u) < (T v).max' (nonempty v)
  have hlen : q.length = p.length + 1 := by simp [q]
  omega

/-- Above the smaller rectangular label bound, a full opposite-color clique occurs. -/
theorem monotone_full_layer {k d n : ℕ} (hk : 2 ≤ k) (G : SimpleGraph (Fin n))
    (havoid : ¬CyclicEmbeddable (monoPath k) Gᶜ) (r : Fin n → Fin d)
    (hr : ∀ u v, u < v → G.Adj u v → r u < r v) (hn : d * (k - 2) < n) :
    ∃ c : Fin d, (univ.filter fun v => r v = c).card = k - 1 ∧
      Gᶜ.IsClique ((univ.filter fun v => r v = c) : Set (Fin n)) := by
  classical
  have clique := label_fiber_clique G r hr
  have small : ∀ c : Fin d, (univ.filter fun v => r v = c).card < k := by
    intro c
    by_contra h
    have hc : k ≤ (univ.filter fun v => r v = c).card := by omega
    let C := univ.filter fun v => r v = c
    let e : Fin k ↪o Fin n := C.orderEmbOfCardLe hc
    apply havoid
    refine ⟨0, e, e.strictMono, ?_⟩
    intro i j hij
    have zero : ∀ x : Fin k, dihedralPerm 0 false x = x := by
      intro x
      apply Fin.ext
      simp [dihedralPerm, Nat.mod_eq_of_lt x.isLt]
    rw [zero, zero]
    apply clique c
    · exact C.orderEmbOfCardLe_mem hc i
    · exact C.orderEmbOfCardLe_mem hc j
    · exact e.injective.ne ((monoPath k).ne_of_adj hij)
  have large : ∃ c : Fin d, (univ.filter fun v => r v = c).card = k - 1 := by
    obtain ⟨c, _, hc⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := univ) (t := univ) (f := r) (n := k - 2)
      (fun _ _ => mem_univ _) (by simpa using hn)
    have hs := small c
    exact ⟨c, by omega⟩
  obtain ⟨c, hc⟩ := large
  refine ⟨c, hc, ?_⟩
  exact clique c

/-- A saturated constant-label clique occupies an interval with opposite-color endpoints. -/
theorem full_layer_endpoints {n d : ℕ} (G : SimpleGraph (Fin n))
    (C : Finset (Fin n)) (hC : 1 < C.card) (r : Fin n → Fin d)
    (hr : ∀ u v, u < v → Gᶜ.Adj u v → r u < r v)
    (hsame : ∀ u ∈ C, ∀ v ∈ C, r u = r v)
    (hgap : ∀ x ∉ C, ∃ u ∈ C, ∃ v ∈ C,
      u ≠ v ∧ ¬G.Adj u x ∧ ¬G.Adj x v ∧
      ((u < x ∧ x < v ∧ ∀ z ∈ C, z ≤ u ∨ v ≤ z) ∨
       (v < u ∧ (x < v ∨ u < x) ∧ ∀ z ∈ C, v ≤ z ∧ z ≤ u))) :
    ∀ x ∉ C, Gᶜ.Adj (C.min' (card_pos.mp (by omega))) x ∧
      Gᶜ.Adj (C.max' (card_pos.mp (by omega))) x := by
  classical
  have hne : C.Nonempty := card_pos.mp (by omega)
  intro x hx
  obtain ⟨u, hu, v, hv, _, hux, hxv, hgap⟩ := hgap x hx
  rcases hgap with hgap | hgap
  · obtain ⟨huxlt, hxvlt, _⟩ := hgap
    have e1 : Gᶜ.Adj u x := (SimpleGraph.compl_adj _ _ _).mpr ⟨huxlt.ne, hux⟩
    have e2 : Gᶜ.Adj x v := (SimpleGraph.compl_adj _ _ _).mpr ⟨hxvlt.ne, hxv⟩
    have hlt := (hr u x huxlt e1).trans (hr x v hxvlt e2)
    exact (not_lt_of_ge (hsame u hu v hv).ge hlt).elim
  · obtain ⟨_, _, bounds⟩ := hgap
    have hvmin : v = C.min' hne := le_antisymm
      (bounds _ (C.min'_mem hne)).1 (C.min'_le v hv)
    have humax : u = C.max' hne := le_antisymm
      (C.le_max' u hu) (bounds _ (C.max'_mem hne)).2
    constructor
    · apply (SimpleGraph.compl_adj _ _ _).mpr
      refine ⟨fun he => hx (he ▸ C.min'_mem hne), ?_⟩
      intro he
      apply hxv
      rw [hvmin]
      exact he.symm
    · apply (SimpleGraph.compl_adj _ _ _).mpr
      refine ⟨fun he => hx (he ▸ C.max'_mem hne), ?_⟩
      intro he
      apply hux
      rw [humax]
      exact he

/-- Two full layers cannot have opposite clique and endpoint colors. -/
theorem full_layers_incompatible {n : ℕ} (G : SimpleGraph (Fin n))
    (C D : Finset (Fin n)) (hC : 1 < C.card) (hD : 1 < D.card)
    (blue : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → Gᶜ.Adj u v)
    (red : ∀ u ∈ D, ∀ v ∈ D, u ≠ v → G.Adj u v)
    (endsC : ∀ x ∉ C,
      G.Adj (C.min' (card_pos.mp (by omega))) x ∧
      G.Adj (C.max' (card_pos.mp (by omega))) x)
    (endsD : ∀ x ∉ D,
      Gᶜ.Adj (D.min' (card_pos.mp (by omega))) x ∧
      Gᶜ.Adj (D.max' (card_pos.mp (by omega))) x) : False := by
  classical
  have choose : ∀ (H : SimpleGraph (Fin n)) (X Y : Finset (Fin n))
      (hX : 1 < X.card),
      (∀ u ∈ X, ∀ v ∈ X, u ≠ v → Hᶜ.Adj u v) →
      (∀ u ∈ Y, ∀ v ∈ Y, u ≠ v → H.Adj u v) →
      (∀ x ∉ X, H.Adj (X.min' (card_pos.mp (by omega))) x ∧
        H.Adj (X.max' (card_pos.mp (by omega))) x) →
      ∃ c : Fin n, c ∉ Y ∧ ∀ x ∉ X, H.Adj c x := by
    intro H X Y hX hblue hred hends
    have hnX : X.Nonempty := card_pos.mp (by omega)
    by_cases hlo : X.min' hnX ∈ Y
    · have hhi : X.max' hnX ∉ Y := by
        intro hhi
        have hedge := hred _ hlo _ hhi (X.min'_lt_max'_of_card hX).ne
        have hblue := hblue _ (X.min'_mem hnX) _ (X.max'_mem hnX)
          (X.min'_lt_max'_of_card hX).ne
        exact (SimpleGraph.compl_adj _ _ _).mp hblue |>.2 hedge
      exact ⟨X.max' hnX, hhi, fun x hx => (hends x hx).2⟩
    · exact ⟨X.min' hnX, hlo, fun x hx => (hends x hx).1⟩
  have chooseC := choose G C D hC blue red endsC
  have chooseD := choose Gᶜ D C hD (by simpa using red) blue endsD
  obtain ⟨c, hc, hec⟩ := chooseC
  obtain ⟨d, hd, hed⟩ := chooseD
  exact (SimpleGraph.compl_adj _ _ _).mp (hed c hc) |>.2 (hec d hd).symm

/-- Opposite full longest-path layers give the sharp circular monotone forcing bound. -/
theorem monotone_monotone_forcing {a b : ℕ} (ha : 3 ≤ a) (hab : a ≤ b) :
    ∀ G : SimpleGraph (Fin (1 + (a - 1) * (b - 2))),
      CyclicEmbeddable (monoPath a) G ∨ CyclicEmbeddable (monoPath b) Gᶜ := by
  classical
  intro G
  by_cases hred : CyclicEmbeddable (monoPath a) G
  · exact Or.inl hred
  by_cases hblue : CyclicEmbeddable (monoPath b) Gᶜ
  · exact Or.inr hblue
  have hb : 3 ≤ b := ha.trans hab
  have ordered_red : ¬∃ ψ : Fin a → Fin (1 + (a - 1) * (b - 2)),
      StrictMono ψ ∧ ∀ i j, (monoPath a).Adj i j → G.Adj (ψ i) (ψ j) := by
    rintro ⟨ψ, hψ, he⟩
    apply hred
    refine ⟨0, ψ, hψ, ?_⟩
    simpa [dihedralPerm, Nat.mod_eq_of_lt] using he
  have ordered_blue : ¬∃ ψ : Fin b → Fin (1 + (a - 1) * (b - 2)),
      StrictMono ψ ∧ ∀ i j, (monoPath b).Adj i j → Gᶜ.Adj (ψ i) (ψ j) := by
    rintro ⟨ψ, hψ, he⟩
    apply hblue
    refine ⟨0, ψ, hψ, ?_⟩
    simpa [dihedralPerm, Nat.mod_eq_of_lt] using he
  obtain ⟨r, hr⟩ := monotone_path_labels (by omega) G ordered_red
  obtain ⟨l, hl⟩ := monotone_path_labels (by omega) Gᶜ ordered_blue
  obtain ⟨c, hc, hC⟩ := monotone_full_layer (by omega) G hblue r hr (by omega)
  have hcomp : ¬CyclicEmbeddable (monoPath a) Gᶜᶜ := by simpa using hred
  have second : (b - 1) * (a - 2) < 1 + (a - 1) * (b - 2) := by
    have ha1 : a - 1 + 1 = a := by omega
    have ha2 : a - 2 + 2 = a := by omega
    have hb1 : b - 1 + 1 = b := by omega
    have hb2 : b - 2 + 2 = b := by omega
    nlinarith
  obtain ⟨d, hd, hD0⟩ := monotone_full_layer (by omega) Gᶜ hcomp l hl second
  let C := univ.filter fun v => r v = c
  let D := univ.filter fun v => l v = d
  have hCsize : C.card = b - 1 := hc
  have hDsize : D.card = a - 1 := hd
  have hD : G.IsClique (D : Set _) := by simpa [D] using hD0
  have endsC := full_layer_endpoints Gᶜ C (by omega) r
    (fun u v huv he => hr u v huv (by simpa using he))
    (fun u hu v hv => (mem_filter.mp hu).2.trans (mem_filter.mp hv).2.symm)
    (saturated_clique_neighbors hb Gᶜ hblue C hC hCsize)
  have endsD := full_layer_endpoints G D (by omega) l hl
    (fun u hu v hv => (mem_filter.mp hu).2.trans (mem_filter.mp hv).2.symm)
    (saturated_clique_neighbors ha G hred D hD hDsize)
  apply False.elim
  apply full_layers_incompatible G C D (by omega) (by omega)
  · intro u hu v hv hne
    exact hC hu hv hne
  · intro u hu v hv hne
    exact hD hu hv hne
  · simpa using endsC
  · exact endsD

end D5.S3.Combinatorics.DihedralRamsey

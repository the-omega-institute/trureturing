/- GID: D5/S3/Combinatorics/Graph/ZeroForcing/SpiderConnectedForcing
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/ZeroForcing/SpiderConnectedForcing
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.Coeff]
   utility: none
   digest: For k >= 3 arms of lengths h_j >= 1, the spider has connected forcing polynomial x^k (x prod_j F_(h_j) + sum_j prod_(t != j) F_(h_t)), F_h = 1 + x + ... + x^(h-1). -/

import D5.S3.Combinatorics.Graph.ZeroForcing.ConnectedForcingCrossingRefutation
import Mathlib.Algebra.Polynomial.Coeff

/-! The connected forcing polynomial of the spider, Proposition 7.11 of B. Brimkov, Graph
Coloring, Zero Forcing, and Related Problems (PhD thesis, Rice University, 2017), written as a
product: for `k ≥ 3` arms with `h_j ≥ 1` vertices,
`Z_c(S(h_1, …, h_k); x) = x^k (x ∏_j F_{h_j} + Σ_j ∏_{t ≠ j} F_{h_t})` with
`F_h = 1 + x + ⋯ + x^(h-1)`. The coefficients are the frozen
`ConnectedForcingCrossingRefutation.coefficient` for `spider h` on the vertices
`Option (Σ j, Fin (h j))`, where `none` is the centre and `some ⟨j, p⟩` is the vertex of arm `j`
at distance `p + 1` from it.

`connected_forcing_iff` characterizes the connected forcing sets: the sets `body ℓ` made of the
centre and the first `ℓ j ≤ h j` vertices of each arm, with at most one arm untouched. A walk
leaving a region crosses its only boundary vertex, so a connected set without the centre lies in
one arm and a connected set with the centre meets every arm in an initial segment. With three or
more arms the centre has two white neighbours unless at most one arm is untouched, and a touched
arm forces outward along itself.

admission_basis: escape-witness. Escape witnesses: walk_boundary with centre_mem and init_seg
(connected sets), untouched_le_one and body_cf with arm_chain (the forcing behaviour),
mem_iff_lt_armLen (sets as arm-length tuples), card_body, L_eq and sum_L (the generating
function). -/

set_option autoImplicit false
noncomputable section

namespace D5.S3.Combinatorics.Graph.ZeroForcing.SpiderConnectedForcing

open SimpleGraph
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThree
open D5.S3.Combinatorics.Graph.ZeroForcing.ConnectedForcingCrossingRefutation

variable {k : ℕ} (h : Fin k → ℕ)

/-- Vertices of the spider: the centre `none` and `some ⟨j, p⟩`, the vertex of arm `j` at
distance `p + 1` from the centre. -/
abbrev V := Option (Σ j : Fin k, Fin (h j))

/-- Adjacency of the spider with arm lengths `h`. -/
def adj : V h → V h → Prop
  | none, none => False
  | none, some x => x.2.val = 0
  | some x, none => x.2.val = 0
  | some x, some y => x.1 = y.1 ∧ (x.2.val + 1 = y.2.val ∨ y.2.val + 1 = x.2.val)

/-- The spider `S(h_1, …, h_k)`: `k` paths with `h_j` vertices attached to a centre. -/
def spider : SimpleGraph (V h) where
  Adj := adj h
  symm := ⟨fun u v huv => by
    rcases u with _ | ⟨j, p⟩ <;> rcases v with _ | ⟨j', p'⟩ <;> simp only [adj] at huv ⊢
    · exact huv
    · exact huv
    · exact ⟨huv.1.symm, huv.2.symm⟩⟩
  loopless := ⟨fun u hu => by
    rcases u with _ | ⟨j, p⟩ <;> simp only [adj] at hu
    omega⟩

variable {h}

@[simp] private theorem adj_none_some (j : Fin k) (p : Fin (h j)) :
    (spider h).Adj none (some ⟨j, p⟩) ↔ p.val = 0 := Iff.rfl

@[simp] private theorem adj_some_none (j : Fin k) (p : Fin (h j)) :
    (spider h).Adj (some ⟨j, p⟩) none ↔ p.val = 0 := Iff.rfl

@[simp] private theorem adj_some_some (j j' : Fin k) (p : Fin (h j)) (p' : Fin (h j')) :
    (spider h).Adj (some ⟨j, p⟩) (some ⟨j', p'⟩) ↔
      j = j' ∧ (p.val + 1 = p'.val ∨ p'.val + 1 = p.val) := Iff.rfl

/-- A walk inside `S` from a vertex of `R` to a vertex outside `R` passes through `b` when every
edge leaving `R` ends at `b`. -/
private theorem walk_boundary {W : Type*} {G : SimpleGraph W} (S R : Set W) (b : W)
    (hR : ∀ v w, v ∈ R → w ∉ R → G.Adj v w → w = b) {u w : S} (p : (G.induce S).Walk u w)
    (hu : u.1 ∈ R) (hw : w.1 ∉ R) : b ∈ S := by
  induction p with
  | nil => exact absurd hu hw
  | @cons u u' w h p ih =>
    by_cases hu' : u'.1 ∈ R
    · exact ih hu' hw
    · exact (hR u.1 u'.1 hu hu' h) ▸ u'.2

/-- The set made of the centre and the first `ℓ j` vertices of each arm `j`. -/
def body (ℓ : Fin k → ℕ) : Finset (V h) :=
  insert none ((Finset.univ.filter fun x : (Σ j : Fin k, Fin (h j)) => x.2.val < ℓ x.1).map
    Function.Embedding.some)

private theorem none_mem_body (ℓ : Fin k → ℕ) : (none : V h) ∈ body ℓ := Finset.mem_insert_self _ _

private theorem some_mem_body (ℓ : Fin k → ℕ) (j : Fin k) (p : Fin (h j)) :
    (some ⟨j, p⟩ : V h) ∈ body ℓ ↔ p.val < ℓ j := by
  simp [body]

/-- Once the first vertex of an arm is black, the whole arm turns black. -/
private theorem arm_chain (T : Set (V h)) (hc : none ∈ T) (j : Fin k) (h0 : 0 < h j)
    (hb : Black (spider h) T (some ⟨j, ⟨0, h0⟩⟩)) :
    ∀ p (hp : p < h j), Black (spider h) T (some ⟨j, ⟨p, hp⟩⟩) := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro hp
    rcases p with _ | q
    · exact hb
    refine .force (u := some ⟨j, ⟨q, by omega⟩⟩) (ih q (by omega) (by omega))
      (by simp) fun x hx hxw => ?_
    rcases x with _ | ⟨j', p'⟩
    · exact .init hc
    · simp only [adj_some_some] at hx
      obtain ⟨rfl, hx | hx⟩ := hx
      · exact absurd (by congr 2; exact Fin.ext (by simp; omega)) hxw
      · have := ih p'.val (by omega) p'.isLt
        exact this

/-- `body ℓ` is a connected forcing set when at most one arm is untouched. -/
private theorem body_cf (hpos : ∀ j, 0 < h j) (ℓ : Fin k → ℕ)
    (hz : (Finset.univ.filter fun j => ℓ j = 0).card ≤ 1) :
    connectedForcing (spider h) (body ℓ) := by
  have hc : (none : V h) ∈ ((body ℓ : Finset (V h)) : Set (V h)) := none_mem_body ℓ
  refine ⟨?_, ?_⟩
  · have reach : ∀ (j : Fin k) (p : ℕ) (hp : p < h j) (hpl : p < ℓ j),
        ((spider h).induce ((body ℓ : Finset (V h)) : Set (V h))).Reachable ⟨none, hc⟩
          ⟨some ⟨j, ⟨p, hp⟩⟩, (some_mem_body ℓ j _).mpr hpl⟩ := by
      intro j p
      induction p with
      | zero =>
        intro hp hpl
        exact SimpleGraph.Adj.reachable (show (spider h).Adj none (some ⟨j, ⟨0, hp⟩⟩) by simp)
      | succ q ih =>
        intro hp hpl
        exact (ih (by omega) (by omega)).trans (SimpleGraph.Adj.reachable
          (show (spider h).Adj (some ⟨j, ⟨q, by omega⟩⟩) (some ⟨j, ⟨q + 1, hp⟩⟩) by simp))
    have : Nonempty ↥((body ℓ : Finset (V h)) : Set (V h)) := ⟨⟨none, hc⟩⟩
    have hx : ∀ x : ↥((body ℓ : Finset (V h)) : Set (V h)),
        ((spider h).induce ((body ℓ : Finset (V h)) : Set (V h))).Reachable ⟨none, hc⟩ x := by
      rintro ⟨_ | ⟨j, p⟩, hx⟩
      · rfl
      · exact reach j p.val p.isLt ((some_mem_body ℓ j p).mp hx)
    exact ⟨fun x y => (hx x).symm.trans (hx y)⟩
  · -- every arm turns black
    have first : ∀ j, Black (spider h) ((body ℓ : Finset (V h)) : Set (V h))
        (some ⟨j, ⟨0, hpos j⟩⟩) := by
      intro j
      by_cases hj : 0 < ℓ j
      · exact .init ((some_mem_body ℓ j _).mpr hj)
      · refine .force (u := none) (.init hc) (by simp) fun x hx hxw => ?_
        rcases x with _ | ⟨t, p'⟩
        · exact absurd hx ((spider h).loopless.irrefl _)
        · simp only [adj_none_some] at hx
          have htj : t ≠ j := by
            rintro rfl
            exact hxw (by congr 2; exact Fin.ext hx)
          have hlt : 0 < ℓ t := by
            by_contra h0
            have hsub : ({t, j} : Finset (Fin k)) ⊆ Finset.univ.filter fun j => ℓ j = 0 := by
              intro y hy
              rcases Finset.mem_insert.mp hy with rfl | hy
              · simp; omega
              · rw [Finset.mem_singleton.mp hy]; simp; omega
            have := Finset.card_le_card hsub
            rw [Finset.card_pair htj] at this
            omega
          exact .init ((some_mem_body ℓ t p').mpr (by omega))
    rintro (_ | ⟨j, p⟩)
    · exact .init hc
    · exact arm_chain _ hc j (hpos j) (first j) p.val p.isLt

private theorem some_ne_some {j j' : Fin k} (p : Fin (h j)) (p' : Fin (h j')) (hj : j ≠ j') :
    (some ⟨j, p⟩ : V h) ≠ some ⟨j', p'⟩ := by
  intro e; simp only [Option.some.injEq, Sigma.mk.inj_iff] at e; exact hj e.1

/-- Two arms other than a given one, when there are at least three arms. -/
private theorem two_other (hk : 3 ≤ k) (j : Fin k) :
    ∃ t1 t2 : Fin k, t1 ≠ t2 ∧ t1 ≠ j ∧ t2 ≠ j := by
  have : 1 < (Finset.univ.erase j).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]; omega
  obtain ⟨t1, h1, t2, h2, h12⟩ := Finset.one_lt_card.mp this
  exact ⟨t1, t2, h12, Finset.ne_of_mem_erase h1, Finset.ne_of_mem_erase h2⟩

/-- With at least three arms a connected forcing set contains the centre. -/
private theorem centre_mem (hk : 3 ≤ k) (hpos : ∀ j, 0 < h j) (S : Finset (V h))
    (hS : connectedForcing (spider h) S) : (none : V h) ∈ S := by
  by_contra hc
  obtain ⟨hconn, hforce⟩ := hS
  obtain ⟨⟨v, hv⟩⟩ := hconn.nonempty
  rcases v with _ | ⟨j, p⟩
  · exact hc hv
  have harm : ∀ w ∈ (S : Set (V h)), ∃ q, w = some ⟨j, q⟩ := by
    intro w hw
    by_contra hnot
    obtain ⟨pth⟩ := hconn.preconnected ⟨some ⟨j, p⟩, hv⟩ ⟨w, hw⟩
    refine hc (walk_boundary (S : Set (V h)) {x | ∃ q, x = some ⟨j, q⟩} none ?_ pth ⟨p, rfl⟩ hnot)
    rintro x y ⟨q, rfl⟩ hy hxy
    rcases y with _ | ⟨j', q'⟩
    · rfl
    · simp only [adj_some_some] at hxy; obtain ⟨rfl, -⟩ := hxy; exact absurd ⟨q', rfl⟩ hy
  obtain ⟨t1, t2, h12, h1, h2⟩ := two_other hk j
  have inv : ∀ w, Black (spider h) (S : Set (V h)) w → w = none ∨ ∃ q, w = some ⟨j, q⟩ := by
    intro w hw
    induction hw with
    | init hw => exact Or.inr (harm _ hw)
    | @force u w hu huw hall ihu ihall =>
      rcases ihu with rfl | ⟨q, rfl⟩
      · exfalso
        have key : ∀ t, t ≠ j → some ⟨t, ⟨0, hpos t⟩⟩ ≠ w → False := by
          intro t ht hne
          rcases ihall (some ⟨t, ⟨0, hpos t⟩⟩) (by simp) hne with e | ⟨q, e⟩
          · exact Option.some_ne_none _ e
          · exact some_ne_some _ _ ht e
        by_cases hw1 : some ⟨t1, ⟨0, hpos t1⟩⟩ = w
        · exact key t2 h2 (hw1 ▸ some_ne_some _ _ (Ne.symm h12))
        · exact key t1 h1 hw1
      · rcases w with _ | ⟨j', r⟩
        · exact Or.inl rfl
        · simp only [adj_some_some] at huw
          obtain ⟨rfl, -⟩ := huw
          exact Or.inr ⟨r, rfl⟩
  rcases inv _ (hforce (some ⟨t1, ⟨0, hpos t1⟩⟩)) with e | ⟨q, e⟩
  · exact Option.some_ne_none _ e
  · exact some_ne_some _ _ h1 e

/-- A connected set containing the centre meets each arm in an initial segment. -/
private theorem init_seg (S : Finset (V h)) (hconn : ((spider h).induce (S : Set (V h))).Connected)
    (hc : (none : V h) ∈ S) (j : Fin k) (p q : Fin (h j)) (hqp : q.val < p.val)
    (hp : (some ⟨j, p⟩ : V h) ∈ S) : (some ⟨j, q⟩ : V h) ∈ S := by
  obtain ⟨pth⟩ := hconn.preconnected ⟨some ⟨j, p⟩, hp⟩ ⟨none, hc⟩
  refine walk_boundary (S : Set (V h)) {x | ∃ r : Fin (h j), q.val < r.val ∧ x = some ⟨j, r⟩}
    (some ⟨j, q⟩) ?_ pth ⟨p, hqp, rfl⟩ (by rintro ⟨r, -, e⟩; exact Option.some_ne_none _ e.symm)
  rintro x y ⟨r, hr, rfl⟩ hy hxy
  rcases y with _ | ⟨j', r'⟩
  · simp only [adj_some_none] at hxy; omega
  · simp only [adj_some_some] at hxy
    obtain ⟨rfl, hxy | hxy⟩ := hxy
    · exact absurd ⟨r', by omega, rfl⟩ hy
    · have : ¬ q.val < r'.val := fun hlt => hy ⟨r', hlt, rfl⟩
      congr 2; exact Fin.ext (by omega)

/-- The number of vertices of arm `j` in `S`. -/
private def armLen (S : Finset (V h)) (j : Fin k) : ℕ :=
  (Finset.univ.filter fun p : Fin (h j) => (some ⟨j, p⟩ : V h) ∈ S).card

private theorem armLen_le (S : Finset (V h)) (j : Fin k) : armLen S j ≤ h j := by
  unfold armLen
  calc _ ≤ (Finset.univ : Finset (Fin (h j))).card := Finset.card_le_card (Finset.filter_subset _ _)
    _ = h j := by simp

private theorem mem_iff_lt_armLen (S : Finset (V h))
    (hconn : ((spider h).induce (S : Set (V h))).Connected)
    (hc : (none : V h) ∈ S) (j : Fin k) (p : Fin (h j)) :
    (some ⟨j, p⟩ : V h) ∈ S ↔ p.val < armLen S j := by
  unfold armLen
  constructor
  · intro hp
    have hsub : (Finset.univ.filter fun q : Fin (h j) => (q : ℕ) < p.val + 1) ⊆
        Finset.univ.filter fun q : Fin (h j) => (some ⟨j, q⟩ : V h) ∈ S := by
      intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      rcases Nat.lt_or_ge q.val p.val with hlt | hge
      · exact init_seg S hconn hc j p q hlt hp
      · have : q = p := Fin.ext (by omega)
        rw [this]; exact hp
    have := Finset.card_le_card hsub
    rw [Fin.card_filter_val_lt] at this
    have := p.isLt
    omega
  · intro hlt
    by_contra hp
    have hsub : (Finset.univ.filter fun q : Fin (h j) => (some ⟨j, q⟩ : V h) ∈ S) ⊆
        Finset.univ.filter fun q : Fin (h j) => (q : ℕ) < p.val := by
      intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      by_contra hge
      rcases Nat.lt_or_ge p.val q.val with hlt' | hle
      · exact hp (init_seg S hconn hc j q p hlt' hq)
      · have : q = p := Fin.ext (by omega)
        exact hp (this ▸ hq)
    have := Finset.card_le_card hsub
    rw [Fin.card_filter_val_lt] at this
    omega

/-- In a connected forcing set at most one arm is untouched. -/
private theorem untouched_le_one (hpos : ∀ j, 0 < h j) (S : Finset (V h))
    (hS : connectedForcing (spider h) S) (hc : (none : V h) ∈ S) :
    (Finset.univ.filter fun j => armLen S j = 0).card ≤ 1 := by
  obtain ⟨hconn, hforce⟩ := hS
  by_contra hmany
  push Not at hmany
  obtain ⟨j1, hj1, j2, hj2, h12⟩ := Finset.one_lt_card.mp hmany
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj1 hj2
  have notin : ∀ j, armLen S j = 0 → ∀ q : Fin (h j), (some ⟨j, q⟩ : V h) ∉ S := by
    intro j hj q hq
    have := (mem_iff_lt_armLen S hconn hc j q).mp hq
    omega
  have inv : ∀ w, Black (spider h) (S : Set (V h)) w →
      (∀ q, w ≠ some ⟨j1, q⟩) ∧ (∀ q, w ≠ some ⟨j2, q⟩) := by
    intro w hw
    induction hw with
    | init hw =>
      exact ⟨fun q e => notin j1 hj1 q (e ▸ hw), fun q e => notin j2 hj2 q (e ▸ hw)⟩
    | @force u w hu huw hall ihu ihall =>
      rcases u with _ | ⟨j', q⟩
      · exfalso
        by_cases hw1 : some ⟨j1, ⟨0, hpos j1⟩⟩ = w
        · exact (ihall (some ⟨j2, ⟨0, hpos j2⟩⟩) (by simp)
            (hw1 ▸ some_ne_some _ _ (Ne.symm h12))).2 _ rfl
        · exact (ihall (some ⟨j1, ⟨0, hpos j1⟩⟩) (by simp) hw1).1 _ rfl
      · have h1 : j' ≠ j1 := by rintro rfl; exact ihu.1 q rfl
        have h2 : j' ≠ j2 := by rintro rfl; exact ihu.2 q rfl
        rcases w with _ | ⟨j'', r⟩
        · exact ⟨fun q e => Option.some_ne_none _ e.symm, fun q e => Option.some_ne_none _ e.symm⟩
        · simp only [adj_some_some] at huw
          obtain ⟨rfl, -⟩ := huw
          exact ⟨fun q e => some_ne_some _ _ h1 e, fun q e => some_ne_some _ _ h2 e⟩
  exact (inv _ (hforce (some ⟨j1, ⟨0, hpos j1⟩⟩))).1 _ rfl

/-- The connected forcing sets of a spider with `k ≥ 3` arms of positive lengths: the sets
`body ℓ` with `ℓ j ≤ h j` for every arm and at most one arm untouched (`ℓ j = 0`). -/
theorem connected_forcing_iff (hk : 3 ≤ k) (hpos : ∀ j, 0 < h j) (S : Finset (V h)) :
    connectedForcing (spider h) S ↔ ∃ ℓ : Fin k → ℕ, (∀ j, ℓ j ≤ h j) ∧
      (Finset.univ.filter fun j => ℓ j = 0).card ≤ 1 ∧ S = body ℓ := by
  constructor
  · intro hS
    have hc := centre_mem hk hpos S hS
    refine ⟨armLen S, armLen_le S, untouched_le_one hpos S hS hc, ?_⟩
    ext v
    rcases v with _ | ⟨j, p⟩
    · simp [hc, none_mem_body]
    · rw [some_mem_body, mem_iff_lt_armLen S hS.1 hc]
  · rintro ⟨ℓ, -, hz, rfl⟩
    exact body_cf hpos ℓ hz

open Polynomial

private theorem armLen_body (ℓ : Fin k → ℕ) (hℓ : ∀ j, ℓ j ≤ h j) (j : Fin k) :
    armLen (body (h := h) ℓ) j = ℓ j := by
  unfold armLen
  simp only [some_mem_body]
  rw [Fin.card_filter_val_lt]
  have := hℓ j; omega

private theorem card_body (ℓ : Fin k → ℕ) (hℓ : ∀ j, ℓ j ≤ h j) :
    (body (h := h) ℓ).card = 1 + ∑ j, ℓ j := by
  unfold body
  rw [Finset.card_insert_of_notMem (by simp), Finset.card_map, add_comm]
  congr 1
  have : (Finset.univ.filter fun x : (Σ j : Fin k, Fin (h j)) => x.2.val < ℓ x.1) =
      Finset.univ.sigma fun j => Finset.univ.filter fun p : Fin (h j) => p.val < ℓ j := by
    ext ⟨j, p⟩; simp
  rw [this, Finset.card_sigma]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fin.card_filter_val_lt]
  have := hℓ j; omega

private theorem coeff_sum_pow (A : Finset (Finset (V h))) (i : ℕ) :
    (∑ S ∈ A, (X : ℕ[X]) ^ S.card).coeff i = (A.filter fun S => S.card = i).card := by
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_X_pow]
  rw [Finset.sum_boole]
  simp [eq_comm]

private theorem X_mul_geom (n : ℕ) :
    (X : ℕ[X]) * ∑ e ∈ Finset.range n, X ^ e = ∑ l ∈ Finset.Ico 1 (n + 1), X ^ l := by
  rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum, show n + 1 - 1 = n by omega]
  refine Finset.sum_congr rfl fun e _ => ?_
  ring

/-- Arm-length tuples with at most one untouched arm. -/
private def L (h : Fin k → ℕ) : Finset (Fin k → ℕ) :=
  (Fintype.piFinset fun j => Finset.range (h j + 1)).filter fun ℓ =>
    (Finset.univ.filter fun j => ℓ j = 0).card ≤ 1

/-- Tuples touching every arm. -/
private def A (h : Fin k → ℕ) : Finset (Fin k → ℕ) :=
  Fintype.piFinset fun j => Finset.Ico 1 (h j + 1)

/-- Tuples leaving exactly arm `j0` untouched. -/
private def B (h : Fin k → ℕ) (j0 : Fin k) : Finset (Fin k → ℕ) :=
  Fintype.piFinset fun j => if j = j0 then {0} else Finset.Ico 1 (h j + 1)

private theorem mem_B (j0 : Fin k) (ℓ : Fin k → ℕ) :
    ℓ ∈ B h j0 ↔ ℓ j0 = 0 ∧ ∀ j, j ≠ j0 → 1 ≤ ℓ j ∧ ℓ j < h j + 1 := by
  simp only [B, Fintype.mem_piFinset]
  constructor
  · intro H
    refine ⟨by simpa using H j0, fun j hj => ?_⟩
    simpa [hj] using H j
  · rintro ⟨h0, H⟩ j
    split_ifs with hj
    · subst hj; simp [h0]
    · rw [Finset.mem_Ico]; exact H j hj

private theorem L_eq : L h = A h ∪ Finset.univ.biUnion (B h) := by
  ext ℓ
  simp only [L, A, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range, Finset.mem_union,
    Finset.mem_Ico, Finset.mem_biUnion, Finset.mem_univ, true_and, mem_B]
  constructor
  · rintro ⟨hr, hz⟩
    by_cases hex : ∃ j0, ℓ j0 = 0
    · obtain ⟨j0, h0⟩ := hex
      right
      refine ⟨j0, h0, fun j hj => ⟨?_, hr j⟩⟩
      by_contra hj0
      have hsub : ({j, j0} : Finset (Fin k)) ⊆ Finset.univ.filter fun j => ℓ j = 0 := by
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · simp; omega
        · rw [Finset.mem_singleton.mp hy]; simp [h0]
      have := Finset.card_le_card hsub
      rw [Finset.card_pair hj] at this
      omega
    · push Not at hex
      left
      exact fun j => ⟨by have := hex j; omega, hr j⟩
  · rintro (H | ⟨j0, h0, H⟩)
    · refine ⟨fun j => (H j).2, ?_⟩
      rw [Finset.card_le_one]
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      have := (H a).1; omega
    · refine ⟨fun j => ?_, ?_⟩
      · by_cases hj : j = j0
        · subst hj; omega
        · exact (H j hj).2
      · rw [Finset.card_le_one]
        intro a ha b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
        by_contra hab
        rcases eq_or_ne a j0 with rfl | haj
        · have := (H b (fun e => hab e.symm)).1; omega
        · have := (H a haj).1; omega

private theorem disjoint_A_B : Disjoint (A h) (Finset.univ.biUnion (B h)) := by
  rw [Finset.disjoint_left]
  intro ℓ hA hB
  simp only [A, Fintype.mem_piFinset, Finset.mem_Ico] at hA
  obtain ⟨j0, -, hB⟩ := Finset.mem_biUnion.mp hB
  have := ((mem_B j0 ℓ).mp hB).1
  have := (hA j0).1
  omega

private theorem pairwise_B :
    (↑(Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint (B h) := by
  intro j0 _ j1 _ hne
  rw [Function.onFun, Finset.disjoint_left]
  intro ℓ h0 h1
  have := ((mem_B j0 ℓ).mp h0).1
  have := (((mem_B j1 ℓ).mp h1).2 j0 hne).1
  omega

/-- The generating sum over the arm-length tuples. -/
private theorem sum_L (hk : 1 ≤ k) :
    ∑ ℓ ∈ L h, ∏ j, (X : ℕ[X]) ^ ℓ j =
      X ^ (k - 1) * (X * ∏ j, ∑ e ∈ Finset.range (h j), X ^ e +
        ∑ j, ∏ t ∈ Finset.univ.erase j, ∑ e ∈ Finset.range (h t), X ^ e) := by
  rw [L_eq, Finset.sum_union disjoint_A_B, Finset.sum_biUnion pairwise_B]
  have hA : ∑ ℓ ∈ A h, ∏ j, (X : ℕ[X]) ^ ℓ j =
      X ^ k * ∏ j, ∑ e ∈ Finset.range (h j), X ^ e := by
    rw [A, ← Finset.prod_univ_sum]
    simp only [← X_mul_geom]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hB : ∀ j0, ∑ ℓ ∈ B h j0, ∏ j, (X : ℕ[X]) ^ ℓ j =
      X ^ (k - 1) * ∏ t ∈ Finset.univ.erase j0, ∑ e ∈ Finset.range (h t), X ^ e := by
    intro j0
    rw [B, ← Finset.prod_univ_sum]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j0)]
    simp only [↓reduceIte, Finset.sum_singleton, pow_zero, one_mul]
    rw [Finset.prod_congr rfl (g := fun t => X * ∑ e ∈ Finset.range (h t), (X : ℕ[X]) ^ e)
      fun t ht => by simp only [Finset.ne_of_mem_erase ht, ↓reduceIte]; rw [X_mul_geom]]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin]
  rw [hA, Finset.sum_congr rfl fun j0 _ => hB j0, ← Finset.mul_sum]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  ring

private theorem body_injOn : Set.InjOn (body (h := h)) (L h) := by
  intro ℓ hℓ ℓ' hℓ' e
  have le : ∀ m ∈ (L h : Set (Fin k → ℕ)), ∀ j, m j ≤ h j := by
    intro m hm j
    simp only [L, Finset.coe_filter, Fintype.mem_piFinset, Finset.mem_range,
      Set.mem_ofPred_eq] at hm
    have := hm.1 j; omega
  funext j
  rw [← armLen_body ℓ (le ℓ hℓ) j, ← armLen_body ℓ' (le ℓ' hℓ') j, e]

open Classical in
private theorem cf_finset_eq (hk : 3 ≤ k) (hpos : ∀ j, 0 < h j) :
    (Finset.univ.filter fun S : Finset (V h) => connectedForcing (spider h) S) =
      (L h).image body := by
  ext S
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
    connected_forcing_iff hk hpos]
  constructor
  · rintro ⟨ℓ, hle, hz, rfl⟩
    refine ⟨ℓ, ?_, rfl⟩
    simp only [L, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
    exact ⟨fun j => by have := hle j; omega, hz⟩
  · rintro ⟨ℓ, hℓ, rfl⟩
    simp only [L, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hℓ
    exact ⟨ℓ, fun j => by have := hℓ.1 j; omega, hℓ.2, rfl⟩

/-- The connected forcing polynomial of the spider with `k ≥ 3` arms of lengths `h j ≥ 1`:
`Z_c = x^k (x ∏_j F_{h_j} + Σ_j ∏_{t ≠ j} F_{h_t})` with `F_h = Σ_{e < h} x^e`. -/
theorem result (hk : 3 ≤ k) (hpos : ∀ j, 0 < h j) (i : ℕ) :
    coefficient (spider h) i =
      ((X : ℕ[X]) ^ k * (X * ∏ j, ∑ e ∈ Finset.range (h j), X ^ e +
        ∑ j, ∏ t ∈ Finset.univ.erase j, ∑ e ∈ Finset.range (h t), X ^ e)).coeff i := by
  classical
  have hsum : ∑ S ∈ (Finset.univ.filter fun S : Finset (V h) => connectedForcing (spider h) S),
      (X : ℕ[X]) ^ S.card = X ^ k * (X * ∏ j, ∑ e ∈ Finset.range (h j), X ^ e +
        ∑ j, ∏ t ∈ Finset.univ.erase j, ∑ e ∈ Finset.range (h t), X ^ e) := by
    rw [cf_finset_eq hk hpos, Finset.sum_image body_injOn]
    have : ∀ ℓ ∈ L h, (X : ℕ[X]) ^ (body (h := h) ℓ).card = X * ∏ j, X ^ ℓ j := by
      intro ℓ hℓ
      simp only [L, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hℓ
      rw [card_body ℓ fun j => by have := hℓ.1 j; omega, pow_add, pow_one,
        Finset.prod_pow_eq_pow_sum]
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, sum_L (by omega)]
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  rw [← hsum, coeff_sum_pow, Finset.filter_filter]
  unfold coefficient
  congr 1
  ext S
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact and_comm

end D5.S3.Combinatorics.Graph.ZeroForcing.SpiderConnectedForcing

/- GID: D5/S3/ConceptDynamics/GraphColoring/JacoDirectedPathCount
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/GraphColoring/JacoDirectedPathCount
   mirror-E: none(waiver:structural-proof)
   anchors: [lake/module/D5.S3.ConceptDynamics.GraphColoring.JacoEndpointBeatty, mathlib/module/Mathlib.Combinatorics.Quiver.Path.Vertices]
   utility: none
   digest: Directed Jaco paths retain their actual minimum-length cardinality in finite truncations. -/

import D5.S3.ConceptDynamics.GraphColoring.JacoEndpointBeatty
import Mathlib.Combinatorics.Quiver.Path.Vertices

/-! Directed edge sequences, minimum edge lengths, and finite truncations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.GraphColoring.JacoDirectedPathCount

open D5.S0.Certificates.JacoExponentialDominationRefutation
open D5.S3.ConceptDynamics.GraphColoring.JacoEndpointBeatty

/-- Positive source labels, with precisely the original forward arcs. -/
@[instance_reducible] def directed : Quiver ℕ+ where
  Hom a b := PLift (a.val < b.val ∧ b.val ≤ jacoRight a.val)

attribute [local instance] directed

private instance (a b : ℕ+) : Subsingleton (a ⟶ b) := inferInstanceAs (Subsingleton (PLift _))

/-- A path in the induced truncation, retaining the original edge sequence. -/
def TruncatedPath (r : ℕ) (a b : ℕ+) :=
  {p : Quiver.Path a b // ∀ v ∈ p.vertices, v.val ≤ r}

/-- Actual shortest directed paths in the target vertex's own truncation. -/
def Shortest (n : ℕ+) :=
  {p : TruncatedPath n.val 1 n // ∀ q : TruncatedPath n.val 1 n,
    p.val.length ≤ q.val.length}

/-- Cardinality of actual minimum-edge-length paths; index zero is unused. -/
noncomputable def psi (n : ℕ) : ℕ :=
  if hn : 0 < n then Nat.card (Shortest ⟨n, hn⟩) else 0

/-- Infinite outdegree, rather than an outdegree truncated at the target. -/
def outdegree (n : ℕ) : ℕ := jacoRight n - n

/-- The complete original directed Proposition 4.4, with both adjacent comparisons. -/
def claim : Prop :=
  ∀ k : ℕ, 7 ≤ k → ∀ i : ℕ, Nat.fib i < k → k ≤ Nat.fib (i + 1) →
    ((outdegree (k - 1) ≠ outdegree k ∧ outdegree k ≠ outdegree (k + 1)) ↔
      (psi (k - 1) ≠ psi k ∧ psi k ≠ psi (k + 1)))

private theorem vertices_bounds {a b : ℕ+} (p : Quiver.Path a b) :
    ∀ v ∈ p.vertices, a.val ≤ v.val ∧ v.val ≤ b.val := by
  induction p with
  | nil => simp
  | @cons b c p e ih =>
      intro v hv
      rcases (Quiver.Path.mem_vertices_cons p e).mp hv with hv | rfl
      · exact ⟨(ih v hv).1, le_trans (ih v hv).2 (Nat.le_of_lt e.down.1)⟩
      · exact ⟨le_trans (ih a p.start_mem_vertices).1
          (le_trans (ih a p.start_mem_vertices).2 (Nat.le_of_lt e.down.1)), le_rfl⟩

private def splitLast {a b : ℕ+} (p : Quiver.Path a b) :
    Option (Σ c : {c : ℕ+ // c.val < b.val}, Quiver.Path a c.val) :=
  by
    cases p with
    | nil => exact none
    | @cons c d q e => exact some ⟨⟨c, e.down.1⟩, q⟩

private theorem splitLast_injective (a b : ℕ+) :
    Function.Injective (@splitLast a b) := by
  intro p q h
  cases p with
  | nil =>
      cases q with
      | nil => rfl
      | cons q e => simp [splitLast] at h
  | @cons c b p e =>
      cases q with
      | nil => simp [splitLast] at h
      | @cons d b q f =>
          simp only [splitLast, Option.some.injEq] at h
          have hc : c = d := congrArg (fun s => s.fst.val) h
          subst d
          have hp : p = q := by cases h; rfl
          subst q
          congr
          exact Subsingleton.elim _ _

private theorem path_finite (a b : ℕ+) : Finite (Quiver.Path a b) := by
  induction b using (measure (fun b : ℕ+ => b.val)).wf.induction with
  | h b ih =>
      letI : Finite {c : ℕ+ // c.val < b.val} :=
        Finite.of_injective (fun c => (⟨c.val.val, c.property⟩ : Fin b.val)) (by
          intro c d h
          apply Subtype.ext
          apply Subtype.ext
          exact congrArg Fin.val h)
      letI (c : {c : ℕ+ // c.val < b.val}) : Finite (Quiver.Path a c.val) :=
        ih c.val c.property
      exact Finite.of_injective splitLast (splitLast_injective a b)

private def truncate {a b : ℕ+} (r : ℕ) (hb : b.val ≤ r)
    (p : Quiver.Path a b) : TruncatedPath r a b :=
  ⟨p, fun v hv => le_trans (vertices_bounds p v hv).2 hb⟩

private def truncationEquiv (r : ℕ) (a b : ℕ+) (hb : b.val ≤ r) :
    TruncatedPath r a b ≃ Quiver.Path a b where
  toFun := Subtype.val
  invFun := truncate r hb
  left_inv p := Subtype.ext rfl
  right_inv _ := rfl

private theorem consecutive_arc (n : ℕ+) :
    n.val + 1 ≤ jacoRight n.val := by
  rw [endpoint_eq_beatty]
  have := (beatty_bounds n.val n.property).1
  omega

private theorem path_nonempty (n : ℕ+) : Nonempty (Quiver.Path (1 : ℕ+) n) := by
  obtain ⟨n, hn⟩ := n
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hz : n = 0
      · subst n
        exact ⟨.nil⟩
      · obtain ⟨p⟩ := ih (by omega)
        exact ⟨p.cons (PLift.up ⟨by exact Nat.lt_succ_self n, consecutive_arc ⟨n, by omega⟩⟩)⟩

private theorem shortest_nonempty (n : ℕ+) : Nonempty (Shortest n) := by
  classical
  obtain ⟨p⟩ := path_nonempty n
  let P : ℕ → Prop := fun l => ∃ p : TruncatedPath n.val 1 n, p.val.length = l
  have hex : ∃ l, P l := ⟨p.length, truncate n.val le_rfl p, rfl⟩
  obtain ⟨q, hq⟩ := Nat.find_spec hex
  refine ⟨⟨q, ?_⟩⟩
  intro r
  have hr := Nat.find_min' hex (show P r.val.length from ⟨r, rfl⟩)
  omega

/-- Every own-truncation shortest-path set is finite and nonempty; later
truncations preserve the full directed path set, including each edge length. -/
theorem path_count_foundations (n : ℕ+) :
    Finite (Shortest n) ∧ Nonempty (Shortest n) ∧ 0 < psi n.val ∧
    (∀ r : ℕ, n.val ≤ r → ∃ e : TruncatedPath r 1 n ≃ TruncatedPath n.val 1 n,
      ∀ p, (e p).val.length = p.val.length) := by
  letI := path_finite (1 : ℕ+) n
  haveI : Finite (TruncatedPath n.val 1 n) := by unfold TruncatedPath; infer_instance
  haveI : Finite (Shortest n) := by unfold Shortest; infer_instance
  haveI := shortest_nonempty n
  refine ⟨inferInstance, inferInstance, ?_, ?_⟩
  · unfold psi
    split_ifs with hn
    · have he : (⟨n.val, hn⟩ : ℕ+) = n := Subtype.ext rfl
      rw [he]
      exact Nat.card_pos
    · exact (hn n.property).elim
  · intro r hr
    exact ⟨(truncationEquiv r 1 n hr).trans (truncationEquiv n.val 1 n le_rfl).symm,
      fun _ => rfl⟩

#print axioms path_count_foundations

private theorem endpoint_strict : StrictMono jacoRight :=
  strictMono_nat_of_lt_succ fun n => by
    have := jacoRight_succ_ge n
    omega

private theorem out_at_endpoint (m : ℕ) : beattyOut (jacoRight m) = m := by
  have hle : beattyOut (jacoRight m) ≤ m := by
    apply (beatty_threshold _ _).mp
    rw [← endpoint_eq_beatty]
  apply Nat.le_antisymm hle
  by_contra h
  have hlt : beattyOut (jacoRight m) < m := by omega
  have hreach : jacoRight m ≤ jacoRight (beattyOut (jacoRight m)) := by
    rw [endpoint_eq_beatty (beattyOut (jacoRight m))]
    exact (beatty_threshold _ _).mpr le_rfl
  exact (not_lt_of_ge hreach) (endpoint_strict hlt)

private theorem endpoint_fib (l : ℕ) :
    jacoRight (Nat.fib (l + 2)) = Nat.fib (l + 3) := by
  induction l with
  | zero => change jacoRight 1 = 2; decide +kernel
  | succ l ih =>
      have h := out_at_endpoint (Nat.fib (l + 2))
      rw [ih] at h
      rw [show l + 1 + 2 = l + 3 by omega, endpoint_eq_beatty, h]
      have hf := Nat.fib_add_two (n := l + 2)
      rw [show l + 2 + 1 = l + 3 by omega,
        show l + 2 + 2 = l + 1 + 3 by omega] at hf
      omega

private theorem reachable_prefix (l : ℕ) (n : ℕ+) :
    (∃ p : Quiver.Path (1 : ℕ+) n, p.length ≤ l) ↔ n.val ≤ Nat.fib (l + 2) := by
  induction l generalizing n with
  | zero =>
      constructor
      · rintro ⟨p, hp⟩
        have he := p.eq_of_length_zero (by omega)
        subst n
        decide
      · intro hn
        have hn1 : n = 1 := by
          apply Subtype.ext
          change n.val = 1
          apply Nat.le_antisymm
          · simpa only [Nat.zero_add, Nat.fib_two] using hn
          · exact n.property
        subst n
        exact ⟨.nil, le_rfl⟩
  | succ l ih =>
      constructor
      · rintro ⟨p, hp⟩
        cases p with
        | nil =>
            exact Nat.fib_pos.mpr (by omega)
        | @cons c n p e =>
            have hlen : p.length ≤ l := by
              change p.length + 1 ≤ l + 1 at hp
              omega
            have hc := (ih c).mp ⟨p, hlen⟩
            calc
              n.val ≤ jacoRight c.val := e.down.2
              _ ≤ jacoRight (Nat.fib (l + 2)) := endpoint_strict.monotone hc
              _ = Nat.fib (l + 1 + 2) := by simpa [Nat.add_assoc] using endpoint_fib l
      · intro hn
        by_cases hold : n.val ≤ Nat.fib (l + 2)
        · obtain ⟨p, hp⟩ := (ih n).mpr hold
          exact ⟨p, by omega⟩
        · let M : ℕ+ := ⟨Nat.fib (l + 2), Nat.fib_pos.mpr (by omega)⟩
          obtain ⟨p, hp⟩ := (ih M).mpr le_rfl
          have e : M ⟶ n := PLift.up ⟨by dsimp [M]; omega, by
            change n.val ≤ jacoRight (Nat.fib (l + 2))
            rw [endpoint_fib]
            simpa [Nat.add_assoc] using hn⟩
          exact ⟨p.cons e, Nat.add_le_add_right hp 1⟩

/-- The vertices reachable in at most l directed edges are exactly the positive
prefix ending at F_(l+2), and this is the same threshold for every shortest path. -/
theorem fibonacci_distance (l : ℕ) (n : ℕ+) :
    ((∃ p : TruncatedPath n.val 1 n, p.val.length ≤ l) ↔
      n.val ≤ Nat.fib (l + 2)) ∧
    (∀ p : Shortest n, p.val.val.length ≤ l ↔ n.val ≤ Nat.fib (l + 2)) := by
  constructor
  · constructor
    · rintro ⟨p, hp⟩
      exact (reachable_prefix l n).mp ⟨p.val, hp⟩
    · intro hn
      obtain ⟨p, hp⟩ := (reachable_prefix l n).mpr hn
      exact ⟨truncate n.val le_rfl p, hp⟩
  · intro p
    constructor
    · intro hp
      exact (reachable_prefix l n).mp ⟨p.val.val, hp⟩
    · intro hn
      obtain ⟨q, hq⟩ := (reachable_prefix l n).mpr hn
      exact le_trans (p.property (truncate n.val le_rfl q)) hq

#print axioms fibonacci_distance

private theorem beatty_mono : Monotone beattyOut := by
  intro i j hij
  apply Nat.floor_mono
  apply div_le_div_of_nonneg_right _ Real.goldenRatio_pos.le
  exact_mod_cast Nat.add_le_add_right hij 1

private theorem shortest_length_layer {j : ℕ} (hj : 3 ≤ j) (n : ℕ+)
    (hlo : Nat.fib j < n.val) (hhi : n.val ≤ Nat.fib (j + 1))
    (p : Shortest n) : p.val.val.length = j - 1 := by
  have hupper : p.val.val.length ≤ j - 1 := by
    have hpath : ∃ q : TruncatedPath n.val 1 n, q.val.length ≤ j - 1 := by
      have h := (fibonacci_distance (j - 1) n).1.mpr (by
        simpa only [show j - 1 + 2 = j + 1 by omega] using hhi)
      exact h
    obtain ⟨q, hq⟩ := hpath
    exact le_trans (p.property q) hq
  have hlower : j - 1 ≤ p.val.val.length := by
    by_contra h
    have hp : p.val.val.length ≤ j - 2 := by omega
    have hreach := (fibonacci_distance (j - 2) n).1.mp ⟨p.val, hp⟩
    have hidx : j - 2 + 2 = j := by omega
    rw [hidx] at hreach
    omega
  omega

private def Pred (n : ℕ+) (j : ℕ) :=
  {h : ℕ+ // beattyOut n.val ≤ h.val ∧ h.val ≤ Nat.fib j}

private instance predFinite (n : ℕ+) (j : ℕ) : Finite (Pred n j) :=
  Finite.of_injective
    (fun h => (⟨h.val.val, by have := h.property.2; omega⟩ : Fin (Nat.fib j + 1))) (by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg Fin.val hab)

private noncomputable instance predFintype (n : ℕ+) (j : ℕ) : Fintype (Pred n j) :=
  Fintype.ofFinite _

private instance shortestFinite (n : ℕ+) : Finite (Shortest n) := by
  letI := path_finite (1 : ℕ+) n
  unfold Shortest TruncatedPath
  infer_instance

private theorem pred_lt {j : ℕ} (hj : 3 ≤ j) {n : ℕ+}
    (hlo : Nat.fib j < n.val) {h : Pred n j} : h.val.val < n.val := by
  exact lt_of_le_of_lt h.property.2 hlo

private def pred_edge {j : ℕ} (hj : 3 ≤ j) {n : ℕ+}
    (hlo : Nat.fib j < n.val) (h : Pred n j) : (h.val : ℕ+) ⟶ n := by
  apply PLift.up
  constructor
  · exact pred_lt hj hlo
  · rw [endpoint_eq_beatty]
    exact (beatty_threshold n.val h.val.val).mpr h.property.1

private theorem fib_prev_endpoint {j : ℕ} (hj : 3 ≤ j) :
    jacoRight (Nat.fib (j - 1)) = Nat.fib j := by
  have h := endpoint_fib (j - 3)
  simpa only [show j - 3 + 2 = j - 1 by omega,
    show j - 3 + 3 = j by omega] using h

private theorem pred_lower {j : ℕ} (hj : 3 ≤ j) {n : ℕ+}
    (hlo : Nat.fib j < n.val) : Nat.fib (j - 1) < beattyOut n.val := by
  by_contra h
  have hreach := (beatty_threshold n.val (Nat.fib (j - 1))).mpr (by omega)
  rw [← endpoint_eq_beatty, fib_prev_endpoint hj] at hreach
  omega

private def shortest_prefix_is_shortest {j : ℕ} (hj : 3 ≤ j) {n : ℕ+}
    (hlo : Nat.fib j < n.val) (hhi : n.val ≤ Nat.fib (j + 1))
    (p : Shortest n) {c : ℕ+} (q : Quiver.Path (1 : ℕ+) c)
    (e : c ⟶ n) (hp : p.val.val = q.cons e) :
    Shortest c := by
  have hplen := shortest_length_layer hj n hlo hhi p
  have hq_len : q.length = j - 2 := by
    rw [hp, Quiver.Path.length_cons] at hplen
    omega
  refine ⟨truncate c.val le_rfl q, ?_⟩
  intro r
  let r' : TruncatedPath n.val 1 n :=
    ⟨r.val.cons e, by
      intro v hv
      rcases (Quiver.Path.mem_vertices_cons r.val e).mp hv with hv | rfl
      · exact le_trans (vertices_bounds r.val v hv).2 (Nat.le_of_lt e.down.1)
      · rfl⟩
  have hp' := p.property r'
  rw [hp] at hp'
  change q.length + 1 ≤ r.val.length + 1 at hp'
  change q.length ≤ r.val.length
  omega

private def suffixForward {j : ℕ} (hj : 3 ≤ j) {n : ℕ+}
    (hlo : Nat.fib j < n.val) (hhi : n.val ≤ Nat.fib (j + 1)) :
    Shortest n → Σ h : Pred n j, Shortest h.val := by
  intro p
  have hplen := shortest_length_layer hj n hlo hhi p
  have hpos : p.val.val.length ≠ 0 := by omega
  cases hpath : p.val.val with
  | nil =>
      exact (hpos (by simp [hpath])).elim
  | cons q e =>
      have hc_low : beattyOut n.val ≤ q.end.val := by
        have he := e.down.2
        rw [endpoint_eq_beatty] at he
        exact (beatty_threshold n.val q.end.val).mp he
      have hq_len : q.length = j - 2 := by
        rw [hpath, Quiver.Path.length_cons] at hplen
        omega
      have hc_high : q.end.val ≤ Nat.fib j := by
        have hqpath : ∃ r : TruncatedPath q.end.val 1 q.end,
            r.val.length ≤ j - 2 := by
          refine ⟨truncate q.end.val le_rfl q, ?_⟩
          change q.length ≤ j - 2
          omega
        have hc := (fibonacci_distance (j - 2) q.end).1.mp hqpath
        simpa only [show j - 2 + 2 = j by omega] using hc
      refine ⟨⟨q.end, hc_low, hc_high⟩, ?_⟩
      exact shortest_prefix_is_shortest hj hlo hhi p q e hpath

private noncomputable def suffixBackward {j : ℕ} (hj : 3 ≤ j) {n : ℕ+}
    (hlo : Nat.fib j < n.val) (hhi : n.val ≤ Nat.fib (j + 1)) :
    (Σ h : Pred n j, Shortest h.val) → Shortest n := by
  rintro ⟨h, q⟩
  let e : (h.val : ℕ+) ⟶ n := pred_edge hj hlo h
  have hlow : Nat.fib (j - 1) < h.val.val := by
    exact lt_of_lt_of_le (pred_lower hj hlo) h.property.1
  have hq_upper : q.val.val.length ≤ j - 2 := by
    have hpath : ∃ r : TruncatedPath h.val.val 1 h.val,
        r.val.length ≤ j - 2 := by
      have hh := (fibonacci_distance (j - 2) h.val).1.mpr (by
        simpa only [show j - 2 + 2 = j by omega] using h.property.2)
      exact hh
    obtain ⟨r, hr⟩ := hpath
    exact le_trans (q.property r) hr
  have hq_lower : j - 2 ≤ q.val.val.length := by
    by_contra hq
    have hq' : q.val.val.length ≤ j - 3 := by omega
    have hreach := (fibonacci_distance (j - 3) h.val).1.mp ⟨q.val, hq'⟩
    have hidx : j - 3 + 2 = j - 1 := by omega
    rw [hidx] at hreach
    omega
  have hq_len : q.val.val.length = j - 2 := by omega
  let p : TruncatedPath n.val 1 n :=
    ⟨q.val.val.cons e, by
      intro v hv
      rcases (Quiver.Path.mem_vertices_cons q.val.val e).mp hv with hv | rfl
      · exact le_trans (vertices_bounds q.val.val v hv).2
          (Nat.le_of_lt e.down.1)
      · rfl⟩
  refine ⟨p, ?_⟩
  have hp_len : p.val.length = j - 1 := by
    dsimp [p]
    change q.val.val.length + 1 = j - 1
    rw [hq_len]
    omega
  intro r
  by_contra hnot
  have hrlow : r.val.length ≤ j - 2 := by
    have : r.val.length < p.val.length := Nat.lt_of_not_ge hnot
    rw [hp_len] at this
    omega
  have hreach := (fibonacci_distance (j - 2) n).1.mp ⟨r, hrlow⟩
  have hidx : j - 2 + 2 = j := by omega
  rw [hidx] at hreach
  omega

private noncomputable def suffix_equiv {j : ℕ} (hj : 3 ≤ j) {n : ℕ+}
    (hlo : Nat.fib j < n.val) (hhi : n.val ≤ Nat.fib (j + 1)) :
    Shortest n ≃ Σ h : Pred n j, Shortest h.val := by
  let f := suffixForward hj hlo hhi
  let g := suffixBackward hj hlo hhi
  refine { toFun := f, invFun := g, left_inv := ?_, right_inv := ?_ }
  · intro p
    have hplen := shortest_length_layer hj n hlo hhi p
    rcases p with ⟨⟨path, htrunc⟩, hp⟩
    cases path with
    | nil =>
        change 0 = j - 1 at hplen
        omega
    | cons q e =>
        apply Subtype.ext
        dsimp [f, g, suffixForward, suffixBackward]
        congr 1
  · rintro ⟨h, q⟩
    apply Sigma.ext
    · apply Subtype.ext
      rfl
    · apply heq_of_eq
      apply Subtype.ext
      dsimp [f, g, suffixForward, suffixBackward]
      rfl

private theorem path_count_suffix {j : ℕ} (hj : 3 ≤ j) {n : ℕ+}
    (hlo : Nat.fib j < n.val) (hhi : n.val ≤ Nat.fib (j + 1)) :
    psi n.val = ∑ h : Pred n j, psi h.val.val := by
  have hncard : psi n.val = Nat.card (Shortest n) := by
    unfold psi
    split_ifs with hn
    · have heq : (⟨n.val, hn⟩ : ℕ+) = n := Subtype.ext rfl
      rw [heq]
    · exact (hn n.property).elim
  rw [hncard]
  rw [Nat.card_congr (suffix_equiv hj hlo hhi), Nat.card_sigma]
  congr 1
  funext h
  have hhcard : psi h.val.val = Nat.card (Shortest h.val) := by
    unfold psi
    split_ifs with hh
    · have heq : (⟨h.val.val, hh⟩ : ℕ+) = h.val := Subtype.ext rfl
      rw [heq]
    · exact (hh h.val.property).elim
  rw [hhcard]

#print axioms path_count_suffix

end D5.S3.ConceptDynamics.GraphColoring.JacoDirectedPathCount

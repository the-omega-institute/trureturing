/- GID: D5/S3/Arith/AffineNetworks/AffineModularStopping
   generality: G
   mirror-B: D5/B/S3/Arith/AffineNetworks/AffineModularStopping
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original all-path affine modulus, prime-loss coordinates, and named-edge recurrence
   are defined independently and connected by actual named-edge cycle erasure. -/

import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Combinatorics.Quiver.Path.Weight
import Mathlib.Combinatorics.Quiver.Path.Vertices
import Mathlib.Data.Nat.Factorization.Divisors
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.AffineNetworks.AffineModularStopping

open Quiver
open scoped BigOperators

structure Network where
  m : ℕ
  hm : 0 < m
  V : Type
  instV : Fintype V
  instVDec : DecidableEq V
  hV : Nonempty V
  E : Type
  instE : Fintype E
  instEDec : DecidableEq E
  src : E → V
  dst : E → V
  d : V → ℕ
  hd : ∀ v, 0 < d v ∧ d v ∣ m
  a : E → ℕ
  c : E → ZMod m

attribute [instance] Network.instV Network.instVDec Network.instE Network.instEDec

/-- The declared port readout on the full source `ZMod m`. -/
def portRead (N : Network) (v : N.V) (t : ZMod N.m) : ZMod (N.d v) :=
  (ZMod.castHom (N.hd v).2 (ZMod (N.d v))) t

/-- The original named edge type between two vertices.  Subtype identity retains
loops and parallel edges instead of collapsing them to a simple graph. -/
instance networkQuiver (N : Network) : Quiver N.V :=
  ⟨fun v w => {e : N.E // N.src e = v ∧ N.dst e = w}⟩

abbrev NPath (N : Network) (v w : N.V) :=
  Quiver.Path v w

/-- The original edge word carried by a path, with repeated occurrences retained. -/
def pathEdges {N : Network} {v w : N.V} (p : NPath N v w) : List N.E :=
  match p with
  | .nil => []
  | .cons q e => pathEdges q ++ [e.1]

/-- Product of the original natural edge multipliers along a named path. -/
def pathMultiplier {N : Network} {v w : N.V} (p : NPath N v w) : ℕ :=
  Quiver.Path.weight (fun {i j : N.V} (e : i ⟶ j) => N.a e.1) p

/-- The quotient contributed by one actual path to the all-path kernel. -/
def pathQuotient {N : Network} {v w : N.V} (p : NPath N v w) : ℕ :=
  N.d w / Nat.gcd (N.d w) (pathMultiplier p)

/-- The actual affine run transports one phase through the original named edge
word.  Appending an edge uses the original order of composition. -/
def pathRun {N : Network} {v w : N.V} (p : NPath N v w) (t : ZMod N.m) : ZMod N.m :=
  match p with
  | .nil => t
  | .cons q e => (N.a e.1 : ZMod N.m) * pathRun q t + N.c e.1

def pathOffset {N : Network} {v w : N.V} (p : NPath N v w) : ZMod N.m :=
  pathRun p 0

/-- The independent finite image of all actual-path quotients.  No path-length
cutoff occurs in this definition; finiteness comes only from `m.divisors`. -/
noncomputable def allPathDivisorImage (N : Network) (v : N.V) : Finset ℕ :=
  by
    classical
    exact N.m.divisors.filter (fun q => ∃ (w : N.V) (p : NPath N v w), pathQuotient p = q)

/-- The original all-path lcm modulus. -/
noncomputable def allPathModulus (N : Network) (v : N.V) : ℕ :=
  (allPathDivisorImage N v).lcm id

/-- The exact original gcd/lcm recurrence, using every outgoing named edge. -/
def iterate (N : Network) : ℕ → N.V → ℕ
  | 0, v => N.d v
  | n + 1, v =>
      Nat.lcm (N.d v)
        ((Finset.univ : Finset {e : N.E // N.src e = v}).lcm
          (fun e => iterate N n (N.dst e.1) /
            Nat.gcd (iterate N n (N.dst e.1)) (N.a e.1)))

/-- Actual simple paths are the paths whose vertex list has no repetition. -/
def ActualSimple {N : Network} {v w : N.V} (p : NPath N v w) : Prop :=
  p.vertices.Nodup

/-- The positive-part loss convention, including `ν_p(0)=+∞`, as a small
internal datatype rather than a finite valuation of zero. -/
inductive PrimeLoss where
  | finite (n : ℕ)
  | top
deriving DecidableEq, Repr

def PrimeLoss.add : PrimeLoss → PrimeLoss → PrimeLoss
  | .top, _ => .top
  | _, .top => .top
  | .finite a, .finite b => .finite (a + b)

def PrimeLoss.edge (p a : ℕ) : PrimeLoss :=
  if a = 0 then .top else .finite (Nat.factorization a p)

def PrimeLoss.positivePart : ℕ → PrimeLoss → ℕ
  | _, .top => 0
  | δ, .finite ℓ => δ - ℓ

def PrimeLoss.path {N : Network} {v w : N.V} (p : ℕ) (γ : NPath N v w) : PrimeLoss :=
  (pathEdges γ).foldl (fun acc e => PrimeLoss.add acc (PrimeLoss.edge p (N.a e))) (.finite 0)

def pathPrimeContribution {N : Network} {v w : N.V} (p : ℕ) (γ : NPath N v w) : ℕ :=
  Nat.factorization (pathQuotient γ) p

def pathPrimeLossContribution {N : Network} {v w : N.V} (p : ℕ) (γ : NPath N v w) : ℕ :=
  PrimeLoss.positivePart (Nat.factorization (N.d w) p) (PrimeLoss.path p γ)

def SimplePrimeMaximum (N : Network) (v : N.V) (p k : ℕ) : Prop :=
  (∀ (w : N.V) (γ : NPath N v w),
      pathPrimeLossContribution p γ ≤ k) ∧
    ∃ (w : N.V) (γ : NPath N v w), ActualSimple γ ∧
      γ.length ≤ Fintype.card N.V - 1 ∧
      k = pathPrimeLossContribution p γ

/-- Exact original prime-loss maximum and stopping statement, with no
certificate or assumed cycle-erasure or stability hypothesis. -/
def theorem11_3_claim (N : Network) : Prop :=
  (∀ v : N.V, 0 < allPathModulus N v ∧ allPathModulus N v ∣ N.m) ∧
  (∀ (v : N.V) (p : ℕ), p.Prime → p ∣ N.m →
      (∀ (w : N.V) (γ : NPath N v w),
        pathPrimeContribution p γ = pathPrimeLossContribution p γ) ∧
      SimplePrimeMaximum N v p (Nat.factorization (allPathModulus N v) p)) ∧
  (∀ (v : N.V) (n : ℕ), Fintype.card N.V - 1 ≤ n →
    iterate N n v = allPathModulus N v)

/-- Endpoint-preserving erasure on actual named-edge paths.  The surviving word
is an occurrence sublist, so its multiplier divides the original product even
when an original edge multiplier vanishes. -/
theorem actual_cycle_erasure {N : Network} {v w : N.V} (γ : NPath N v w) :
    ∃ η : NPath N v w, ActualSimple η ∧
      (pathEdges η).Sublist (pathEdges γ) ∧
      pathMultiplier η ∣ pathMultiplier γ ∧
      η.length ≤ Fintype.card N.V - 1 ∧
      ∀ p, match PrimeLoss.path p η, PrimeLoss.path p γ with
        | .finite a, .finite b => a ≤ b
        | _, .top => True
        | .top, .finite _ => False := by
  classical
  have word_comp : ∀ {i j k : N.V} (r : NPath N i j) (s : NPath N j k),
      pathEdges (r.comp s) = pathEdges r ++ pathEdges s := by
    intro i j k r s
    induction s with
    | nil => simp [pathEdges]
    | cons s e ih => simp [pathEdges, ih, List.append_assoc]
  have vertices_prefix : ∀ {i j k : N.V} (r : NPath N i j) (s : NPath N j k),
      r.vertices.Sublist (r.comp s).vertices := by
    intro i j k r s
    induction s with
    | nil => simp
    | @cons j k s e ih =>
        simpa only [Path.comp_cons, Path.vertices_cons, List.concat_eq_append] using
          ih.trans (List.sublist_append_left _ [k])
  have bound : ∀ {i j : N.V} (r : NPath N i j), ActualSimple r →
      r.length ≤ Fintype.card N.V - 1 := by
    intro i j r hr
    have hcard := List.Nodup.length_le_card hr
    rw [Path.vertices_length] at hcard
    omega
  have erased : ∃ η : NPath N v w, ActualSimple η ∧
      (pathEdges η).Sublist (pathEdges γ) ∧
      pathMultiplier η ∣ pathMultiplier γ ∧
      η.length ≤ Fintype.card N.V - 1 := by
    induction γ with
    | nil =>
        refine ⟨Path.nil, by simp [ActualSimple], by simp [pathEdges], ?_, ?_⟩
        · simp [pathMultiplier]
        · simp
    | @cons w x γ e ih =>
        obtain ⟨η, hs, hword, hmul, hlen⟩ := ih
        by_cases hx : x ∈ η.vertices
        · obtain ⟨r, s, heq⟩ := η.exists_eq_comp_of_mem_vertices hx
          have hr : ActualSimple r := (vertices_prefix r s).nodup (by
            change η.vertices.Nodup at hs
            rw [heq] at hs
            exact hs)
          refine ⟨r, hr, ?_, ?_, bound r hr⟩
          · have hpre : (pathEdges r).Sublist (pathEdges η) := by
              rw [heq, word_comp]
              exact List.sublist_append_left _ _
            exact (hpre.trans hword).trans (by
              change (pathEdges γ).Sublist (pathEdges γ ++ [e.1])
              exact List.sublist_append_left _ _)
          · have hrmul : pathMultiplier r ∣ pathMultiplier η := by
              rw [heq]
              exact ⟨pathMultiplier s, by simp [pathMultiplier, Path.weight_comp]⟩
            exact (hrmul.trans hmul).trans (by
              simpa only [pathMultiplier, Path.weight_cons] using
                dvd_mul_right (pathMultiplier γ) (N.a e.1))
        · have hs' : ActualSimple (η.cons e) := by
            rw [ActualSimple, Path.vertices_cons, List.concat_eq_append]
            rw [List.nodup_append]
            refine ⟨hs, by simp, ?_⟩
            intro a ha b hb hab
            rcases List.mem_singleton.mp hb with rfl
            exact hx (hab ▸ ha)
          refine ⟨η.cons e, hs', ?_, ?_, bound _ hs'⟩
          · exact hword.append (List.Sublist.refl [e.1])
          · simpa only [pathMultiplier, Path.weight_cons] using
              Nat.mul_dvd_mul_right hmul (N.a e.1)
  obtain ⟨η, hs, hw, hm, hl⟩ := erased
  refine ⟨η, hs, hw, hm, hl, ?_⟩
  intro p
  let leLoss : PrimeLoss → PrimeLoss → Prop
    | .finite a, .finite b => a ≤ b
    | _, .top => True
    | .top, .finite _ => False
  have trans : ∀ a b c, leLoss a b → leLoss b c → leLoss a c := by
    intro a b c hab hbc
    cases a <;> cases b <;> cases c <;> simp_all [leLoss]
    omega
  have grow : ∀ a b, leLoss a (PrimeLoss.add a b) := by
    intro a b
    cases a <;> cases b <;> simp [leLoss, PrimeLoss.add]
  have add_mono : ∀ a b c, leLoss a b →
      leLoss (PrimeLoss.add a c) (PrimeLoss.add b c) := by
    intro a b c h
    cases a <;> cases b <;> cases c <;> simp_all [leLoss, PrimeLoss.add]
  have fold_mono : ∀ {l₁ l₂ : List N.E}, l₁.Sublist l₂ →
      ∀ a b, leLoss a b →
      leLoss (l₁.foldl (fun acc e => PrimeLoss.add acc (PrimeLoss.edge p (N.a e))) a)
        (l₂.foldl (fun acc e => PrimeLoss.add acc (PrimeLoss.edge p (N.a e))) b) := by
    intro l₁ l₂ h
    induction h with
    | slnil => exact fun a b hab => hab
    | cons e h ih =>
        intro a b hab
        exact ih a _ (trans _ _ _ hab (grow b (PrimeLoss.edge p (N.a e))))
    | cons_cons e h ih =>
        intro a b hab
        exact ih _ _ (add_mono a b (PrimeLoss.edge p (N.a e)) hab)
  exact fold_mono hw (.finite 0) (.finite 0) (Nat.le_refl 0)

/-- The complete original prime-loss and stopping theorem.  Both the all-path
lcm and the outgoing-edge recurrence are the independent definitions above. -/
theorem theorem11_3 (N : Network) : theorem11_3_claim N := by
  classical
  have atten : ∀ (d a x : ℕ) (_ : 0 < d),
      d / Nat.gcd d a ∣ x ↔ d ∣ a * x := by
    intro d a x hd
    rw [Nat.div_dvd_iff_dvd_mul (Nat.gcd_dvd_left d a)
      (Nat.gcd_pos_of_pos_left a hd), Nat.dvd_gcd_mul_iff_dvd_mul]
  have qpos : ∀ {v w : N.V} (γ : NPath N v w), 0 < pathQuotient γ := by
    intro v w γ
    exact Nat.div_pos (Nat.gcd_le_left _ (N.hd w).1)
      (Nat.gcd_pos_of_pos_left _ (N.hd w).1)
  have qdvd : ∀ {v w : N.V} (γ : NPath N v w), pathQuotient γ ∣ N.m := by
    intro v w γ
    exact (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)).trans (N.hd w).2
  have image_mem : ∀ (v : N.V) (q : ℕ), q ∈ allPathDivisorImage N v ↔
      ∃ (w : N.V) (γ : NPath N v w), pathQuotient γ = q := by
    intro v q
    constructor
    · intro h
      exact (Finset.mem_filter.mp h).2
    · rintro ⟨w, γ, rfl⟩
      exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨qdvd γ, N.hm.ne'⟩,
        ⟨w, γ, rfl⟩⟩
  have domination : ∀ {v w : N.V} (γ η : NPath N v w),
      pathMultiplier η ∣ pathMultiplier γ → pathQuotient γ ∣ pathQuotient η := by
    intro v w γ η hmul
    apply (atten (N.d w) (pathMultiplier γ) (pathQuotient η) (N.hd w).1).mpr
    exact ((atten (N.d w) (pathMultiplier η) (pathQuotient η) (N.hd w).1).mp
      dvd_rfl).trans (Nat.mul_dvd_mul_right hmul _)
  have prime_identity : ∀ {v w : N.V} (p : ℕ) (γ : NPath N v w),
      pathPrimeContribution p γ = pathPrimeLossContribution p γ := by
    intro v w p γ
    have characterization :
        (pathMultiplier γ = 0 ∧ PrimeLoss.path p γ = .top) ∨
        ∃ k, pathMultiplier γ ≠ 0 ∧ PrimeLoss.path p γ = .finite k ∧
          Nat.factorization (pathMultiplier γ) p = k := by
      induction γ with
      | nil =>
          right
          exact ⟨0, by simp [pathMultiplier],
            by simp [PrimeLoss.path, pathEdges], by simp [pathMultiplier]⟩
      | cons q e ih =>
          have hmult : pathMultiplier (q.cons e) = pathMultiplier q * N.a e.1 :=
            Path.weight_cons _ q e
          have heq : PrimeLoss.path p (q.cons e) =
              PrimeLoss.add (PrimeLoss.path p q) (PrimeLoss.edge p (N.a e.1)) := by
            simp [PrimeLoss.path, pathEdges, List.foldl_append, PrimeLoss.add]
          rcases ih with ⟨hq, hloss⟩ | ⟨k, hq, hloss, hfactor⟩
          · left
            exact ⟨by simp [hmult, hq],
              by simp [heq, hloss, PrimeLoss.add]⟩
          · by_cases he : N.a e.1 = 0
            · left
              exact ⟨by simp [hmult, he],
                by simp [heq, hloss, PrimeLoss.edge, he, PrimeLoss.add]⟩
            · right
              refine ⟨k + Nat.factorization (N.a e.1) p, ?_, ?_, ?_⟩
              · simpa only [pathMultiplier, Path.weight_cons] using Nat.mul_ne_zero hq he
              · simp [heq, hloss, PrimeLoss.edge, he, PrimeLoss.add]
              · rw [hmult, Nat.factorization_mul hq he]
                simp [hfactor]
    rcases characterization with ⟨hzero, htop⟩ | ⟨k, hnonzero, hfinite, hfactor⟩
    · simp [pathPrimeContribution, pathPrimeLossContribution, pathQuotient,
        hzero, htop, PrimeLoss.positivePart]
    · have hdiv := congrArg (fun f : ℕ →₀ ℕ => f p)
          (Nat.factorization_div (Nat.gcd_dvd_left (N.d w) (pathMultiplier γ)))
      rw [Nat.factorization_gcd (N.hd w).1.ne' hnonzero] at hdiv
      have hsub : ((N.d w).factorization - (N.d w).factorization ⊓
          (pathMultiplier γ).factorization) p = (N.d w).factorization p - k := by
        change (N.d w).factorization p -
          ((N.d w).factorization ⊓ (pathMultiplier γ).factorization) p = _
        rw [Finsupp.inf_apply, hfactor]
        omega
      rw [hsub] at hdiv
      simpa [pathPrimeContribution, pathPrimeLossContribution, pathQuotient,
        hfinite, PrimeLoss.positivePart] using hdiv
  have iterate_dvd : ∀ n v, iterate N n v ∣ N.m := by
    intro n
    induction n with
    | zero => exact fun v => (N.hd v).2
    | succ n ih =>
        intro v
        apply Nat.lcm_dvd (N.hd v).2
        apply Finset.lcm_dvd
        intro e he
        exact (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)).trans (ih _)
  have iterate_pos : ∀ n v, 0 < iterate N n v := by
    intro n v
    have h := iterate_dvd n v
    by_contra hn
    have hz : iterate N n v = 0 := by omega
    rw [hz, zero_dvd_iff] at h
    exact N.hm.ne' h
  have bounded : ∀ (n : ℕ) (v : N.V) (x : ℕ), iterate N n v ∣ x ↔
      ∀ (w : N.V) (γ : NPath N v w), γ.length ≤ n →
        N.d w ∣ pathMultiplier γ * x := by
    intro n
    induction n with
    | zero =>
        intro v x
        constructor
        · intro h w γ hlen
          have hz : γ.length = 0 := by omega
          have hvw := Path.eq_of_length_zero γ hz
          subst w
          have hnil := Path.eq_nil_of_length_zero γ hz
          subst γ
          simpa [iterate, pathMultiplier] using h
        · intro h
          simpa [iterate, pathMultiplier] using h v Path.nil (by simp)
    | succ n ih =>
        intro v x
        constructor
        · intro h w γ hlen
          have hh := Nat.lcm_dvd_iff.mp h
          by_cases hz : γ.length = 0
          · have hvw := Path.eq_of_length_zero γ hz
            subst w
            have hnil := Path.eq_nil_of_length_zero γ hz
            subst γ
            simpa [pathMultiplier] using hh.1
          · obtain ⟨u, e, tail, heq, hlength⟩ :=
              (Path.length_ne_zero_iff_eq_comp γ).mp hz
            have hedge : iterate N n u / Nat.gcd (iterate N n u) (N.a e.1) ∣ x := by
              have hf := (Finset.lcm_dvd_iff.mp hh.2) ⟨e.1, e.2.1⟩ (Finset.mem_univ _)
              simpa only [e.2.2] using hf
            have htail := (ih u (N.a e.1 * x)).mp
              ((atten _ _ _ (iterate_pos n u)).mp hedge) w tail (by omega)
            simpa [heq, pathMultiplier, Path.weight_comp, Hom.toPath,
              Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using htail
        · intro h
          apply Nat.lcm_dvd
          · simpa [pathMultiplier] using h v Path.nil (by simp)
          · apply Finset.lcm_dvd
            intro e he
            apply (atten _ _ _ (iterate_pos n _)).mpr
            apply (ih _ _).mpr
            intro w tail htail
            let edge : (networkQuiver N).Hom v (N.dst e.1) :=
              ⟨e.1, e.2, rfl⟩
            have hh := h w (edge.toPath.comp tail) (by simp; omega)
            simpa [pathMultiplier, Path.weight_comp, Hom.toPath, edge,
              Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hh
  refine ⟨?_, ?_⟩
  · intro v
    have hdvd : allPathModulus N v ∣ N.m := by
      apply Finset.lcm_dvd
      intro q hq
      obtain ⟨w, γ, rfl⟩ := (image_mem v q).mp hq
      exact qdvd γ
    refine ⟨Nat.pos_of_ne_zero ?_, hdvd⟩
    intro hz
    rw [hz, zero_dvd_iff] at hdvd
    exact N.hm.ne' hdvd
  · constructor
    · intro v p hp hm
      refine ⟨fun w γ => prime_identity p γ, ?_⟩
      have hnonzero : ∀ q ∈ allPathDivisorImage N v, q ≠ 0 := by
        intro q hq
        obtain ⟨w, γ, rfl⟩ := (image_mem v q).mp hq
        exact (qpos γ).ne'
      have hf : Nat.factorization (allPathModulus N v) p =
          (allPathDivisorImage N v).sup (fun q => Nat.factorization q p) :=
        Finset.factorization_lcm hnonzero p
      have upper : ∀ (w : N.V) (γ : NPath N v w),
          pathPrimeLossContribution p γ ≤ Nat.factorization (allPathModulus N v) p := by
        intro w γ
        rw [← prime_identity p γ, hf]
        exact Finset.le_sup (f := fun q => Nat.factorization q p)
          ((image_mem v _).mpr ⟨w, γ, rfl⟩)
      have hmem : pathQuotient (Path.nil : NPath N v v) ∈ allPathDivisorImage N v :=
        (image_mem v _).mpr ⟨v, Path.nil, rfl⟩
      obtain ⟨q, hq, hmax⟩ := Finset.exists_mem_eq_sup (allPathDivisorImage N v)
        ⟨_, hmem⟩ (fun q => Nat.factorization q p)
      obtain ⟨w, γ, heq⟩ := (image_mem v q).mp hq
      obtain ⟨η, hsimple, hword, hmul, hlen, hloss⟩ := actual_cycle_erasure γ
      refine ⟨upper, w, η, hsimple, hlen, ?_⟩
      have hmono := (Nat.factorization_le_iff_dvd (qpos γ).ne' (qpos η).ne').mpr
        (domination γ η hmul) p
      have hupper := upper w η
      have hidentity := prime_identity p η
      have hidentityγ := prime_identity p γ
      unfold pathPrimeContribution at hidentity hidentityγ
      rw [← heq] at hmax
      omega
    · intro v n hn
      apply Nat.dvd_antisymm
      · apply (bounded n v (allPathModulus N v)).mpr
        intro w γ hlen
        apply (atten _ _ _ (N.hd w).1).mp
        exact Finset.dvd_lcm ((image_mem v _).mpr ⟨w, γ, rfl⟩)
      · apply Finset.lcm_dvd
        intro q hq
        obtain ⟨w, γ, rfl⟩ := (image_mem v q).mp hq
        obtain ⟨η, hsimple, hword, hmul, hlen, hloss⟩ := actual_cycle_erasure γ
        apply (domination γ η hmul).trans
        apply (atten _ _ _ (N.hd w).1).mpr
        exact (bounded n v (iterate N n v)).mp dvd_rfl w η (hlen.trans hn)

end D5.S3.Arith.AffineNetworks.AffineModularStopping

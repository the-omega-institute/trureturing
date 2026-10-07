/- GID: D5/S3/Combinatorics/AbelianBorders/MutualAbelianBorderDensity
   generality: I
   mirror-B: D5/B/S3/Combinatorics/AbelianBorders/MutualAbelianBorderDensity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Both binary mutual abelian-border densities have limits, with witnesses 1 and 0. -/
/-
proof_shape: result: content
escape_witness: form (2): result itself, through the injective encoding of border-free
  binary pairs as zero-avoiding walks, their reflection count, and the density squeeze.
admission_basis: open-problem-resolution (#13242; Proved)
Direct frozen dependencies:
  D5/S3/ConceptDynamics/ExperimentBoundary/BoundedRunSpace.Word; declaration statement_id: sha256:785cc7e93e8e79350640f22df253286057cbbbb946da45242cddbe1bc9942ca3
  D5/S3/StatisticalMechanics/RandomWalks/SurvivingWalkRecurrence.walks; declaration statement_id: sha256:71fd837a14eb899c0c820cbdfa37d1196776f6eb5d5e6ae7ca85c98950f78746
  D5/S3/Arith/AbsoluteValues/Heights/Gelfond.choose_middle_sq_mul_le; declaration statement_id: sha256:5abf01ef5f045d38584f3662fcc3705ed5830749345b3fc584e8058fe0df2e3a
  D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionDefs.heightAfter; declaration statement_id: sha256:8031371a0d6ac25411b4257ddc07ba754959ed555b98db10eedbf8a70c60266f
Same-delivery content: D5/S3/StatisticalMechanics/RandomWalks/WalkCount.walk_count.
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.Arith.AbsoluteValues.Heights.Gelfond
import D5.S3.Combinatorics.NarayanaStrip.CiglerStripExpansionDefs
import D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunSpace
import D5.S3.StatisticalMechanics.RandomWalks.SurvivingWalkRecurrence
import D5.S3.StatisticalMechanics.RandomWalks.WalkCount

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.AbelianBorders.MutualAbelianBorderDensity

open Finset Filter
open scoped Topology
open D5.S3.Combinatorics.NarayanaStrip.CiglerStripExpansionDefs (heightAfter)
open D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunSpace (Word)
open D5.S3.StatisticalMechanics.RandomWalks.SurvivingWalkRecurrence (walks)

def internal {n : ℕ} (p : Word n × Word n) : Prop :=
  ∃ r ∈ Finset.Icc 1 (n-1), ∀ b : Bool,
    ((List.ofFn p.1).drop (n-r)).count b = ((List.ofFn p.2).take r).count b

def external {n : ℕ} (p : Word n × Word n) : Prop :=
  ∃ r ∈ Finset.Icc 1 (n-1), ∀ b : Bool,
    ((List.ofFn p.1).take r).count b = ((List.ofFn p.2).drop (n-r)).count b

private instance {n : ℕ} (p : Word n × Word n) : Decidable (internal p) := by
  unfold internal
  infer_instance

private instance {n : ℕ} (p : Word n × Word n) : Decidable (external p) := by
  unfold external
  infer_instance

def M (n : ℕ) : ℕ := ((Finset.univ : Finset (Word n × Word n)).filter
  (fun p => internal p ∧ external p)).card

def Mbar (n : ℕ) : ℕ := ((Finset.univ : Finset (Word n × Word n)).filter
  (fun p => ¬ internal p ∧ ¬ external p)).card

def claim : Prop :=
  (∃ L : ℝ, Tendsto (fun n => (M n : ℝ) / 4^n) atTop (𝓝 L)) ∧
  (∃ L : ℝ, Tendsto (fun n => (Mbar n : ℝ) / 4^n) atTop (𝓝 L))

private def sign (b : Bool) : ℤ := if b then 1 else -1

private def weave : List Bool → List Bool → List Bool
  | a::u, b::v => a :: (!b) :: weave u v
  | _,_ => []

private def oriented (l : List Bool) (k : ℕ) : ℤ :=
  if l.head! then heightAfter l k else -heightAfter l k

private def trace (l : List Bool) (n : ℕ) : Fin (n+1) → ℕ :=
  fun i => (oriented l (i.val+1)-1).toNat

private def traceSet (n : ℕ) : Set (List Bool) :=
  {l | l.length=n+1 ∧ ∀ k, 1≤k → k≤n+1 → heightAfter l k ≠ 0}

private def lengthWords (n : ℕ) : Set (List Bool) := {l | l.length=n}

private def encoded {n : ℕ} (p : Word n × Word n) : List Bool :=
  weave (List.ofFn p.1).reverse (List.ofFn p.2)

private def N (n : ℕ) : ℕ := ((Finset.univ : Finset (Word n × Word n)).filter
  (fun p => ¬internal p)).card

theorem result : claim := by
  have swapped {n : ℕ} (p : Word n × Word n) :
      internal (p.2,p.1) ↔ external p := by
    simp only [internal, external]
    constructor <;> rintro ⟨r,hr,h⟩ <;> exact ⟨r,hr,fun b => (h b).symm⟩

  have central_vanish :
      Tendsto (fun n => (Nat.centralBinom n : ℝ) / 4^n) atTop (𝓝 0) := by
    have bound (n : ℕ) : ((Nat.centralBinom n : ℝ) / 4^n)^2 ≤ 1 / (2*(n:ℝ)+1) := by
      have h := Nat.choose_middle_sq_mul_le (2*n)
      rw [show 2*n/2=n by omega, ← Nat.centralBinom] at h
      have h' : (Nat.centralBinom n : ℝ)^2 * (2*(n:ℝ)+1) ≤ (4:ℝ)^(2*n) := by
        exact_mod_cast h
      have p : (0:ℝ) < 4^n := by positivity
      rw [div_pow, div_le_div_iff₀ (pow_pos p 2) (by positivity)]
      simpa [pow_mul, mul_comm] using h'
    have lim : Tendsto (fun n : ℕ => 1 / (2*(n:ℝ)+1)) atTop (𝓝 (0:ℝ)) :=
      tendsto_const_nhds.div_atTop ((tendsto_natCast_atTop_atTop.const_mul_atTop
        (by norm_num : (0:ℝ)<2)).atTop_add tendsto_const_nhds)
    have sq : Tendsto (fun n => ((Nat.centralBinom n : ℝ) / 4^n)^2) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds lim
        (fun n => sq_nonneg _) bound
    have heq : (fun n => Real.sqrt (((Nat.centralBinom n : ℝ) / 4^n)^2)) =
        (fun n => (Nat.centralBinom n : ℝ) / 4^n) := by
      funext n
      exact Real.sqrt_sq (by positivity)
    simpa only [heq, Real.sqrt_zero] using sq.sqrt

  have counts_total (l : List Bool) : l.count true + l.count false = l.length := by
    induction l with
    | nil => simp
    | cons b l ih => cases b <;> simp <;> omega

  have counts_iff (u v : List Bool) (h : u.length=v.length) :
      (∀ b : Bool, u.count b = v.count b) ↔ u.count true = v.count true := by
    constructor
    · intro h; exact h true
    · intro ht b
      have hu := counts_total u
      have hv := counts_total v
      cases b <;> omega

  have score_formula (l : List Bool) (r : ℕ) :
      heightAfter l r = 2*((l.take r).count true : ℤ) - (l.take r).length := by
    suffices h : ∀ l : List Bool, (l.map sign).sum = 2*(l.count true : ℤ) - l.length by
      exact h (l.take r)
    intro l
    induction l with
    | nil => simp
    | cons b l ih => cases b <;> simp [sign, ih] <;> omega

  have weave_length (u v : List Bool) (h : u.length=v.length) :
      (weave u v).length = 2*u.length := by
    induction u generalizing v with
    | nil => simp [weave]
    | cons a u ih =>
      cases v with
      | nil => simp at h
      | cons b v =>
        have he : u.length=v.length := by simpa using h
        simp only [weave, List.length_cons, ih v he]
        omega

  have weave_even (u v : List Bool) (r : ℕ) :
      u.length=v.length → heightAfter (weave u v) (2*r) =
        2*((u.take r).count true : ℤ) - 2*((v.take r).count true : ℤ) := by
    intro h
    induction r generalizing u v with
    | zero => simp [heightAfter]
    | succ r ih =>
      cases u with
      | nil => have : v=[] := List.length_eq_zero_iff.mp h.symm; subst v; simp [weave, heightAfter]
      | cons a u =>
        cases v with
        | nil => simp at h
        | cons b v =>
          have he : u.length=v.length := by simpa using h
          have step : 2*(r+1)=2*r+2 := by omega
          rw [step]
          simp only [weave, List.take_succ_cons, heightAfter, List.map_cons, List.sum_cons]
          change sign a + (sign (!b) + heightAfter (weave u v) (2*r)) = _
          rw [ih u v he]
          cases a <;> cases b <;> simp [sign] <;> omega

  have weave_injective {u v u' v' : List Bool}
      (h : u.length=v.length) (h' : u'.length=v'.length)
      (he : weave u v = weave u' v') : u=u' ∧ v=v' := by
    induction u generalizing v u' v' with
    | nil =>
      have hv : v=[] := List.length_eq_zero_iff.mp h.symm
      subst v
      cases u' with
      | nil => have hv' : v'=[] := List.length_eq_zero_iff.mp h'.symm; simp_all
      | cons a u' => cases v' <;> simp_all [weave]
    | cons a u ih =>
      cases v with
      | nil => simp at h
      | cons b v =>
        cases u' with
        | nil => have hv' : v'=[] := List.length_eq_zero_iff.mp h'.symm; simp_all [weave]
        | cons a' u' =>
          cases v' with
          | nil => simp at h'
          | cons b' v' =>
            simp only [weave, List.cons.injEq] at he
            have hb : b=b' := by simpa using he.2.1
            obtain ⟨hu,hv⟩ := ih (by simpa using h) (by simpa using h') he.2.2
            simp_all

  have score_step (l : List Bool) (k : ℕ) (h : k<l.length) :
      heightAfter l (k+1) = heightAfter l k + sign l[k] := by
    unfold heightAfter
    rw [List.take_succ_eq_append_getElem h]
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, sign]

  have score_unit (l : List Bool) (k : ℕ) (h : k<l.length) :
      heightAfter l (k+1) = heightAfter l k+1 ∨ heightAfter l (k+1)+1=heightAfter l k := by
    rw [score_step l k h]
    cases l[k] <;> simp [sign]

  have score_odd (l : List Bool) (k : ℕ) (h : 2*k+1≤l.length) :
      heightAfter l (2*k+1) ≠ 0 := by
    rw [score_formula]
    simp only [List.length_take, Nat.min_eq_left h, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one]
    omega

  have score_positive (l : List Bool) (N : ℕ) (hl : N≤l.length)
      (h0 : ∀ k, 1≤k → k≤N → heightAfter l k ≠ 0) :
      (∀ k, 1≤k → k≤N → 0<heightAfter l k) ∨ (∀ k, 1≤k → k≤N → heightAfter l k<0) := by
    by_cases first : 0<heightAfter l 1
    · left
      intro k hk hn
      induction k with
      | zero => omega
      | succ k ih =>
        by_cases hk0 : k=0
        · simpa [hk0] using first
        · have hp := ih (by omega) (by omega)
          have step := score_unit l k (by omega)
          have hn0 := h0 (k+1) (by omega) hn
          omega
    · right
      intro k hk hn
      induction k with
      | zero => omega
      | succ k ih =>
        by_cases hk0 : k=0
        · have hz := h0 1 (by omega) (by omega)
          simp only [hk0, zero_add]
          omega
        · have hp := ih (by omega) (by omega)
          have step := score_unit l k (by omega)
          have hn0 := h0 (k+1) (by omega) hn
          omega

  have score_first (l : List Bool) (h : 0<l.length) : heightAfter l 1=sign l.head! := by
    cases l with
    | nil => simp at h
    | cons b l => cases b <;> simp [heightAfter, sign]

  have oriented_positive (l : List Bool) (N : ℕ) (hl : N≤l.length)
      (h0 : ∀ k, 1≤k → k≤N → heightAfter l k ≠ 0) (k : ℕ) (hk : 1≤k) (hn : k≤N) :
      0 < oriented l k := by
    have hl0 : 0<l.length := by omega
    have hf := score_first l hl0
    rcases score_positive l N hl h0 with hp | hp
    · have hp1 := hp 1 (by omega) (by omega)
      have hb : l.head! = true := by cases h : l.head! <;> simp [h, sign] at hf ⊢ <;> omega
      simpa [oriented,hb] using hp k hk hn
    · have hp1 := hp 1 (by omega) (by omega)
      have hb : l.head! = false := by cases h : l.head! <;> simp [h, sign] at hf ⊢ <;> omega
      simp [oriented,hb]
      exact hp k hk hn

  have trace_signed (l : List Bool) (n : ℕ) (hl : n+1≤l.length)
      (h0 : ∀ k, 1≤k → k≤n+1 → heightAfter l k ≠ 0) (i : Fin (n+1)) :
      (trace l n i : ℤ) = oriented l (i.val+1)-1 := by
    apply Int.toNat_of_nonneg
    have hp := oriented_positive l (n+1) hl h0 (i.val+1) (by omega) (by omega)
    omega

  have trace_walk (l : List Bool) (n : ℕ) (hl : n+1≤l.length)
      (h0 : ∀ k, 1≤k → k≤n+1 → heightAfter l k ≠ 0) :
      trace l n 0=0 ∧ ∀ i : Fin n,
        trace l n i.succ=trace l n i.castSucc+1 ∨
        trace l n i.succ+1=trace l n i.castSucc := by
    constructor
    · have hf := score_first l (by omega)
      change (oriented l 1-1).toNat=0
      unfold oriented
      rw [hf]
      cases h : l.head! <;> simp [sign]
    · intro i
      have ha := trace_signed l n hl h0 i.castSucc
      have hb := trace_signed l n hl h0 i.succ
      have step := score_unit l (i.val+1) (by omega)
      simp only [Fin.val_castSucc, Fin.val_succ] at ha hb
      unfold oriented at ha hb
      split_ifs at ha hb <;> omega

  have scores_injective (l q : List Bool) (h : l.length=q.length)
      (hs : ∀ k, k≤l.length → heightAfter l k=heightAfter q k) : l=q := by
    apply List.ext_getElem h
    intro i hi hq
    have h1 := hs (i+1) (by omega)
    have h2 := hs i (by omega)
    rw [score_step l i hi, score_step q i hq] at h1
    have he : sign l[i]=sign q[i] := by omega
    cases hx : l[i] <;> cases hy : q[i] <;> simp [hx, hy, sign] at he ⊢

  have trace_injective (l q : List Bool) (n : ℕ)
      (hl : l.length=n+1) (hq : q.length=n+1)
      (h0 : ∀ k, 1≤k → k≤n+1 → heightAfter l k ≠ 0)
      (h0q : ∀ k, 1≤k → k≤n+1 → heightAfter q k ≠ 0)
      (hh : l.head! = q.head!) (ht : trace l n=trace q n) : l=q := by
    apply scores_injective l q (by omega)
    intro k hk
    by_cases hz : k=0
    · simp [hz,heightAfter]
    · let i : Fin (n+1) := ⟨k-1,by omega⟩
      have he := congrArg (fun x : ℕ => (x:ℤ)) (congrFun ht i)
      rw [trace_signed l n (by omega) h0 i, trace_signed q n (by omega) h0q i] at he
      have hi : i.val+1=k := by simp [i]; omega
      rw [hi] at he
      unfold oriented at he
      rw [hh] at he
      split_ifs at he <;> omega

  have lengthWords_card (n : ℕ) : (lengthWords n).ncard = 2^n := by
    change Nat.card (List.Vector Bool n) = _
    rw [Nat.card_congr (Equiv.vectorEquivFin Bool n), Nat.card_eq_fintype_card]
    simp

  have traceSet_finite (n : ℕ) : (traceSet n).Finite :=
    (List.finite_length_eq Bool (n+1)).subset (fun _ h => h.1)

  have traceSet_bound (n : ℕ) : (traceSet n).ncard ≤ 2*(walks n 0).ncard := by
    let f : List Bool → Bool × (Fin (n+1) → ℕ) := fun l => (l.head!, trace l n)
    have ht : ((Set.univ : Set Bool) ×ˢ walks n 0).Finite :=
      Set.finite_univ.prod (D5.S3.StatisticalMechanics.RandomWalks.WalkCount.walk_count walks (fun _ _ => rfl) n 0).1
    have h := Set.ncard_le_ncard_of_injOn f (t := Set.univ ×ˢ walks n 0) (s := traceSet n)
      (fun l hl => ⟨Set.mem_univ _, trace_walk l n hl.1.ge hl.2⟩)
      (by
        intro l hl q hq he
        apply trace_injective l q n hl.1 hq.1 hl.2 hq.2
        · exact congrArg Prod.fst he
        · exact congrArg Prod.snd he) ht
    simpa [Set.ncard_prod] using h

  have encoded_length {n : ℕ} (p : Word n × Word n) :
      (encoded p).length=2*n := by
    unfold encoded
    rw [weave_length _ _ (by simp), List.length_reverse, List.length_ofFn]

  have internal_walk {n : ℕ} (p : Word n × Word n) :
      internal p ↔ ∃ r ∈ Finset.Icc 1 (n-1), heightAfter (encoded p) (2*r)=0 := by
    have he (r : ℕ) : heightAfter (encoded p) (2*r) =
        2*(((List.ofFn p.1).drop (n-r)).count true : ℤ) -
        2*(((List.ofFn p.2).take r).count true : ℤ) := by
      rw [encoded, weave_even _ _ r (by simp)]
      simp only [List.take_reverse, List.length_ofFn, List.count_reverse]
    constructor
    · rintro ⟨r,hr,hc⟩
      refine ⟨r,hr,?_⟩
      rw [he r, hc true]
      omega
    · rintro ⟨r,hr,hc⟩
      refine ⟨r,hr,?_⟩
      have hrn : r≤n := by have := (Finset.mem_Icc.mp hr).2; omega
      have hlen : ((List.ofFn p.1).drop (n-r)).length = ((List.ofFn p.2).take r).length := by
        simp only [List.length_drop, List.length_take, List.length_ofFn,
          Nat.min_eq_left hrn]
        omega
      apply (counts_iff _ _ hlen).mpr
      rw [he r] at hc
      omega

  have no_internal_walk {n : ℕ} (p : Word n × Word n) (hp : ¬internal p) :
      ∀ k, 1≤k → k≤2*(n-1) → heightAfter (encoded p) k≠0 := by
    intro k hk hn
    rcases Nat.even_or_odd' k with ⟨r, rfl | rfl⟩
    · intro hc
      apply hp
      apply (internal_walk p).mpr
      exact ⟨r,Finset.mem_Icc.mpr ⟨by omega,by omega⟩,hc⟩
    · exact score_odd (encoded p) r (by rw [encoded_length]; omega)

  have encoded_injective {n : ℕ} :
      Function.Injective (encoded : Word n × Word n → List Bool) := by
    intro p q he
    have h := weave_injective (by simp) (by simp) he
    apply Prod.ext
    · exact List.ofFn_injective (List.reverse_injective h.1)
    · exact List.ofFn_injective h.2

  have N_ncard (n : ℕ) : N n = ({p : Word n × Word n | ¬internal p} : Set _).ncard := by
    rw [N, ← Set.ncard_coe_finset]
    congr 1
    ext p
    simp

  have odd_walk_count (m : ℕ) : (walks (2*m+1) 0).ncard = (2*m+1).choose m := by
    rw [(D5.S3.StatisticalMechanics.RandomWalks.WalkCount.walk_count walks (fun _ _ => rfl) (2*m+1) 0).2, ← Finset.sum_filter]
    have hs : (range (2*m+1+1)).filter (fun d => 2*m+1 < 2*d+0+2 ∧ 2*d≤2*m+1+0) = {m} := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      omega
    rw [hs, Finset.sum_singleton]

  have N_bound (m : ℕ) : N (m+2) ≤ 4*Nat.centralBinom (m+1) := by
    let f : Word (m+2) × Word (m+2) → List Bool × List Bool :=
      fun p => ((encoded p).take (2*m+2), (encoded p).drop (2*m+2))
    have ht : (traceSet (2*m+1) ×ˢ lengthWords 2).Finite :=
      (traceSet_finite _).prod (List.finite_length_eq Bool 2)
    have h := Set.ncard_le_ncard_of_injOn f (s := {p | ¬internal p})
      (t := traceSet (2*m+1) ×ˢ lengthWords 2) (by
        intro p hp
        have hlen := encoded_length p
        constructor
        · constructor
          · simp only [f, List.length_take, hlen]
            omega
          · intro k hk hn
            have hz := no_internal_walk p hp k hk (by omega)
            simpa only [f, heightAfter, List.take_take, Nat.min_eq_left (by omega : k≤2*m+2)] using hz
        · change ((encoded p).drop (2*m+2)).length=2
          rw [List.length_drop, hlen]
          omega)
      (by
        intro p hp q hq he
        have ha := congrArg Prod.fst he
        have hb := congrArg Prod.snd he
        apply encoded_injective
        have hc := congrArg₂ (fun a b : List Bool => a++b) ha hb
        simpa only [f,List.take_append_drop] using hc) ht
    rw [← N_ncard, Set.ncard_prod, lengthWords_card] at h
    have hb := traceSet_bound (2*m+1)
    rw [odd_walk_count] at hb
    have hc : Nat.centralBinom (m+1)=2*(2*m+1).choose m := by
      rw [Nat.centralBinom, show 2*(m+1)=2*m+1+1 by omega,
        Nat.choose_succ_succ']
      have hs : (2*m+1).choose (m+1)=(2*m+1).choose m :=
        Nat.choose_symm_of_eq_add (by omega)
      rw [hs]
      omega
    rw [hc]
    norm_num at h
    omega

  have all_pairs_card (n : ℕ) : Fintype.card (Word n × Word n)=4^n := by
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    rw [← mul_pow]
    norm_num

  have M_ncard (n : ℕ) : M n = ({p : Word n × Word n | internal p ∧ external p} : Set _).ncard := by
    rw [M, ← Set.ncard_coe_finset]
    congr 1
    ext p
    simp

  have Mbar_ncard (n : ℕ) : Mbar n = ({p : Word n × Word n | ¬internal p ∧ ¬external p} : Set _).ncard := by
    rw [Mbar, ← Set.ncard_coe_finset]
    congr 1
    ext p
    simp

  have no_external_card (n : ℕ) :
      ({p : Word n × Word n | ¬external p} : Set _).ncard = N n := by
    have heq : ({p : Word n × Word n | ¬external p} : Set _) =
        Prod.swap '' {p : Word n × Word n | ¬internal p} := by
      ext p
      constructor
      · intro hp
        change ¬external p at hp
        refine ⟨Prod.swap p, ?_, Prod.swap_swap p⟩
        change ¬internal (p.2,p.1)
        simpa only [swapped] using hp
      · rintro ⟨q,hq,rfl⟩
        change ¬internal q at hq
        change ¬external (q.2,q.1)
        simpa only [← swapped, Prod.swap_swap] using hq
    rw [heq, Set.ncard_image_of_injective _ Prod.swap_injective, ← N_ncard]

  have count_bounds (n : ℕ) :
      M n≤4^n ∧ 4^n-M n≤2*N n ∧ Mbar n≤N n := by
    classical
    have hM : M n≤4^n := by
      rw [M, ← all_pairs_card]
      exact Finset.card_filter_le _ _
    refine ⟨hM,?_,?_⟩
    · let s : Set (Word n × Word n) := {p | internal p ∧ external p}
      have hsc : sᶜ = {p | ¬internal p} ∪ {p | ¬external p} := by
        ext p
        simp only [s, Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_union]
        tauto
      have h := Set.ncard_union_le ({p : Word n × Word n | ¬internal p}) {p | ¬external p}
      rw [← hsc, Set.ncard_compl, Nat.card_eq_fintype_card, all_pairs_card, ← M_ncard,
        ← N_ncard, no_external_card] at h
      simpa only [two_mul] using h
    · rw [Mbar_ncard, N_ncard]
      exact Set.ncard_le_ncard (fun p hp => hp.1)

  have N_vanish : Tendsto (fun n => (N n : ℝ)/4^n) atTop (𝓝 0) := by
    rw [← tendsto_add_atTop_iff_nat 2]
    have hc := central_vanish.comp (tendsto_add_atTop_nat 1)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc
    · intro n
      positivity
    · intro n
      have hb : (N (n+2) : ℝ) ≤ 4*(Nat.centralBinom (n+1) : ℝ) := by
        exact_mod_cast N_bound n
      calc (N (n+2) : ℝ)/4^(n+2) ≤ (4*(Nat.centralBinom (n+1) : ℝ))/4^(n+2) :=
          div_le_div_of_nonneg_right hb (by positivity)
        _ = (Nat.centralBinom (n+1) : ℝ)/4^(n+1) := by
          rw [show n+2=n+1+1 by omega, pow_succ]
          field_simp

  have hN2 : Tendsto (fun n => 2*((N n : ℝ)/4^n)) atTop (𝓝 (0:ℝ)) := by
    simpa using N_vanish.const_mul 2
  have hM : Tendsto (fun n => (M n : ℝ)/4^n) atTop (𝓝 (1:ℝ)) := by
    have hlow : Tendsto (fun n => 1-2*((N n : ℝ)/4^n)) atTop (𝓝 (1:ℝ)) := by
      simpa using tendsto_const_nhds.sub hN2
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
    · intro n
      have hbounds := count_bounds n
      have hm : (M n : ℝ) ≤ (4:ℝ)^n := by exact_mod_cast hbounds.1
      have hd : (4:ℝ)^n-(M n : ℝ) ≤ 2*(N n : ℝ) := by
        have hb : ((4^n-M n : ℕ) : ℝ) ≤ 2*(N n : ℝ) := by
          exact_mod_cast hbounds.2.1
        rw [Nat.cast_sub hbounds.1] at hb
        norm_cast at hb ⊢
      have hp : (0:ℝ)<4^n := by positivity
      rw [le_div_iff₀ hp]
      field_simp
      nlinarith
    · intro n
      rw [div_le_one (by positivity)]
      have hb : M n≤4^n := (count_bounds n).1
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using
        (Nat.cast_le.mpr hb : (M n : ℝ) ≤ ((4^n : ℕ) : ℝ))
  have hMb : Tendsto (fun n => (Mbar n : ℝ)/4^n) atTop (𝓝 (0:ℝ)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds N_vanish
    · intro n
      positivity
    · intro n
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hb : Mbar n≤N n := (count_bounds n).2.2
      exact Nat.cast_le.mpr hb
  exact ⟨⟨1,hM⟩,⟨0,hMb⟩⟩

end D5.S3.Combinatorics.AbelianBorders.MutualAbelianBorderDensity

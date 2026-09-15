/- GID: D5/S1/Digit/Infinite/MarkerHyperfiniteness
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/MarkerHyperfiniteness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Shrinking circle markers yield increasing finite Borel equivalences exhausting rotation orbits and asynchronous merging of legal streams. -/

import D5.S1.Digit.Infinite.WindowSuccessorGraph
import D5.S1.Digit.Infinite.PhaseOrbitRelations

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.MarkerHyperfiniteness
open Set
open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Digit.Infinite.SignedSeriesRange
open D5.S1.Digit.Infinite.SignedSeriesFibres
open D5.S1.Digit.Infinite.WindowSuccessorGraph (G)
open D5.S1.Digit.Infinite.MultiplierObstruction
open D5.S1.Digit.Infinite.PhaseOrbitRelations
/-- The real circle with circumference one. -/
abbrev MarkerCircle := AddCircle (1 : ℝ)
/-- The length of the nth marker arc. -/
noncomputable def markerEll (n : ℕ) : ℝ := 1 / ((n:ℝ)+2)

/-- The image of the open interval from zero to the nth marker length in the circle. -/
noncomputable def markerU (n : ℕ) : Set MarkerCircle :=
  (fun x : ℝ => (x : MarkerCircle)) '' Set.Ioo 0 (markerEll n)

/-- The least positive odd index whose corresponding power of alpha is below the marker length. -/
noncomputable def markerJ (n : ℕ) : ℕ := Nat.find (show ∃ j : ℕ, 1 ≤ j ∧ j%2=1 ∧ alpha^(j+2)< markerEll n  from by
  have ha : 0 < alpha := inv_pos.mpr Real.goldenRatio_pos
  have hb : alpha < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have he : 0 < markerEll n := by unfold markerEll; positivity
  obtain ⟨k,hk⟩ := exists_pow_lt_of_lt_one he hb
  refine ⟨2*k+1,by omega,by omega,?_⟩
  have hm : alpha^(2*k+1+2) ≤ alpha^k :=
    pow_le_pow_of_le_one ha.le hb.le (by omega)
  exact hm.trans_lt hk)

/-- The small rotation increment selected by the nth marker index. -/
noncomputable def markerH (n : ℕ) : ℝ := alpha^(markerJ n+2)

/-- The Fibonacci return time selected by the nth marker index. -/
noncomputable def markerQ (n : ℕ) : ℕ := G (markerJ n)

/-- The natural floor of the reciprocal of the positive marker increment. -/
noncomputable def markerM (n : ℕ) : ℕ := ⌊1 / markerH n⌋₊

/-- The uniform bound on the time needed to visit the nth marker arc. -/
noncomputable def markerB (n : ℕ) : ℕ := markerQ n * markerM n

/-- The bound on the distance between adjacent deleted edge sources. -/
noncomputable def markerL (n : ℕ) : ℕ := markerB n+1

/-- Integer iterates of rotation by the golden ratio on the circle. -/
noncomputable def rotate (k : ℤ) (x : MarkerCircle) : MarkerCircle :=
  x + k • (Real.goldenRatio : MarkerCircle)

/-- A directed rotation edge retained exactly when its source is outside the marker arc. -/
def remainingEdge (n : ℕ) (x y : MarkerCircle) : Prop := x ∉ markerU n ∧ y=rotate 1 x

/-- Connectivity by finite undirected paths of retained rotation edges, including empty paths. -/
def markerF (n : ℕ) : MarkerCircle → MarkerCircle → Prop :=
  Relation.ReflTransGen (fun x y => remainingEdge n x y ∨ remainingEdge n y x)

/-- The pullback of the nth circle path relation along the phase map of legal streams. -/
def markerG (n : ℕ) (x y : LegalDigits) : Prop := markerF n (phase x) (phase y)

/-- Every integer interval of the specified length contains a visit to the marker arc. -/
def VisitBoundSpec : Prop := ∀ n (x : MarkerCircle) (a : ℤ),
  ∃ k : ℤ, a ≤ k ∧ k ≤ a+(markerB n:ℤ) ∧ rotate k x ∈ markerU n

/-- An equivalence relation whose graph belongs to the Borel sigma algebra of the product topology. -/
def BorelEquivalence {X : Type*} [TopologicalSpace X] (E : X → X → Prop) : Prop :=
  Equivalence E ∧ @MeasurableSet (X × X) (borel (X × X)) {p | E p.1 p.2}

/-- An increasing family indexed by all natural numbers of finite Borel equivalences exhausting a relation. -/
def Hyperfinite {X : Type*} [TopologicalSpace X] (E : X → X → Prop) : Prop :=
  ∃ F : ℕ → X → X → Prop, Monotone F ∧
    (∀ n, BorelEquivalence (F n) ∧ ∀ x, Set.Finite {y | F n x y}) ∧
    ∀ x y, E x y ↔ ∃ n, F n x y

/-- A forward or backward step of the circle rotation, according to a Boolean letter. -/
noncomputable def step (b : Bool) (x : MarkerCircle) : MarkerCircle := rotate (if b then 1 else -1) x

/-- A step is permitted exactly when the source of its underlying directed edge is unmarked. -/
def allowed (n : ℕ) (b : Bool) (x : MarkerCircle) : Prop :=
  (if b then x else rotate (-1) x) ∉ markerU n

/-- The endpoint reached by following a finite Boolean word of rotation steps. -/
noncomputable def walk : List Bool → MarkerCircle → MarkerCircle
  | [], x => x
  | b::bs, x => walk bs (step b x)

/-- Every step of a finite Boolean word is permitted from its successive starting points. -/
def valid (n : ℕ) : List Bool → MarkerCircle → Prop
  | [], _ => True
  | b::bs, x => allowed n b x ∧ valid n bs (step b x)

set_option maxHeartbeats 800000 in
/-- Shrinking open markers have uniformly bounded return gaps. Their undirected path relations
form increasing finite Borel equivalences exhausting circle rotation orbits; pulling them back
along phase gives such equivalences for asynchronous merging, with at most twice the class size. -/
theorem marker_hyperfiniteness :
    (∀ n, IsOpen (markerU n)) ∧ Antitone markerU ∧ (⋂ n, markerU n) = ∅ ∧
    VisitBoundSpec ∧
    (∀ n (x : MarkerCircle),
      (∀ b : ℤ, ∃ k : ℤ, b ≤ k ∧ rotate k x ∈ markerU n) ∧
      (∀ b : ℤ, ∃ k : ℤ, k ≤ b ∧ rotate k x ∈ markerU n) ∧
      (∀ c d : ℤ, c<d → rotate c x ∈ markerU n → rotate d x ∈ markerU n →
        (∀ k : ℤ, c<k → k<d → rotate k x ∉ markerU n) → d-c ≤ (markerL n:ℤ))) ∧
    (∀ n, BorelEquivalence (markerF n) ∧ ∀ t,
      Set.Finite {s | markerF n t s} ∧ {s | markerF n t s}.ncard ≤ markerL n) ∧
    Monotone markerF ∧ (∀ t s, ER t s ↔ ∃ n, markerF n t s) ∧
    (∀ n, BorelEquivalence (markerG n) ∧ ∀ x,
      Set.Finite {y | markerG n x y} ∧ {y | markerG n x y}.ncard ≤ 2 * markerL n) ∧
    Monotone markerG ∧ (∀ x y, ET x y ↔ ∃ n, markerG n x y) ∧
    Hyperfinite ER ∧ Hyperfinite ET := by
  classical
  have ell_bounds (n : ℕ) : 0 < markerEll n ∧ markerEll n ≤ 1 / 2 := by
    constructor
    · unfold markerEll; positivity
    · exact one_div_le_one_div_of_le (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have ell_antitone : Antitone markerEll := by
    intro m n h
    apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < m + 2)
    exact_mod_cast Nat.add_le_add_right h 2
  have mem_marker (n : ℕ) (c : MarkerCircle) :
      c ∈ markerU n ↔ 0 < (AddCircle.equivIco (1 : ℝ) 0 c).val ∧
        (AddCircle.equivIco (1 : ℝ) 0 c).val < markerEll n := by
    let t := AddCircle.equivIco (1 : ℝ) 0 c
    have ht : t.val ∈ Ico (0 : ℝ) (0+1) := t.property
    have htc : (t.val : MarkerCircle) = c := AddCircle.coe_equivIco
    have hbound := ell_bounds n
    constructor
    · rintro ⟨r,hr,he⟩
      have he' : r = t.val := (AddCircle.coe_eq_coe_iff_of_mem_Ico
        (show r ∈ Ico (0 : ℝ) (0+1) from ⟨hr.1.le,by linarith [hr.2]⟩) ht).mp
          (he.trans htc.symm)
      rw [he'] at hr
      exact hr
    · intro h
      exact ⟨t.val,h,htc⟩
  have marker_arc (n : ℕ) :
      (markerU n).Nonempty ∧ IsOpen (markerU n) ∧
      Set.InjOn (fun r : ℝ => (r : MarkerCircle)) (Ioo 0 (markerEll n)) := by
    have hb := ell_bounds n
    refine ⟨?_,?_,?_⟩
    · exact ⟨((markerEll n / 2 : ℝ) : MarkerCircle),⟨markerEll n / 2,⟨by linarith,by linarith⟩,rfl⟩⟩
    · exact QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
    · intro x hx y hy he
      exact (AddCircle.coe_eq_coe_iff_of_mem_Ico
        (show x ∈ Ico (0 : ℝ) (0+1) from ⟨hx.1.le,by linarith [hx.2]⟩)
        (show y ∈ Ico (0 : ℝ) (0+1) from ⟨hy.1.le,by linarith [hy.2]⟩)).mp he
  have marker_decreasing : Antitone markerU := by
    intro m n h c hc
    obtain ⟨r,hr,he⟩ := hc
    exact ⟨r,⟨hr.1,lt_of_lt_of_le hr.2 (ell_antitone h)⟩,he⟩
  have marker_empty_inter : (⋂ n, markerU n) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro c hc
    have all : ∀ n, c ∈ markerU n := mem_iInter.mp hc
    have hp := ((mem_marker 0 c).mp (all 0)).1
    obtain ⟨n,hn⟩ := exists_nat_one_div_lt hp
    have he : markerEll n ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    have ht := ((mem_marker n c).mp (all n)).2
    linarith
  have odd_small_exists (n : ℕ) : ∃ j : ℕ, 1 ≤ j ∧ j%2=1 ∧ alpha^(j+2)< markerEll n := by
    have ha : 0 < alpha := inv_pos.mpr Real.goldenRatio_pos
    have hb : alpha < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
    have he : 0 < markerEll n := by unfold markerEll; positivity
    obtain ⟨k,hk⟩ := exists_pow_lt_of_lt_one he hb
    refine ⟨2*k+1,by omega,by omega,?_⟩
    have hm : alpha^(2*k+1+2) ≤ alpha^k :=
      pow_le_pow_of_le_one ha.le hb.le (by omega)
    exact hm.trans_lt hk
  have marker_parameters (n : ℕ) :
      1 ≤ markerJ n ∧ markerJ n%2=1 ∧ 0 <  markerH n ∧ markerH n< markerEll n := by
    have hs := Nat.find_spec (odd_small_exists n)
    exact ⟨hs.1, hs.2.1, pow_pos (inv_pos.mpr Real.goldenRatio_pos) _, hs.2.2⟩
  have marker_geometry :
      (∀ n, (markerU n).Nonempty ∧ IsOpen (markerU n)) ∧
      Antitone markerU ∧ (⋂ n, markerU n) = ∅ :=
    ⟨fun n => ⟨(marker_arc n).1,(marker_arc n).2.1⟩,
      marker_decreasing,marker_empty_inter⟩
  have coefficient (j : ℕ) :
      (-1 : ℝ) ^ (j + 1) * alpha ^ (j + 2) =
      Real.goldenRatio * (Nat.fib (j + 2) : ℝ) - (Nat.fib (j + 3) : ℝ) := by
    have e := Real.fib_succ_sub_goldenRatio_mul_fib (j + 2)
    have hc : Real.goldenConj = -alpha := by
      dsimp [alpha]
      have hi := Real.inv_goldenRatio
      linarith [hi]
    have hsign : (-alpha) ^ (j + 2) =
        -((-1 : ℝ) ^ (j + 1) * alpha ^ (j + 2)) := by
      rw [neg_eq_neg_one_mul, mul_pow]
      simp only [show j + 2 = (j + 1) + 1 by omega, pow_succ]
      ring
    rw [hc, hsign] at e
    have hi : j + 2 + 1 = j + 3 := by omega
    rw [hi] at e
    linarith
  have grid_hits (δ ε θ : ℝ) (hδ : 0 < δ) (hδε : δ < ε) (hε : ε ≤ 1)
      (hθ : 0 ≤ θ) (hθ1 : θ < 1) :
      ∃ i : ℕ, i ≤ ⌊1/δ⌋₊ ∧
        ∃ r : ℝ, 0 < r ∧ r < ε ∧ ((θ+(i:ℝ)*δ : ℝ) : MarkerCircle) = (r:MarkerCircle) := by
    by_cases hz : θ=0
    · subst θ
      refine ⟨1,?_,δ,hδ,hδε,by simp⟩
      apply (Nat.le_floor_iff (by positivity)).mpr
      apply (le_div_iff₀ hδ).mpr
      norm_num
      linarith
    by_cases he : θ<ε
    · exact ⟨0,by omega,θ,lt_of_le_of_ne hθ (Ne.symm hz),he,by simp⟩
    let q := ⌊(1-θ)/δ⌋₊
    have hp : 0 ≤ (1-θ)/δ := div_nonneg (by linarith) hδ.le
    have hf : (q:ℝ) ≤ (1-θ)/δ := Nat.floor_le hp
    have hg : (1-θ)/δ < (q:ℝ)+1 := Nat.lt_floor_add_one _
    have hfm : (q:ℝ)*δ ≤ 1-θ := (le_div_iff₀ hδ).mp hf
    have hgm : 1-θ < ((q:ℝ)+1)*δ := (div_lt_iff₀ hδ).mp hg
    refine ⟨q+1,?_,θ+((q:ℝ)+1)*δ-1,by linarith,by nlinarith,?_⟩
    · apply (Nat.le_floor_iff (by positivity)).mpr
      apply (le_div_iff₀ hδ).mpr
      push_cast
      nlinarith
    · have hone : ((1:ℝ):MarkerCircle)=0 := (AddCircle.coe_eq_zero_iff (1:ℝ)).mpr ⟨1,by simp⟩
      rw [AddCircle.coe_sub,hone,sub_zero]
      norm_cast
  have golden_marker_step (n : ℕ) :
      ((markerQ n : ℝ) * Real.goldenRatio : MarkerCircle) = ((markerH n : ℝ):MarkerCircle) := by
    have hj := marker_parameters n
    have hs := coefficient (markerJ n)
    have hsign : (-1:ℝ)^(markerJ n+1)=1 := by
      exact Even.neg_one_pow (even_iff_two_dvd.mpr (Nat.dvd_of_mod_eq_zero (by omega)))
    rw [hsign,one_mul] at hs
    have hreal : (markerQ n:ℝ)*Real.goldenRatio = markerH n+(G (markerJ n+1):ℝ) := by
      simpa [markerQ,markerH,G,Nat.add_assoc,mul_comm] using (eq_add_of_sub_eq hs.symm)
    rw [hreal,AddCircle.coe_add]
    have hz : ((G (markerJ n+1):ℝ):MarkerCircle)=0 :=
      (AddCircle.coe_eq_zero_iff (1:ℝ)).mpr ⟨G (markerJ n+1),by simp⟩
    rw [hz,add_zero]
  have visit_bound : VisitBoundSpec := by
    intro n x a
    let y := rotate a x
    let θ := (AddCircle.equivIco (1:ℝ) 0 y).val
    have hθ : 0 ≤ θ ∧ θ < 1 := by
      simpa using (AddCircle.equivIco (1:ℝ) 0 y).property
    have hθy : ((θ:ℝ):MarkerCircle)=y := AddCircle.coe_equivIco
    have hp := marker_parameters n
    have he : markerEll n ≤ 1 := (ell_bounds n).2.trans (by norm_num)
    obtain ⟨i,hi,r,hr0,hre,hri⟩ := grid_hits (markerH n) (markerEll n) θ
      hp.2.2.1 hp.2.2.2 he hθ.1 hθ.2
    refine ⟨a+(i:ℤ)*(markerQ n:ℤ),?_,?_,r,⟨hr0,hre⟩,?_⟩
    · have : (0:ℤ) ≤ (i:ℤ)*(markerQ n:ℤ) := mul_nonneg (by positivity) (by positivity)
      omega
    · have hm : i*markerQ n ≤ markerB n := by
        unfold markerB
        exact (Nat.mul_le_mul_right (markerQ n) hi).trans_eq (Nat.mul_comm _ _)
      exact_mod_cast (show a+(i:ℤ)*(markerQ n:ℤ) ≤ a+(markerB n:ℤ) by omega)
    · have hstep := golden_marker_step n
      have ht : rotate (a+(i:ℤ)*(markerQ n:ℤ)) x =
          ((θ+(i:ℝ)*markerH n:ℝ):MarkerCircle) := by
        simp only [rotate,add_zsmul,mul_zsmul,← add_assoc]
        change y + (i:ℤ) • ((markerQ n:ℤ) • (Real.goldenRatio:MarkerCircle)) = _
        rw [← hθy,AddCircle.coe_add]
        congr 1
        have hstep' : (markerQ n:ℤ) • (Real.goldenRatio:MarkerCircle) =
            ((markerH n:ℝ):MarkerCircle) := by
          rw [← AddCircle.coe_zsmul]
          simpa [zsmul_eq_mul] using hstep
        rw [hstep',← AddCircle.coe_zsmul]
        simp [zsmul_eq_mul]
      exact hri.symm.trans ht.symm
  have visit_consequences (n : ℕ) (x : MarkerCircle) :
      (∀ b : ℤ, ∃ k : ℤ, b ≤ k ∧ rotate k x ∈ markerU n) ∧
      (∀ b : ℤ, ∃ k : ℤ, k ≤ b ∧ rotate k x ∈ markerU n) ∧
      (∀ c d : ℤ, c<d → rotate c x ∈ markerU n → rotate d x ∈ markerU n →
        (∀ k : ℤ, c<k → k<d → rotate k x ∉ markerU n) → d-c ≤ (markerL n:ℤ)) := by
    refine ⟨?_,?_,?_⟩
    · intro b
      obtain ⟨k,hk,hkb,hm⟩ := visit_bound n x b
      exact ⟨k,hk,hm⟩
    · intro b
      obtain ⟨k,hk,hkb,hm⟩ := visit_bound n x (b-(markerB n:ℤ))
      exact ⟨k,by omega,hm⟩
    · intro c d hcd _ _ hadj
      obtain ⟨k,hk,hkb,hm⟩ := visit_bound n x (c+1)
      have hL : (markerL n:ℤ) = (markerB n:ℤ)+1 := by simp [markerL]
      by_contra hn
      exact hadj k (by omega) (by omega) hm
  have f_equivalence (n : ℕ) : Equivalence (markerF n) := by
    letI : Std.Symm (fun x y => remainingEdge n x y ∨ remainingEdge n y x) :=
      ⟨fun _ _ h => h.symm⟩
    unfold markerF
    exact ⟨fun _ => .refl, fun h => symm h, fun h h' => h.trans h'⟩
  have f_monotone : Monotone markerF := by
    intro m n h
    apply Relation.ReflTransGen.mono
    intro x y he
    have step : ∀ a b, remainingEdge m a b → remainingEdge n a b := by
      intro a b hab
      exact ⟨fun hn => hab.1 (marker_geometry.2.1 h hn),hab.2⟩
    exact he.imp (step x y) (step y x)
  have f_orbit (n : ℕ) (x y : MarkerCircle) : markerF n x y → ER x y := by
    intro h
    induction h with
    | refl => exact phase_orbit_relations.1.refl _
    | @tail y z h he ih =>
      apply phase_orbit_relations.1.trans ih
      rcases he with he | he
      · exact ⟨1,he.2⟩
      · exact phase_orbit_relations.1.symm ⟨1,he.2⟩
  have g_equivalence (n : ℕ) : Equivalence (markerG n) :=
    (f_equivalence n).comap phase
  have g_monotone : Monotone markerG := fun _ _ h _ _ => f_monotone h _ _
  have pullback_exhaustion
      (hf : ∀ t s, ER t s ↔ ∃ n, markerF n t s) :
      ∀ x y, ET x y ↔ ∃ n, markerG n x y := by
    intro x y
    exact (phase_orbit_relations.2.2.2.2.2.2.1 x y).trans (hf _ _)
  have marker_bracket (n : ℕ) (x : MarkerCircle) :
      ∃ c d : ℤ, c < 0 ∧ 0 ≤ d ∧ rotate c x ∈ markerU n ∧ rotate d x ∈ markerU n ∧
        (∀ k : ℤ, c < k → k < d → rotate k x ∉ markerU n) ∧
        d-c ≤ (markerL n : ℤ) := by
    have hu := (visit_consequences n x).1
    have hl := (visit_consequences n x).2.1
    obtain ⟨c,hc,hcmax⟩ := Int.exists_greatest_of_bdd
      (P := fun k => k < 0 ∧ rotate k x ∈ markerU n)
      ⟨0,fun k hk => hk.1.le⟩ (by obtain ⟨k,hk,hm⟩ := hl (-1); exact ⟨k,by omega,hm⟩)
    obtain ⟨d,hd,hdmin⟩ := Int.exists_least_of_bdd
      (P := fun k => 0 ≤ k ∧ rotate k x ∈ markerU n)
      ⟨0,fun k hk => hk.1⟩ (by obtain ⟨k,hk,hm⟩ := hu 0; exact ⟨k,hk,hm⟩)
    have hadj : ∀ k : ℤ, c < k → k < d → rotate k x ∉ markerU n := by
      intro k hck hkd hm
      by_cases hk : k < 0
      · have := hcmax k ⟨hk,hm⟩; omega
      · have := hdmin k ⟨by omega,hm⟩; omega
    exact ⟨c,d,hc.1,hd.1,hc.2,hd.2,hadj,
      (visit_consequences n x).2.2 c d (by omega) hc.2 hd.2 hadj⟩
  have path_interval (n : ℕ) (x : MarkerCircle) (c d : ℤ)
      (hc : c < 0) (hd : 0 ≤ d) (hcm : rotate c x ∈ markerU n)
      (hdm : rotate d x ∈ markerU n) :
      ∀ y, markerF n x y → ∃ k : ℤ, c < k ∧ k ≤ d ∧ y = rotate k x := by
    intro y hy
    induction hy with
    | refl => exact ⟨0,hc,hd,by simp [rotate]⟩
    | @tail y z h he ih =>
      obtain ⟨k,hck,hkd,hyk⟩ := ih
      rcases he with he | he
      · have hne : k ≠ d := by
          rintro rfl
          exact he.1 (hyk ▸ hdm)
        refine ⟨k+1,by omega,by omega,?_⟩
        rw [he.2,hyk]
        simp [rotate,add_zsmul,add_assoc]
      · have hz : z = rotate (k-1) x := by
          have hh := he.2
          rw [hyk] at hh
          dsimp [rotate] at hh ⊢
          rw [sub_zsmul,one_zsmul]
          calc z = (x + k • (Real.goldenRatio : MarkerCircle)) -
              (Real.goldenRatio : MarkerCircle) := by
                apply eq_sub_iff_add_eq.mpr
                simpa only [one_zsmul] using hh.symm
            _ = _ := by abel
        have hne : k-1 ≠ c := by
          intro heq
          exact he.1 (hz ▸ (heq ▸ hcm))
        exact ⟨k-1,by omega,by omega,hz⟩
  have class_bound (n : ℕ) (x : MarkerCircle) :
      Set.Finite {y | markerF n x y} ∧ {y | markerF n x y}.ncard ≤ markerL n := by
    classical
    obtain ⟨c,d,hc,hd,hcm,hdm,_,hgap⟩ := marker_bracket n x
    let s : Finset MarkerCircle := (Finset.Ioc c d).image (fun k => rotate k x)
    have hsub : {y | markerF n x y} ⊆ (s : Set MarkerCircle) := by
      intro y hy
      obtain ⟨k,hk,hkd,rfl⟩ := path_interval n x c d hc hd hcm hdm y hy
      exact Finset.mem_image.mpr ⟨k,Finset.mem_Ioc.mpr ⟨hk,hkd⟩,rfl⟩
    refine ⟨s.finite_toSet.subset hsub,?_⟩
    calc {y | markerF n x y}.ncard ≤ (s : Set MarkerCircle).ncard := Set.ncard_le_ncard hsub
      _ = s.card := Set.ncard_coe_finset _
      _ ≤ (Finset.Ioc c d).card := Finset.card_image_le
      _ ≤ markerL n := by rw [Int.card_Ioc]; omega
  have edge_step (n : ℕ) (x y : MarkerCircle) :
      (remainingEdge n x y ∨ remainingEdge n y x) ↔
        ∃ b : Bool, allowed n b x ∧ y = step b x := by
    have hinv (x : MarkerCircle) : rotate 1 (rotate (-1) x) = x := by
      simp [rotate]
    constructor
    · rintro (h | h)
      · exact ⟨true,h.1,h.2⟩
      · have hy : y = rotate (-1) x := by
          rw [h.2]
          simp [rotate]
        exact ⟨false,by simpa [allowed,hy] using h.1,hy⟩
    · rintro ⟨b,hb,rfl⟩
      cases b
      · exact .inr ⟨hb,(hinv x).symm⟩
      · exact .inl ⟨hb,rfl⟩
  have f_words (n : ℕ) (x y : MarkerCircle) :
      markerF n x y ↔ ∃ bs : List Bool, valid n bs x ∧ y = walk bs x := by
    constructor
    · intro h
      induction h using Relation.ReflTransGen.head_induction_on with
      | refl => exact ⟨[],trivial,rfl⟩
      | @head x c he h ih =>
        obtain ⟨b,hb,rfl⟩ := (edge_step n x c).mp he
        obtain ⟨bs,hbs,rfl⟩ := ih
        exact ⟨b::bs,⟨hb,hbs⟩,rfl⟩
    · rintro ⟨bs,hbs,rfl⟩
      induction bs generalizing x with
      | nil => exact .refl
      | cons b bs ih =>
        exact (ih _ hbs.2).head ((edge_step n x _).mpr ⟨b,hbs.1,rfl⟩)
  have continuous_step (b : Bool) : Continuous (step b) :=
    continuous_id.add continuous_const
  have continuous_walk (bs : List Bool) : Continuous (walk bs) := by
    induction bs with
    | nil => exact continuous_id
    | cons b bs ih => exact ih.comp (continuous_step b)
  have measurable_valid (n : ℕ) (bs : List Bool) : MeasurableSet {x | valid n bs x} := by
    induction bs with
    | nil => exact MeasurableSet.univ
    | cons b bs ih =>
      have h : MeasurableSet {x | allowed n b x} := by
        have hm := (marker_geometry.1 n).2.measurableSet.compl
        cases b
        · exact hm.preimage (continuous_step false).measurable
        · exact hm
      exact h.inter (ih.preimage (continuous_step b).measurable)
  have f_borel (n : ℕ) : BorelEquivalence (markerF n) := by
    refine ⟨f_equivalence n,?_⟩
    rw [← (inferInstance : BorelSpace (MarkerCircle × MarkerCircle)).measurable_eq]
    have hrepr : {p : MarkerCircle × MarkerCircle | markerF n p.1 p.2} =
        ⋃ bs : List Bool, {p | valid n bs p.1 ∧ p.2 = walk bs p.1} := by
      ext p
      simp only [Set.mem_setOf_eq,Set.mem_iUnion,f_words]
    rw [hrepr]
    apply MeasurableSet.iUnion
    intro bs
    exact ((measurable_valid n bs).preimage measurable_fst).inter
      (isClosed_eq continuous_snd ((continuous_walk bs).comp continuous_fst)).measurableSet
  have exhaustion : ∀ t s, ER t s ↔ ∃ n, markerF n t s := by
    have disappears (x : MarkerCircle) : ∃ n, x ∉ markerU n := by
      by_contra h
      push_neg at h
      have hx : x ∈ ⋂ n, markerU n := Set.mem_iInter.mpr h
      rw [marker_geometry.2.2] at hx
      exact hx
    have glue {x y z : MarkerCircle} (h : ∃ n, markerF n x y)
        (h' : ∃ n, markerF n y z) : ∃ n, markerF n x z := by
      obtain ⟨n,hn⟩ := h
      obtain ⟨m,hm⟩ := h'
      exact ⟨max n m,(f_monotone (le_max_left _ _) _ _ hn).trans
        (f_monotone (le_max_right _ _) _ _ hm)⟩
    have one (x : MarkerCircle) : ∃ n, markerF n x (rotate 1 x) := by
      obtain ⟨n,hn⟩ := disappears x
      exact ⟨n,.single (.inl ⟨hn,rfl⟩)⟩
    have comp (a b : ℤ) (x : MarkerCircle) : rotate a (rotate b x) = rotate (b+a) x := by
      simp [rotate,add_zsmul,add_assoc]
    have all (x : MarkerCircle) (k : ℤ) : ∃ n, markerF n x (rotate k x) := by
      refine Int.inductionOn' k 0 ?_ ?_ ?_
      · exact ⟨0,by simp [rotate]; exact .refl⟩
      · intro k hk ih
        have h := glue ih (one (rotate k x))
        simpa only [comp] using h
      · intro k hk ih
        have h := one (rotate (k-1) x)
        rw [comp,sub_add_cancel] at h
        obtain ⟨n,hn⟩ := h
        exact glue ih ⟨n,(f_equivalence n).symm hn⟩
    intro t s
    constructor
    · rintro ⟨k,rfl⟩
      exact all t k
    · rintro ⟨n,hn⟩
      exact f_orbit n t s hn
  have value_continuous : Continuous signedValue := by
    have hp : 0 < alpha := inv_pos.mpr Real.goldenRatio_pos
    have hlt : alpha < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
    apply continuous_tsum
    · intro j
      apply continuous_const.mul
      exact (continuous_of_discreteTopology : Continuous (fun b : Bool => if b then (1 : ℝ) else 0)).comp
        ((continuous_apply j).comp continuous_subtype_val)
    · exact (summable_geometric_of_lt_one hp.le hlt).mul_right (alpha ^ 2)
    · intro j x
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_pow]
      simp only [abs_neg, abs_one, one_pow, one_mul, abs_of_pos hp]
      cases x.val j <;> simp [pow_add, mul_nonneg (pow_nonneg hp.le j) (sq_nonneg alpha)]
  have h_continuous : Continuous phase :=
    (AddCircle.continuous_mk' (1 : ℝ)).comp value_continuous
  have phase_fibre_alternatives (c : AddCircle (1 : ℝ)) :
      (∃! x : LegalDigits, phase x = c) ∨
      (∃ x y : LegalDigits, x ≠ y ∧ ∀ z : LegalDigits, phase z = c ↔ z = x ∨ z = y) := by
    classical
    have hba : b = a + 1 := by
      dsimp [b, a, alpha]
      rw [Real.inv_goldenRatio]
      nlinarith [Real.goldenConj_sq]
    have hone : ((1 : ℝ) : AddCircle (1 : ℝ)) = 0 :=
      (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨1, by simp⟩
    have hab : (b : AddCircle (1 : ℝ)) = (a : AddCircle (1 : ℝ)) := by
      rw [hba, AddCircle.coe_add, hone, add_zero]
    have ha : a ∈ Set.Ico a (a + 1) := ⟨le_rfl, by linarith⟩
    have hbounds (z : LegalDigits) : signedValue z ∈ Set.Icc a b := by
      rw [← signed_series_range.1]
      exact Set.mem_range_self z
    let t := AddCircle.equivIco (1 : ℝ) a c
    have htc : ((t.val : ℝ) : AddCircle (1 : ℝ)) = c := AddCircle.coe_equivIco
    by_cases hta : t.val = a
    · have hca : c = (a : AddCircle (1 : ℝ)) := htc.symm.trans (congrArg _ hta)
      right
      refine ⟨u, v, ?_, ?_⟩
      · intro h
        have := congrArg (fun z : LegalDigits => z.val 0) h
        simp [u, v] at this
      · intro z
        constructor
        · intro hz
          have hs : signedValue z = a ∨ signedValue z = b := by
            by_cases hb : signedValue z = b
            · exact Or.inr hb
            · left
              apply (AddCircle.coe_eq_coe_iff_of_mem_Ico
                (show signedValue z ∈ Set.Ico a (a + 1) from
                  ⟨(hbounds z).1, hba ▸ (lt_of_le_of_ne (hbounds z).2 hb)⟩) ha).mp
              exact hz.trans hca
          exact hs.imp ((signed_series_range.2.1 z).mp) ((signed_series_range.2.2 z).mp)
        · rintro (rfl | rfl)
          · change ((signedValue u : ℝ) : AddCircle (1 : ℝ)) = c
            rw [(signed_series_range.2.1 u).mpr rfl, ← hca]
          · change ((signedValue v : ℝ) : AddCircle (1 : ℝ)) = c
            rw [(signed_series_range.2.2 v).mpr rfl, hab, ← hca]
    · have hti : t.val ∈ Set.Ioo a b :=
        ⟨lt_of_le_of_ne t.property.1 (Ne.symm hta), by simpa only [hba] using t.property.2⟩
      have hcb : c ≠ (b : AddCircle (1 : ℝ)) := by
        intro h
        exact hta ((AddCircle.coe_eq_coe_iff_of_mem_Ico t.property ha).mp
          (htc.trans (h.trans hab)))
      have repr (z : LegalDigits) : phase z = c ↔ signedValue z = t.val := by
        constructor
        · intro hz
          have hb : signedValue z ≠ b := by
            intro hb
            exact hcb (hz.symm.trans (congrArg (fun s : ℝ => (s : AddCircle (1 : ℝ))) hb))
          exact (AddCircle.coe_eq_coe_iff_of_mem_Ico
            (show signedValue z ∈ Set.Ico a (a + 1) from
              ⟨(hbounds z).1, hba ▸ (lt_of_le_of_ne (hbounds z).2 hb)⟩) t.property).mp
            (hz.trans htc.symm)
        · intro hz
          exact (congrArg (fun s : ℝ => (s : AddCircle (1 : ℝ))) hz).trans htc
      by_cases hs : t.val ∈ Set.range seam
      · obtain ⟨w, hw⟩ := hs
        right
        refine ⟨leftStream w, rightStream w, (signed_series_fibres.1 w).1, ?_⟩
        intro z
        rw [repr, ← hw]
        exact (signed_series_fibres.1 w).2 z
      · left
        obtain ⟨x, hx, huniq⟩ := signed_series_fibres.2.2 _ ⟨hti.1.le, hti.2.le⟩ hs
        exact ⟨x, (repr x).mpr hx, fun z hz => huniq z ((repr z).mp hz)⟩
  have phase_two_cover (t : MarkerCircle) :
      ∃ s : Finset LegalDigits, s.card ≤ 2 ∧ ∀ x, phase x = t → x ∈ s := by
    classical
    rcases phase_fibre_alternatives t with ⟨x,hx,hu⟩ | ⟨x,y,hxy,hf⟩
    · exact ⟨{x},by simp,fun z hz => by simp [hu z hz]⟩
    · exact ⟨{x,y},by by_cases h : x=y <;> simp [h],fun z hz => by simpa using (hf z).mp hz⟩
  have g_bound (n : ℕ) (x : LegalDigits) :
      Set.Finite {y | markerG n x y} ∧ {y | markerG n x y}.ncard ≤ 2 * markerL n := by
    classical
    let s := (class_bound n (phase x)).1.toFinset
    choose f hf hmem using phase_two_cover
    let q := s.biUnion f
    have hsub : {y | markerG n x y} ⊆ (q : Set LegalDigits) := by
      intro y hy
      apply Finset.mem_biUnion.mpr
      refine ⟨phase y,?_,hmem _ y rfl⟩
      exact ((class_bound n (phase x)).1.mem_toFinset).mpr hy
    refine ⟨q.finite_toSet.subset hsub,?_⟩
    calc {y | markerG n x y}.ncard ≤ q.card :=
        (Set.ncard_le_ncard hsub).trans_eq (Set.ncard_coe_finset q)
      _ ≤ ∑ t ∈ s, (f t).card := Finset.card_biUnion_le
      _ ≤ ∑ _t ∈ s, 2 := Finset.sum_le_sum (fun t _ => hf t)
      _ = 2 * s.card := by simp [Nat.mul_comm]
      _ ≤ 2 * markerL n := Nat.mul_le_mul_left _ (by
        simpa only [s, ← Set.ncard_eq_toFinset_card _ (class_bound n (phase x)).1] using
          (class_bound n (phase x)).2)
  have g_borel (n : ℕ) : BorelEquivalence (markerG n) := by
    refine ⟨g_equivalence n,?_⟩
    letI : MeasurableSpace (LegalDigits × LegalDigits) := borel _
    letI : BorelSpace (LegalDigits × LegalDigits) := ⟨rfl⟩
    have hf := (f_borel n).2
    rw [← (inferInstance : BorelSpace (MarkerCircle × MarkerCircle)).measurable_eq] at hf
    exact hf.preimage
      (((h_continuous.comp continuous_fst).prodMk
        (h_continuous.comp continuous_snd)).measurable)

  have gex : ∀ x y, ET x y ↔ ∃ n, markerG n x y := pullback_exhaustion exhaustion
  refine ⟨fun n => (marker_geometry.1 n).2,marker_geometry.2.1,marker_geometry.2.2,
    visit_bound,visit_consequences,fun n => ⟨f_borel n,class_bound n⟩,f_monotone,exhaustion,
    fun n => ⟨g_borel n,g_bound n⟩,g_monotone,gex,?_,?_⟩
  · exact ⟨markerF,f_monotone,fun n => ⟨f_borel n,fun t => (class_bound n t).1⟩,exhaustion⟩
  · exact ⟨markerG,g_monotone,fun n => ⟨g_borel n,fun x => (g_bound n x).1⟩,gex⟩
end D5.S1.Digit.Infinite.MarkerHyperfiniteness

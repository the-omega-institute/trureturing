/- GID: D5/S3/Observer/Linear/GainRayAdaptive
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/GainRayAdaptive
   mirror-E: none(waiver:unrestricted-native-protocols)
   anchors: []
   utility: none
   digest: A deterministic native protocol attains the whole-world gain-ray upper read bound. -/

import D5.S3.Observer.Linear.GainRayJets
import D5.S3.Observer.Linear.GainRayCompletion
import D5.S3.Observer.Linear.GainRayIdenticalRows

set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace D5.S3.Observer.Linear.GainRay

/-- A singleton preassigned palette exists at every word. Only the intended
terminal word is reached at the stopping time. -/
def upperReadout (d : ℕ) (w : List Bool) : Readout d w :=
  if h : w = List.replicate (2*(d+1)) false then
    h.symm ▸ exactBetaReadout d else 0

def upperProtocol (d : ℕ) : Protocol d where
  palette w := {upperReadout d w}
  countable _ := Set.countable_singleton _
  decide w _ := if w.length < 2*(d+1) then Sum.inl false
    else Sum.inr ⟨upperReadout d w, Set.mem_singleton _⟩

private theorem upper_reaches (d : ℕ) (W : World d) (k : ℕ) (hk : k ≤ 2*(d+1)) :
    Reaches (upperProtocol d) W (List.replicate k false) := by
  induction k with
  | zero => simpa using (Reaches.initial (P := upperProtocol d) (W := W))
  | succ k ih =>
      rw [List.replicate_succ']
      apply Reaches.step (ih (by omega))
      simp [upperProtocol, show k < 2*(d+1) by omega]

/-- The exact native trajectory takes 2d+3 initial-inclusive consecutive reads,
terminates there, and returns the whole original coefficient vector with scalar 1. -/
theorem upper_protocol_correct (d : ℕ) (W : World d) :
    ∃ C : {C : Readout d (List.replicate (2*(d+1)) false) //
        C ∈ (upperProtocol d).palette (List.replicate (2*(d+1)) false)},
      Terminates (upperProtocol d) W (List.replicate (2*(d+1)) false) C ∧
      (List.replicate (2*(d+1)) false).length + 1 = 2*d+3 ∧
      C.1.mulVec (readings W (List.replicate (2*(d+1)) false)) = W.coeff := by
  refine ⟨⟨upperReadout d _, Set.mem_singleton _⟩, ⟨upper_reaches d W _ le_rfl, ?_⟩,
    by simp; omega, ?_⟩
  · simp [upperProtocol]
  · simpa [upperReadout] using pureM_exact_beta d W

/-- The attained upper bound is an actual protocol in the unrestricted history domain. -/
theorem adaptive_upper (d : ℕ) : UniformlySuccessful (upperProtocol d) (2*d+3) := by
  intro W
  obtain ⟨C,ht,hn,hβ⟩ := upper_protocol_correct d W
  exact ⟨_, C, ht, hn.le, 1, one_ne_zero, by simpa using hβ⟩


abbrev RowPolynomial (d : ℕ) := MvPolynomial (Fin (d+3)) ℝ

def rowParameters (d : ℕ) (θ : ℝ) (β : Coeff d) (δ : ℝ) : Fin (d+3) → ℝ :=
  fun i => if i.val = 0 then θ else if h : i.val < d+2 then β ⟨i.val-1,by omega⟩ else δ

private theorem row_parameter_coeff (d : ℕ) (θ : ℝ) (β : Coeff d) (δ : ℝ)
    (k : Fin (d+1)) : rowParameters d θ β δ ⟨k.val+1,by omega⟩ = β k := by
  simp [rowParameters,show k.val+1 ≠ 0 by omega,show k.val+1 < d+2 by omega]

def rowReadPolynomial (d : ℕ) (w : List Bool) (i : Fin (w.length+1)) : RowPolynomial d :=
  (MvPolynomial.C (rowBase w i) + MvPolynomial.X 0 * MvPolynomial.C (rowSlope w i)) *
    (∑ k : Fin (d+1), MvPolynomial.C ((i.val : ℝ)^k.val) *
      MvPolynomial.X ⟨k.val+1,by omega⟩) + MvPolynomial.X ⟨d+2,by omega⟩

def rowOutputPolynomial (d : ℕ) (w : List Bool) (C : Readout d w)
    (k : Fin (d+1)) : RowPolynomial d :=
  ∑ i : Fin (w.length+1), MvPolynomial.C (C k i) * rowReadPolynomial d w i

def rowWedge (d : ℕ) (w : List Bool) (C : Readout d w)
    (j k : Fin (d+1)) : RowPolynomial d :=
  MvPolynomial.X ⟨j.val+1,by omega⟩ * rowOutputPolynomial d w C k -
    MvPolynomial.X ⟨k.val+1,by omega⟩ * rowOutputPolynomial d w C j

private theorem eval_row_read (d : ℕ) (w : List Bool)
    (θ : ℝ) (hθ : 0 < θ) (hθ' : θ < 1) (β : Coeff d) (hβ : β ≠ 0) (δ : ℝ)
    (i : Fin (w.length+1)) :
    MvPolynomial.eval (rowParameters d θ β δ) (rowReadPolynomial d w i) =
      readings (rowWorld d θ hθ hθ' β hβ δ) w i := by
  rw [row_readings_affine]
  simp [rowReadPolynomial, row_parameter_coeff, rowParameters,
    gain, Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum, mul_comm]

private theorem eval_row_wedge (d : ℕ) (w : List Bool) (C : Readout d w)
    (θ : ℝ) (hθ : 0 < θ) (hθ' : θ < 1) (β : Coeff d) (hβ : β ≠ 0) (δ : ℝ)
    (j k : Fin (d+1)) :
    MvPolynomial.eval (rowParameters d θ β δ) (rowWedge d w C j k) =
      β j * C.mulVec (readings (rowWorld d θ hθ hθ' β hβ δ) w) k -
        β k * C.mulVec (readings (rowWorld d θ hθ hθ' β hβ δ) w) j := by
  simp only [rowWedge, map_sub, map_mul, MvPolynomial.eval_X, row_parameter_coeff,
    rowOutputPolynomial, map_sum, MvPolynomial.eval_C, eval_row_read]
  rfl

def RowEligible (d : ℕ) (w : List Bool) : Prop :=
  false ∉ w ∨ ∃ k tail, w = List.replicate k true ++ [false] ++ tail ∧
    tail.length+1 < d+1

private theorem row_success_polynomial (d : ℕ) (hd : 1 ≤ d) (c : WordMatrix d)
    (hc : RowEligible d c.1) :
    ∃ p : RowPolynomial d, p ≠ 0 ∧
      ∀ (θ : ℝ) (hθ : 0 < θ) (hθ' : θ < 1) (β : Coeff d) (hβ : β ≠ 0) (δ : ℝ),
        Succeeds (rowWorld d θ hθ hθ' β hβ δ) c.1 c.2 →
          MvPolynomial.eval (rowParameters d θ β δ) p = 0 := by
  classical
  by_cases hh : ∃ (θ : ℝ) (hθ : 0 < θ) (hθ' : θ < 1) (β : Coeff d)
      (hβ : β ≠ 0) (δ : ℝ), Succeeds (rowWorld d θ hθ hθ' β hβ δ) c.1 c.2
  · have hex : ∃ j k, rowWedge d c.1 c.2 j k ≠ 0 := by
      by_contra h
      push_neg at h
      have hu : RowUniversallyCollinear d c.1 c.2 := by
        intro θ hθ hθ' β hβ δ
        apply collinear_of_wedges β _ hβ
        intro j k
        have he := eval_row_wedge d c.1 c.2 θ hθ hθ' β hβ δ j k
        rw [h j k,map_zero] at he
        exact he.symm
      obtain ⟨θ,hθ,hθ',β,hβ,δ,hs⟩ := hh
      exact (identical_row_annihilation d hd c.1 c.2 hu hc θ hθ hθ' β hβ δ).2 hs
    obtain ⟨j,k,hp⟩ := hex
    refine ⟨rowWedge d c.1 c.2 j k,hp,?_⟩
    intro θ hθ hθ' β hβ δ hs
    rw [eval_row_wedge]
    obtain ⟨a,_,ha⟩ := hs
    change c.2.mulVec (readings _) = a • β at ha
    simp only [ha, Pi.smul_apply, smul_eq_mul]
    ring
  · exact ⟨1,one_ne_zero,fun θ hθ hθ' β hβ δ hs =>
      False.elim (hh ⟨θ,hθ,hθ',β,hβ,δ,hs⟩)⟩

def pureJHistoryPolynomial (d n : ℕ) (i : Fin n) : RowPolynomial d :=
  (∑ k : Fin (d+1), MvPolynomial.C ((i.val : ℝ)^k.val) *
    MvPolynomial.X ⟨k.val+1,by omega⟩) + MvPolynomial.X ⟨d+2,by omega⟩

def historyPullback (d n : ℕ) (p : MvPolynomial (Fin n) ℝ) : RowPolynomial d :=
  MvPolynomial.bind₁ (pureJHistoryPolynomial d n) p

private theorem eval_history_pullback (d n : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (θ : ℝ) (β : Coeff d) (δ : ℝ) :
    MvPolynomial.eval (rowParameters d θ β δ) (historyPullback d n p) =
      MvPolynomial.eval (fun i : Fin n => (gain d β).eval (clocks n i) + δ) p := by
  rw [historyPullback]
  change MvPolynomial.eval₂Hom (RingHom.id ℝ) _ _ = _
  rw [MvPolynomial.eval₂Hom_bind₁]
  change MvPolynomial.eval (fun i => MvPolynomial.eval (rowParameters d θ β δ)
    (pureJHistoryPolynomial d n i)) p = _
  apply congrArg (fun v : Fin n → ℝ => MvPolynomial.eval v p)
  ext i
  simp [pureJHistoryPolynomial, row_parameter_coeff, rowParameters, clocks,
    gain, Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum, mul_comm]

/-- Surjectivity concerns the extended coefficient-and-drift space, including
its zero vector; the actual-world restriction is imposed only afterwards. -/
theorem history_pullback_nonzero (d n : ℕ) (hn : n ≤ d+1)
    (p : MvPolynomial (Fin n) ℝ) (hp : p ≠ 0) : historyPullback d n p ≠ 0 := by
  intro hz
  apply hp
  apply MvPolynomial.funext
  intro y
  obtain ⟨⟨β,δ⟩,he⟩ := pureJ_history_surjective d n hn y
  have hh := eval_history_pullback d n p 0 β δ
  rw [hz,map_zero,he] at hh
  exact hh.symm


private theorem palette_pairs_countable (d : ℕ) (P : Protocol d) :
    ({c : WordMatrix d | c.2 ∈ P.palette c.1} : Set (WordMatrix d)).Countable := by
  letI (w : List Bool) : Countable {C : Readout d w // C ∈ P.palette w} :=
    (P.countable w).to_subtype
  have h := Set.countable_range
    (fun c : (w : List Bool) × {C : Readout d w // C ∈ P.palette w} =>
      (⟨c.1,c.2.1⟩ : WordMatrix d))
  apply h.mono
  rintro ⟨w,C⟩ hc
  exact ⟨⟨w,⟨C,hc⟩⟩,rfl⟩

private theorem first_m_decomposition (w : List Bool) (h : false ∈ w) :
    ∃ k tail, w = List.replicate k true ++ [false] ++ tail := by
  induction w with
  | nil => simp at h
  | cons a w ih =>
      cases a with
      | false => exact ⟨0,w,by simp⟩
      | true =>
          obtain ⟨k,tail,he⟩ := ih (by simpa using h)
          exact ⟨k+1,tail,by simp [List.replicate_succ,he]⟩

private theorem reached_last (d : ℕ) (P : Protocol d) (W : World d)
    (v : List Bool) (a : Bool) (hr : Reaches P W (v ++ [a])) :
    Reaches P W v ∧ P.decide v (readings W v) = Sum.inl a := by
  generalize he : v ++ [a] = z at hr
  cases hr with
  | initial => simp at he
  | @step u b hu hb =>
      obtain ⟨hv,ha⟩ := List.append_inj' he (by simp)
      have hab : a = b := by simpa using ha
      subst u
      subst b
      exact ⟨hu,hb⟩

/-- The lower bound uses only actual reached histories and countable fixed
palettes. Decisions, stopping and selectors carry no regularity hypothesis. -/
theorem adaptive_lower (d : ℕ) (hd : 1 ≤ d) (P : Protocol d) :
    ¬ UniformlySuccessful P (2*d+2) := by
  classical
  intro hsuccess
  let s : Set (WordMatrix d) := {c | c.2 ∈ P.palette c.1 ∧ Eligible d c}
  let t : Set (WordMatrix d) := {c | c.2 ∈ P.palette c.1 ∧ RowEligible d c.1}
  have hs : s.Countable := (palette_pairs_countable d P).mono (fun _ h => h.1)
  have ht : t.Countable := (palette_pairs_countable d P).mono (fun _ h => h.1)
  letI : Countable s := hs.to_subtype
  letI : Countable t := ht.to_subtype
  choose q hq hcomplete using (fun n : Fin (d+1) =>
    short_history_completion d hd s hs (fun _ h => h.2) (n.val+1) (by omega) (by omega))
  choose r hr hrcert using (fun c : t => row_success_polynomial d hd c.1 c.2.2)
  let I := t ⊕ (Fin (d+1) × s)
  let poly : I → RowPolynomial d :=
    Sum.elim r (fun z => historyPullback d (z.1.val+1) (q z.1 z.2))
  have hp (i : I) : poly i ≠ 0 := by
    cases i with
    | inl c => exact hr c
    | inr z => exact history_pullback_nonzero d _ (by omega) _ (hq z.1 z.2)
  let U : Set (Fin (d+3) → ℝ) := {a | 0 < a 0 ∧ a 0 < 1 ∧
    (fun k : Fin (d+1) => a ⟨k.val+1,by omega⟩) ≠ 0}
  have ho : IsOpen U :=
    (isOpen_lt continuous_const (continuous_apply _)).inter
      ((isOpen_lt (continuous_apply _) continuous_const).inter
        (isOpen_ne.preimage (continuous_pi fun _ => continuous_apply _)))
  have hne : U.Nonempty := by
    let a := rowParameters d (1/2) (Pi.single (⟨0,by omega⟩ : Fin (d+1)) 1) 0
    refine ⟨a,by norm_num [a,rowParameters],by norm_num [a,rowParameters],?_⟩
    intro hz
    have h := congrFun hz (⟨0,by omega⟩ : Fin (d+1))
    norm_num [a,rowParameters] at h
  obtain ⟨a,ha,havoid⟩ := countable_polynomial_avoidance (d+3) poly hp U ho hne
  let θ := a 0
  let β : Coeff d := fun k => a ⟨k.val+1,by omega⟩
  let δ := a ⟨d+2,by omega⟩
  have hθ : 0 < θ := ha.1
  have hθ' : θ < 1 := ha.2.1
  have hβ : β ≠ 0 := ha.2.2
  have hparam : rowParameters d θ β δ = a := by
    ext i
    dsimp [rowParameters, θ,β,δ]
    split_ifs with h0 hb
    · exact congrArg a (Fin.ext h0.symm)
    · exact congrArg a (Fin.ext (by dsimp; omega))
    · exact congrArg a (Fin.ext (by dsimp; omega))
  let W := rowWorld d θ hθ hθ' β hβ δ
  have hbad (w : List Bool) (C : Readout d w) (hC : C ∈ P.palette w)
      (hw : RowEligible d w) : ¬ Succeeds W w C := by
    intro hh
    let c : t := ⟨⟨w,C⟩,hC,hw⟩
    apply havoid (.inl c)
    rw [← hparam]
    exact hrcert c θ hθ hθ' β hβ δ hh
  obtain ⟨w,C,hterm,hN,hout⟩ := hsuccess W
  by_cases hM : false ∈ w
  · obtain ⟨k,tail,hw⟩ := first_m_decomposition w hM
    by_cases hk : k+1 ≤ d+1
    · let n : Fin (d+1) := ⟨k,by omega⟩
      let y : Fin (n.val+1) → ℝ := fun i => (gain d β).eval (clocks _ i) + δ
      have hy : y ∉ exceptionalHistories (q n) := by
        rintro ⟨c,hc⟩
        apply havoid (.inr (n,c))
        rw [← hparam]
        exact (eval_history_pullback d _ (q n c) θ β δ).trans hc
      obtain ⟨W',hprefix,hfail⟩ := hcomplete n y hy
      have htake : w.take (k+1) = List.replicate k true ++ [false] := by
        rw [hw,← List.append_assoc]
        simp [List.take_append, List.take_replicate]
      have hreach := reaches_take P W hterm.1 (k+1) (by rw [hw]; simp; omega)
      rw [htake] at hreach
      obtain ⟨hpre,hnext⟩ := reached_last d P W _ false hreach
      have he : readings W (List.replicate k true) = readings W' (List.replicate k true) := by
        ext i
        have hi : i.val < n.val+1 := by have := i.isLt; simp [n] at *; omega
        have hh := hprefix ⟨i.val,hi⟩
        have hirow := congrFun (identical_row_readings d θ hθ hθ' β hβ δ k) i
        change readAt W _ i.val = readAt W' _ i.val
        rw [show k = n.val+1-1 by simp [n],hh]
        simpa [W,readings,y,n,clocks] using hirow
      have hfirst := identical_prefix_firstM P W W' k hpre he hnext
      obtain ⟨w',C',ht',hN',hs'⟩ := hsuccess W'
      have hpreword := terminal_extends_reached P W' _ w' C' hfirst ht'
      have hM' : false ∈ w' := by
        obtain ⟨u,hu⟩ := hpreword
        rw [← hu]
        simp
      let c' : s := ⟨⟨w',C'.1⟩,C'.2,hM',by omega⟩
      exact hfail c' hs'
    · exact hbad w C.1 C.2 (.inr ⟨k,tail,hw,by
        have hh : w.length = k+1+tail.length := by simp [hw]
        omega⟩) hout
  · exact hbad w C.1 C.2 (.inl hM) hout

/-- Both halves of the original native adaptive gain-ray threshold. -/
theorem adaptive_threshold (d : ℕ) (hd : 1 ≤ d) :
    (∀ P : Protocol d, ¬ UniformlySuccessful P (2*d+2)) ∧
      ∃ P : Protocol d, UniformlySuccessful P (2*d+3) :=
  ⟨adaptive_lower d hd, upperProtocol d, adaptive_upper d⟩

#print axioms upper_protocol_correct
#print axioms adaptive_lower
#print axioms adaptive_threshold
end D5.S3.Observer.Linear.GainRay

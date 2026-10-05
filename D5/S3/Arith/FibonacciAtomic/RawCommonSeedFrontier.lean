/- GID: D5/S3/Arith/FibonacciAtomic/RawCommonSeedFrontier
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Arbitrary measurable controller laws have the exact raw common-seed frontier. -/

import D5.S3.Arith.FibonacciAtomic.FourExitRawParetoSpectrum
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.RawCommonSeedFrontier

open ActualTreeReadoutAcquisition FourExitRawEndpointSpectrum MeasureTheory
open scoped BigOperators ENNReal
local notation "Index" => fun k : Nat => Unit ⊕ (Fin k × Fin 4)

/-- At parameter t the baseline has mass 1-5kt; the four slot choices
have masses t,t,2t,t, with the first choosing the A-zero, H-two endpoint. -/
noncomputable def frontierMeasure (k : Nat) (t : ℝ) : Measure (Index k) :=
  Measure.sum (fun l => ENNReal.ofReal (match l with
    | .inl _ => 1 - 5 * (k : ℝ) * t
    | .inr p => if p.2 = 2 then 2 * t else t) • Measure.dirac l)



example (k : Nat) (hk : 1 ≤ k) :
    ∃ c : Index k → Strategy,
      (∀ l, ∀ i, cost (c l) (family k i) = 8*k+16 +
        (match l with
          | .inl u => endpoint k (.inl u) i
          | .inr p => if p.2 = 0 then endpointWith k p.1 2 i
            else endpoint k (.inr p) i)) ∧
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 / (5*(k:ℝ)+1) →
        IsProbabilityMeasure (frontierMeasure k t) ∧
        (∀ i : Index k, (∫⁻ l, (cost (c l) (family k i) : ℝ≥0∞)
          ∂frontierMeasure k t) =
            ENNReal.ofReal ((8*k+16 : Nat) +
              (match i with | .inl _ => 5*(k:ℝ)*t | .inr _ => 1-t))) ∧
        (⨆ i : Index k, ∫⁻ l, (cost (c l) (family k i) : ℝ≥0∞)
          ∂frontierMeasure k t) = ENNReal.ofReal ((8*k+17 : Nat)-t) ∧
        (∫⁻ l, (⨆ i : Index k, (cost (c l) (family k i) : ℝ≥0∞))
          ∂frontierMeasure k t) = ENNReal.ofReal ((8*k+17 : Nat)+(k:ℝ)*t) := by
  classical
  letI : MeasurableSingletonClass Unit := ⟨fun u => by
    have h : ({u} : Set Unit) = Set.univ := by ext x; simp [Subsingleton.elim x u]
    rw [h]; exact MeasurableSet.univ⟩
  letI : MeasurableSingletonClass (Index k) := ⟨fun _ =>
    measurableSet_sum_iff.mpr ⟨(Set.toFinite _).measurableSet,
      (Set.toFinite _).measurableSet⟩⟩
  let V : Index k → Index k → Nat := fun l i => match l with
    | .inl u => endpoint k (.inl u) i
    | .inr p => if p.2 = 0 then endpointWith k p.1 2 i else endpoint k (.inr p) i
  have member (l : Index k) : V l ∈ menu k := by
    cases l with
    | inl u => exact Or.inl (Or.inl ⟨u,rfl⟩)
    | inr p =>
      rcases p with ⟨j,b⟩
      fin_cases b
      · exact Or.inr ⟨(j,1),rfl⟩
      · exact Or.inl (Or.inr ⟨(j,0),rfl⟩)
      · exact Or.inl (Or.inr ⟨(j,1),rfl⟩)
      · exact Or.inl (Or.inr ⟨(j,2),rfl⟩)
  obtain ⟨c,hc⟩ := Classical.axiomOfChoice
    (fun l => (FourExitRawParetoSpectrum.result k hk).2.1 (V l) (member l))
  refine ⟨c,hc,?_⟩
  intro t ht htmax
  have kp : (0:ℝ) < k := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hk)
  have sp : (0:ℝ) < 5*(k:ℝ)+1 := by positivity
  have budget : (5*(k:ℝ)+1)*t ≤ 1 := by
    simpa [mul_comm] using (le_div_iff₀ sp).mp htmax
  let p : Index k → ℝ := fun l => match l with
    | .inl _ => 1-5*(k:ℝ)*t
    | .inr x => if x.2 = 2 then 2*t else t
  have pn (l : Index k) : 0 ≤ p l := by
    cases l with
    | inl u => dsimp [p]; nlinarith
    | inr x => dsimp [p]; split_ifs <;> positivity
  have total : ∑ l, p l = 1 := by
    simp [p,Fintype.sum_sum_type,Fintype.sum_prod_type,Fin.sum_univ_four]
    ring
  have mass (l : Index k) : frontierMeasure k t {l} = ENNReal.ofReal (p l) :=
    Measure.sum_smul_dirac_singleton
  have probability : IsProbabilityMeasure (frontierMeasure k t) := by
    constructor
    have eq : (frontierMeasure k t) Set.univ = ∑ l, frontierMeasure k t {l} := by
      symm
      simpa only [Finset.coe_univ] using
        (sum_measure_singleton (μ := frontierMeasure k t) (s := Finset.univ))
    rw [eq]
    simp only [mass,← ENNReal.ofReal_sum_of_nonneg (fun l _ => pn l),total,
      ENNReal.ofReal_one,Finset.coe_univ]
  have integrate (f : Index k → ℝ) (hf : ∀ l, 0 ≤ f l) :
      (∫⁻ l, ENNReal.ofReal (f l) ∂frontierMeasure k t) =
        ENNReal.ofReal (∑ l, p l * f l) := by
    rw [lintegral_fintype]
    simp only [mass,← ENNReal.ofReal_mul (hf _)]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun l _ => mul_nonneg (hf l) (pn l))]
    congr 1
    apply Finset.sum_congr rfl
    intro l _
    ring
  have row_gain (i : Index k) :
      ∑ l, p l * (V l i : ℝ) =
        (match i with | .inl _ => 5*(k:ℝ)*t | .inr _ => 1-t) := by
    cases i with
    | inl u =>
      cases u
      simp [p,V,endpoint,endpointWith,Fintype.sum_sum_type,Fintype.sum_prod_type,
        Fin.sum_univ_four]
      ring
    | inr x =>
      rcases x with ⟨j,b⟩
      fin_cases b <;>
        simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,Fin.sum_univ_four]
      all_goals simp [p,V,endpoint,endpointWith,Finset.sum_add_distrib,
        Finset.sum_ite,Finset.sum_sub_distrib,Finset.sum_mul,Finset.mul_sum,
        Finset.filter_ne,Finset.filter_ne',Finset.filter_eq,Finset.filter_eq',Nat.cast_sub hk] <;> ring
  have row (i : Index k) :
      (∫⁻ l, (cost (c l) (family k i) : ℝ≥0∞) ∂frontierMeasure k t) =
        ENNReal.ofReal ((8*k+16 : Nat) +
          (match i with | .inl _ => 5*(k:ℝ)*t | .inr _ => 1-t)) := by
    simp_rw [hc]
    simp only [← ENNReal.ofReal_natCast]
    rw [integrate (fun l => ((8*k+16 + V l i : Nat) : ℝ)) (fun l => Nat.cast_nonneg _)]
    congr 1
    simp only [Nat.cast_add,mul_add,Finset.sum_add_distrib,
      ← Finset.sum_mul,total,one_mul,row_gain]
  have maximum (l : Index k) :
      (⨆ i : Index k, (cost (c l) (family k i) : ℝ≥0∞)) =
        ENNReal.ofReal ((8*k+17 : Nat) +
          (match l with | .inl _ => 0 | .inr p => if p.2 = 0 then 1 else 0)) := by
    let D : Nat := match l with | .inl _ => 0 | .inr p => if p.2 = 0 then 1 else 0
    have upper : ∀ i, V l i ≤ 1+D := by
      intro i
      cases l with
      | inl u => simp [V,D,endpoint]; split_ifs <;> omega
      | inr p => dsimp [V,D]; split_ifs <;> simp [endpointWith,endpoint] <;>
          split_ifs <;> omega
    have attain : ∃ i, V l i = 1+D := by
      cases l with
      | inl u => exact ⟨.inr (⟨0,by omega⟩,0),by simp [V,D,endpoint]⟩
      | inr p =>
        by_cases hb : p.2 = 0
        · refine ⟨.inr (p.1,2),?_⟩
          simp [V,D,endpointWith,hb]
        · exact ⟨.inl (),by simp [V,D,endpoint,hb]⟩
    have mx : (⨆ i : Index k, (cost (c l) (family k i) : ℝ≥0∞)) =
        ((8*k+17+D : Nat) : ℝ≥0∞) := by
      apply le_antisymm
      · apply iSup_le
        intro i
        rw [hc]
        have h := upper i
        exact_mod_cast (by omega : 8*k+16+V l i ≤ (8*k+17)+D)
      · obtain ⟨i,hi⟩ := attain
        apply le_iSup_of_le i
        rw [hc,hi]
        exact le_of_eq (by congr 1; omega)
    rw [mx,← ENNReal.ofReal_natCast]
    congr 1
    simp only [Nat.cast_add]
    cases l <;> dsimp [D] <;> first | norm_num | (split_ifs <;> norm_num)
  refine ⟨probability,row,?_,?_⟩
  · apply le_antisymm
    · apply iSup_le
      intro i
      rw [row]
      apply ENNReal.ofReal_le_ofReal
      cases i with
      | inl u => dsimp; push_cast; nlinarith
      | inr p => dsimp; push_cast; ring_nf; exact le_rfl
    · apply le_iSup_of_le (.inr (⟨0,by omega⟩,0))
      rw [row]
      apply le_of_eq
      congr 1
      push_cast
      ring
  · simp_rw [maximum]
    rw [integrate _ (fun l => by cases l <;> dsimp <;> first | positivity | (split_ifs <;> positivity))]
    congr 1
    simp [p,Fintype.sum_sum_type,Fintype.sum_prod_type,Fin.sum_univ_four]
    push_cast
    ring

example (k : Nat) (hk : 1 ≤ k)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (c : Ω → Strategy)
    (hm : ∀ i : Index k, Measurable (fun ω => (cost (c ω) (family k i) : ℝ≥0∞))) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1/(5*(k:ℝ)+1) ∧
      ENNReal.ofReal ((8*k+17 : Nat)-t) ≤
        ⨆ i : Index k, ∫⁻ ω, (cost (c ω) (family k i) : ℝ≥0∞) ∂μ ∧
      ENNReal.ofReal ((8*k+17 : Nat)+(k:ℝ)*t) ≤
        ∫⁻ ω, (⨆ i : Index k, (cost (c ω) (family k i) : ℝ≥0∞)) ∂μ := by
  classical
  have h20 : (2 : Fin 4) ≠ 0 := by decide
  have supply := FourExitRawParetoSpectrum.result k hk
  have mf : (menu k).Finite :=
    ((Set.finite_range _).union (Set.finite_range _)).union (Set.finite_range _)
  let M := {v // v ∈ menu k}
  letI : Fintype M := mf.fintype
  letI : MeasurableSpace M := ⊤
  letI : MeasurableSingletonClass M := ⟨fun _ => trivial⟩
  let base : M := ⟨endpoint k (.inl ()), Or.inl (Or.inl ⟨(),rfl⟩)⟩
  letI : Nonempty M := ⟨base⟩
  let e := Fintype.equivFin M
  let enum (N : Nat) : M := e.symm ⟨N % Fintype.card M, Nat.mod_lt _ Fintype.card_pos⟩
  let P (ω : Ω) (N : Nat) := ∀ i : Index k,
    ((8*k+16 + (enum N).val i : Nat) : ℝ≥0∞) ≤ (cost (c ω) (family k i) : ℝ≥0∞)
  have existsP (ω : Ω) : ∃ N, P ω N := by
    obtain ⟨v,hv,hd⟩ := supply.1 (c ω)
    let m : M := ⟨v,hv⟩
    refine ⟨(e m).val,?_⟩
    have eq : enum (e m).val = m := by simp [enum,Nat.mod_eq_of_lt (e m).isLt]
    intro i
    rw [eq]
    exact_mod_cast hd i
  have pm (N : Nat) : MeasurableSet {ω | P ω N} := by
    simpa only [P,Set.setOf_forall] using
      (MeasurableSet.iInter (fun i : Index k =>
        measurableSet_le (measurable_const (a := ((8*k+16 + (enum N).val i : Nat) : ℝ≥0∞)))
          (hm i)))
  let select : Ω → M := fun ω => enum (Nat.find (existsP ω))
  have hs : Measurable select :=
    (measurable_of_countable enum).comp (measurable_find existsP pm)
  have domination (ω : Ω) (i : Index k) :
      ((8*k+16 + (select ω).val i : Nat) : ℝ≥0∞) ≤
        (cost (c ω) (family k i) : ℝ≥0∞) := Nat.find_spec (existsP ω) i
  let ν := μ.map select
  letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hs.aemeasurable
  let p : M → ℝ := fun v => ν.real {v}
  have pn (v : M) : 0 ≤ p v := ENNReal.toReal_nonneg
  have total : ∑ v, p v = 1 := by
    simpa [p,Finset.coe_univ] using
      (sum_measureReal_singleton (μ := ν) (s := (Finset.univ : Finset M)))
  have integrate (f : M → ℝ) (hf : ∀ v, 0 ≤ f v) :
      (∫⁻ ω, ENNReal.ofReal (f (select ω)) ∂μ) =
        ENNReal.ofReal (∑ v, p v * f v) := by
    rw [← lintegral_map (μ := μ) (f := fun v : M => ENNReal.ofReal (f v))
      (measurable_of_countable _) hs]
    change (∫⁻ v, ENNReal.ofReal (f v) ∂ν) = _
    rw [lintegral_fintype]
    have mass (v : M) : ν {v} = ENNReal.ofReal (p v) :=
      (ENNReal.ofReal_toReal (measure_ne_top ν {v})).symm
    simp only [mass,← ENNReal.ofReal_mul (hf _)]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun v _ => mul_nonneg (hf v) (pn v))]
    congr 1
    apply Finset.sum_congr rfl
    intro v _
    ring
  let d : M → ℝ := fun v => if ∃ j : Fin k, v.val (.inr (j,0)) = 0 then 1 else 0
  have shape (v : M) :
      (0 ≤ d v ∧ d v ≤ 1) ∧
      (∑ j : Fin k, (v.val (.inr (j,0)) : ℝ)) = (k:ℝ)-d v ∧
      ((v.val (.inl ()) : ℝ) + ∑ j : Fin k, ∑ b : Fin 3,
        (v.val (.inr (j,b.succ)) : ℝ)) = 3*(k:ℝ)+2*d v ∧
      (⨆ i : Index k, ((8*k+16 + v.val i : Nat) : ℝ≥0∞)) =
        ENNReal.ofReal ((8*k+17 : Nat)+d v) := by
    have dp : 0 ≤ d v ∧ d v ≤ 1 := by dsimp [d]; split_ifs <;> norm_num
    have sums :
        (∑ j : Fin k, (v.val (.inr (j,0)) : ℝ)) = (k:ℝ)-d v ∧
        ((v.val (.inl ()) : ℝ) + ∑ j : Fin k, ∑ b : Fin 3,
          (v.val (.inr (j,b.succ)) : ℝ)) = 3*(k:ℝ)+2*d v := by
      simp only [Fin.sum_univ_three]
      rcases v with ⟨v,((⟨u,rfl⟩ | ⟨⟨j,b⟩,rfl⟩) | ⟨⟨j,b⟩,rfl⟩)⟩
      · cases u
        simp [d,endpoint]
        ring
      · fin_cases b <;>
          simp [d,endpoint,Fin.sum_univ_three,Finset.sum_add_distrib,
            Finset.sum_ite,Finset.filter_ne,Finset.filter_ne',Finset.filter_eq,Finset.filter_eq',Nat.cast_sub hk] <;> ring
      · fin_cases b <;>
          simp [d,endpointWith,Fin.sum_univ_three,Finset.sum_add_distrib,
            Finset.sum_ite,Finset.filter_ne,Finset.filter_ne',Finset.filter_eq,Finset.filter_eq',Nat.cast_sub hk] <;> ring
    have bound : ∀ i, (v.val i : ℝ) ≤ 1 + d v := by
      rcases v with ⟨v,((⟨u,rfl⟩ | ⟨⟨j,b⟩,rfl⟩) | ⟨⟨j,b⟩,rfl⟩)⟩
      · intro i; simp [d,endpoint]; split_ifs <;> norm_num
      · intro i; fin_cases b <;> simp [d,endpoint] <;> split_ifs <;> norm_num
      · intro i; fin_cases b <;> simp [d,endpointWith] <;> split_ifs <;> norm_num
    have attained : ∃ i, (v.val i : ℝ) = 1+d v := by
      rcases v with ⟨v,((⟨u,rfl⟩ | ⟨⟨j,b⟩,rfl⟩) | ⟨⟨j,b⟩,rfl⟩)⟩
      · cases u
        exact ⟨.inr (⟨0,by omega⟩,0),by simp [d,endpoint]⟩
      · refine ⟨.inl (),?_⟩
        fin_cases b <;> simp [d,endpoint]
      · refine ⟨.inr (j,b.succ),?_⟩
        fin_cases b <;> norm_num [d,endpointWith,h20,Ne.symm h20]
    refine ⟨dp,sums.1,sums.2,le_antisymm ?_ ?_⟩
    · apply iSup_le
      intro i
      rw [← ENNReal.ofReal_natCast]
      apply ENNReal.ofReal_le_ofReal
      have h := bound i
      push_cast
      linarith
    · obtain ⟨i,hi⟩ := attained
      apply le_iSup_of_le i
      rw [← ENNReal.ofReal_natCast]
      apply le_of_eq
      congr 1
      push_cast
      linarith
  let q := ∑ v, p v * d v
  have qp : 0 ≤ q := Finset.sum_nonneg (fun v _ => mul_nonneg (pn v) (shape v).1.1)
  have qu : q ≤ 1 := by
    calc
      _ ≤ ∑ v, p v * 1 := Finset.sum_le_sum
        (fun v _ => mul_le_mul_of_nonneg_left (shape v).1.2 (pn v))
      _ = 1 := by simpa using total
  let n : ℝ := ((8*k+17 : Nat) : ℝ)
  let E : Index k → ℝ := fun i => ∑ v, p v * (((8*k+16 + v.val i : Nat) : ℝ))
  have ep (i : Index k) : 0 ≤ E i :=
    Finset.sum_nonneg (fun v _ => mul_nonneg (pn v) (Nat.cast_nonneg _))
  have row_lower (i : Index k) : ENNReal.ofReal (E i) ≤
      ∫⁻ ω, (cost (c ω) (family k i) : ℝ≥0∞) ∂μ := by
    rw [← integrate _ (fun v => Nat.cast_nonneg _)]
    simp only [ENNReal.ofReal_natCast]
    exact lintegral_mono (μ := μ) (fun ω => domination ω i)
  have worst_lower : ENNReal.ofReal (n+q) ≤
      ∫⁻ ω, (⨆ i : Index k, (cost (c ω) (family k i) : ℝ≥0∞)) ∂μ := by
    have eq : ∑ v, p v * (n+d v) = n+q := by
      simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,total,one_mul,q]
    rw [← eq,← integrate _ (fun v => add_nonneg (Nat.cast_nonneg _) (shape v).1.1)]
    apply lintegral_mono
    intro ω
    change ENNReal.ofReal (((8*k+17 : Nat):ℝ)+d (select ω)) ≤ _
    rw [← (shape (select ω)).2.2.2]
    exact iSup_mono (fun i => domination ω i)
  have floor : ENNReal.ofReal n ≤
      ∫⁻ ω, (⨆ i : Index k, (cost (c ω) (family k i) : ℝ≥0∞)) ∂μ :=
    (ENNReal.ofReal_le_ofReal (by linarith)).trans worst_lower
  let R := ⨆ i : Index k, ∫⁻ ω, (cost (c ω) (family k i) : ℝ≥0∞) ∂μ
  by_cases hr : R = ⊤
  · refine ⟨0,le_rfl,by positivity,?_,?_⟩
    · change _ ≤ R
      rw [hr]
      exact le_top
    · simpa [n] using floor
  have er (i : Index k) : E i ≤ R.toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hr).mp
      ((row_lower i).trans (le_iSup (fun i => ∫⁻ ω,
        (cost (c ω) (family k i) : ℝ≥0∞) ∂μ) i))
  have averageA : (k:ℝ)*n-q ≤ (k:ℝ)*R.toReal := by
    have bound := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin k))) =>
      er (.inr (j,0)))
    have eq : (∑ j : Fin k, E (.inr (j,0))) = (k:ℝ)*n-q := by
      dsimp [E]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum,Nat.cast_add,Finset.sum_add_distrib,
        Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,(shape _).2.1]
      dsimp [n]
      simp only [mul_sub,mul_add,Finset.sum_sub_distrib,Finset.sum_add_distrib,
        ← Finset.sum_mul,total,one_mul,q]
      push_cast
      ring
    simpa [eq,Finset.sum_const,nsmul_eq_mul] using bound
  have averageB : (3*(k:ℝ)+1)*n-1+2*q ≤ (3*(k:ℝ)+1)*R.toReal := by
    have bound := add_le_add (er (.inl ()))
      (Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin k))) =>
        Finset.sum_le_sum (fun b (_ : b ∈ (Finset.univ : Finset (Fin 3))) =>
          er (.inr (j,b.succ)))))
    have eq : E (.inl ()) + ∑ j : Fin k, ∑ b : Fin 3, E (.inr (j,b.succ)) =
        (3*(k:ℝ)+1)*n-1+2*q := by
      dsimp [E]
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin 3)))]
      rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin k)))]
      rw [← Finset.sum_add_distrib]
      simp_rw [← Finset.mul_sum,← mul_add,Nat.cast_add,Finset.sum_add_distrib,
        Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      have comb (v : M) :
          ((8*k+16 : Nat):ℝ) + (v.val (.inl ()):ℝ) +
            (k:ℝ)*(3*((8*k+16 : Nat):ℝ)) +
            ∑ j : Fin k, ∑ b : Fin 3, (v.val (.inr (j,b.succ)):ℝ) =
              (3*(k:ℝ)+1)*n-1+2*d v := by
        have h := (shape v).2.2.1
        dsimp [n]
        push_cast
        linarith
      simp only [Nat.cast_add] at comb
      trace_state
      simp_rw [comb,mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib,
        ← Finset.sum_mul,total,one_mul]
      dsimp [q]
      rw [← Finset.mul_sum]
    rw [eq] at bound
    simpa [Finset.sum_const,nsmul_eq_mul,show R.toReal + (k:ℝ)*(3*R.toReal) =
      (3*(k:ℝ)+1)*R.toReal by ring] using bound
  have kp : (0:ℝ) < k := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hk)
  have sp : (0:ℝ) < 5*(k:ℝ)+1 := by positivity
  have bp : (0:ℝ) < 3*(k:ℝ)+1 := by positivity
  by_cases hq : q ≤ (k:ℝ)/(5*(k:ℝ)+1)
  · refine ⟨q/(k:ℝ),(div_nonneg qp kp.le),?_,?_,?_⟩
    · apply (div_le_iff₀ kp).mpr
      simpa [div_eq_mul_inv,mul_comm] using hq
    · change ENNReal.ofReal (n-q/(k:ℝ)) ≤ R
      apply (ENNReal.ofReal_le_iff_le_toReal hr).mpr
      have mulq : (k:ℝ)*(q/(k:ℝ)) = q := mul_div_cancel₀ q kp.ne'
      nlinarith
    · have mulq : (k:ℝ)*(q/(k:ℝ)) = q := mul_div_cancel₀ q kp.ne'
      simpa [n,mulq] using worst_lower
  · refine ⟨1/(5*(k:ℝ)+1),by positivity,le_rfl,?_,?_⟩
    · change ENNReal.ofReal (n-1/(5*(k:ℝ)+1)) ≤ R
      apply (ENNReal.ofReal_le_iff_le_toReal hr).mpr
      have threshold : (k:ℝ) < q*(5*(k:ℝ)+1) := (div_lt_iff₀ sp).mp (lt_of_not_ge hq)
      have denom : (5*(k:ℝ)+1)*(1/(5*(k:ℝ)+1)) = 1 := by field_simp
      nlinarith
    · apply (ENNReal.ofReal_le_ofReal ?_).trans worst_lower
      dsimp [n]
      have threshold : (k:ℝ)/(5*(k:ℝ)+1) ≤ q := (lt_of_not_ge hq).le
      simpa [div_eq_mul_inv] using add_le_add_left threshold n

end D5.S3.Arith.FibonacciAtomic.RawCommonSeedFrontier

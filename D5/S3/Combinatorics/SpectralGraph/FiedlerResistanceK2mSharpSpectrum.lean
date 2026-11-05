/- GID: D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mSharpSpectrum
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mSharpSpectrum
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: Sharp product equality determines the complete native K2m Laplacian spectrum. -/
import D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mOptimizer

/-! Sharp product equality on positive labelled weights determines every spectral multiplicity. -/
set_option autoImplicit false
open Matrix Finset
noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mSharpSpectrum
open FiedlerResistanceK2mOptimizer FiedlerResistanceInvariantWeightsRefutation

/-- Equality in the reciprocal estimate concentrates all excess in one entry. -/
private lemma reciprocal_rigidity {ι : Type*} [Fintype ι] (m : ℕ) (hm : 1 < m)
    (hcard : Fintype.card ι = m + 1) (r : ι → ℝ) (t : ℝ) (ht : 0 < t)
    (hr : ∀ i, t ≤ r i) (htrace : (∑ i, r i) = 2 * m * t)
    (hinv : t * (∑ i, (r i)⁻¹) = m + 1 / m) :
    ∃ j, r j = m * t ∧ ∀ i, i ≠ j → r i = t := by
  classical
  let q := fun i => r i / t-1
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hm1 : (1 : ℝ) < m := by exact_mod_cast hm
  have hq (i : ι) : 0 ≤ q i := by
    dsimp [q]
    rw [sub_nonneg,le_div_iff₀ ht]
    simpa using hr i
  have hsum : (∑ i, q i) = m-1 := by
    simp only [q,Finset.sum_sub_distrib,← Finset.sum_div,Finset.sum_const,
      Finset.card_univ,hcard,nsmul_eq_mul,Nat.cast_add,Nat.cast_one,mul_one,htrace]
    field_simp
    ring
  have hqi (i : ι) : q i ≤ m-1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ => hq j) (Finset.mem_univ i)
  have hd (i : ι) : 0 ≤ q i / (1 + q i)-q i / m := by
    apply sub_nonneg.mpr
    exact div_le_div_of_nonneg_left (hq i) (by linarith [hq i]) (by linarith [hqi i])
  have hid (i : ι) : t * (r i)⁻¹ = 1-q i / (1 + q i) := by
    have hp : 0 < r i := lt_of_lt_of_le ht (hr i)
    dsimp [q]
    field_simp [ht.ne',hp.ne']
    ring
  have hfrac : (∑ i, q i / (1 + q i)) = (m-1) / m := by
    have hh : t * (∑ i,(r i)⁻¹) = (m + 1)-∑ i,q i / (1 + q i) := by
      rw [Finset.mul_sum]
      simp_rw [hid]
      simp [Finset.sum_sub_distrib,hcard,Nat.cast_add,Nat.cast_one]
    have hn : (m + 1 : ℝ)-(m + 1 / m) = (m-1) / m := by field_simp; ring
    linarith
  have hzero : (∑ i, (q i / (1 + q i)-q i / m)) = 0 := by
    rw [Finset.sum_sub_distrib,hfrac,← Finset.sum_div,hsum,sub_self]
  have hterm (i : ι) : q i = 0 ∨ q i = m-1 := by
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hd j)).mp hzero i (Finset.mem_univ i)
    have hp : 1 + q i ≠ 0 := by linarith [hq i]
    have he : q i * (m-1-q i) = 0 := by
      have heq : q i / (1 + q i) = q i / m := sub_eq_zero.mp hi
      field_simp [hp,hm0.ne'] at heq
      nlinarith
    rcases mul_eq_zero.mp he with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  obtain ⟨j,hj⟩ : ∃ j, q j ≠ 0 := by
    by_contra! h
    have hz : (∑ i,q i) = 0 := by simp [h]
    linarith
  have hjq : q j = m-1 := (hterm j).resolve_left hj
  have hother (i : ι) (hij : i ≠ j) : q i = 0 := by
    have hz : (∑ i ∈ Finset.univ.erase j, q i) = 0 := by
      have hh := Finset.sum_erase_add (Finset.univ) q (Finset.mem_univ j)
      rw [hsum,hjq] at hh
      linarith
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hq k)).mp hz i
      (Finset.mem_erase.mpr ⟨hij,Finset.mem_univ i⟩)
  refine ⟨j,?_,?_⟩
  · dsimp [q] at hjq
    have hh := (div_eq_iff ht.ne').mp (show r j / t = m from by linarith)
    exact hh
  · intro i hij
    have hi := hother i hij
    dsimp [q] at hi
    have hh := (div_eq_iff ht.ne').mp (show r i / t = 1 from by linarith)
    simpa using hh

/-- Multiplicities of the actual native Hermitian Laplacian, without an ordering convention. -/
def FullSpectrum (m : ℕ) (w : Sym2 (Fin (2 + m)) → ℝ) (t : ℝ) : Prop :=
  let e := (lap_hermitian (K2m m) w).eigenvalues
  (Finset.univ.filter (fun i => e i = 0)).card = 1 ∧
  (Finset.univ.filter (fun i => e i = t)).card = m ∧
  (Finset.univ.filter (fun i => e i = m * t)).card = 1 ∧
  ∀ i, e i = 0 ∨ e i = t ∨ e i = m * t

private lemma spectrum_at_equality {m : ℕ} (hm : 3 ≤ m)
    (w : Sym2 (Fin (2 + m)) → ℝ) (hw : ∀ e ∈ (K2m m).edgeSet, 0 < w e)
    (heq : lambda2 (K2m m) w * totalRes (K2m m) w = sharpConstant m) :
    FullSpectrum m w (lambda2 (K2m m) w) := by
  classical
  let hL := lap_hermitian (K2m m) w
  let e := hL.eigenvalues
  let J := {i : Fin (2 + m) // e i ≠ 0}
  let t := lambda2 (K2m m) w
  have hs := lambda2_spectral (by omega) w hw
  have hz := zero_eigenvalue_count (by omega) w hw
  have hc : (Finset.univ.filter (fun i => e i ≠ 0)).card = m + 1 := by
    have hh := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i => e i = 0)
    rw [hz] at hh
    simp only [Finset.card_univ,Fintype.card_fin] at hh
    simpa only [ne_eq] using (show (Finset.univ.filter (fun i => ¬ e i = 0)).card = m + 1 by omega)
  have hcard : Fintype.card J = m + 1 := by simpa [J,Fintype.card_subtype] using hc
  have hsum : (∑ i : J, e i) = (wLap (K2m m) w).trace := by
    rw [hL.trace_eq_sum_eigenvalues]
    change (∑ i : J, e i) = ∑ i,e i
    rw [← Finset.sum_subtype (Finset.univ.filter (fun i => e i ≠ 0)) (by simp) e]
    exact Finset.sum_filter_ne_zero Finset.univ
  have hinverse : (∑ i : J, (e i)⁻¹) = ∑ i,(e i)⁻¹ := by
    rw [← Finset.sum_subtype (Finset.univ.filter (fun i => e i ≠ 0)) (by simp) (fun i => (e i)⁻¹)]
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases he : e i = 0 <;> simp [he]
  have htrace : (∑ i : J,e i) = 2 * m * t := by
    rw [hsum,lap_trace,(product_bound_trace hm w hw).2 heq]
    ring
  have hinv : t * (∑ i : J,(e i)⁻¹) = m + 1 / m := by
    have hR := resistance_spectral (by omega) w hw
    rw [← hinverse] at hR
    change totalRes (K2m m) w = (2 + m : ℕ)*∑ i : J,(e i)⁻¹ at hR
    rw [hR] at heq
    dsimp [sharpConstant] at heq
    have hn : (0 : ℝ) < m + 2 := by positivity
    dsimp [t]
    push_cast at heq
    nlinarith
  obtain ⟨j,hj,hother⟩ := reciprocal_rigidity m (by omega) hcard (fun i : J => e i) t hs.1
    (fun i => hs.2.2 i i.2) htrace hinv
  have ht : 0 < t := hs.1
  have hmt0 : m * t ≠ 0 := by positivity
  have hmtt : m * t ≠ t := by
    have hm1 : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
    nlinarith
  have hall (i : Fin (2 + m)) : e i = 0 ∨ e i = t ∨ e i = m * t := by
    by_cases hi0 : e i = 0
    · exact Or.inl hi0
    · by_cases hij : i = j
      · exact Or.inr (Or.inr (hij ▸ hj))
      · exact Or.inr (Or.inl (hother ⟨i,hi0⟩ (by intro h; exact hij (congrArg Subtype.val h))))
  have hmax : Finset.univ.filter (fun i => e i = m * t) = {j.val} := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
    constructor
    · intro hi
      by_contra hij
      have hi0 : e i ≠ 0 := by rw [hi]; exact hmt0
      have hh := hother ⟨i,hi0⟩ (by intro h; exact hij (congrArg Subtype.val h))
      exact hmtt (hi.symm.trans hh)
    · intro hij; subst i; exact hj
  have hsmall : Finset.univ.filter (fun i => e i = t) =
      (Finset.univ.filter (fun i => e i ≠ 0)).erase j.val := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase]
    constructor
    · intro hi
      refine ⟨?_,?_⟩
      · intro hij
        have hh : e i = m * t := hij ▸ hj
        exact hmtt (hh.symm.trans hi)
      · rw [hi]; exact ht.ne'
    · rintro ⟨hij,hi0⟩
      exact hother ⟨i,hi0⟩ (by intro h; exact hij (congrArg Subtype.val h))
  change _ ∧ _ ∧ _ ∧ _
  refine ⟨hz,?_,?_,hall⟩
  · rw [hsmall,Finset.card_erase_of_mem (by simp only [Finset.mem_filter,Finset.mem_univ,true_and]; exact j.2),hc]
    omega
  · rw [hmax,Finset.card_singleton]

/-- A common sign fixes all labelled edge conductances; nonedges are unrestricted. -/
def Ray (m : ℕ) (t ε : ℝ) (w : Sym2 (Fin (2 + m)) → ℝ) : Prop :=
  EdgeRestriction m (t / 2 * (1 + ε * splitRatio m)) (t / 2 * (1-ε * splitRatio m)) w

private lemma ray_parameters {m : ℕ} (hm : 3 ≤ m) (t ε : ℝ) (ht : 0 < t)
    (hε : ε = 1 ∨ ε = -1) :
    0 < t / 2 * (1 + ε * splitRatio m) ∧ 0 < t / 2 * (1-ε * splitRatio m) ∧
    t / 2 * (1 + ε * splitRatio m) + t / 2 * (1-ε * splitRatio m) = t ∧
    (m + 2 : ℝ) * (t / 2 * (1 + ε * splitRatio m)) * (t / 2 * (1-ε * splitRatio m)) = t ^ 2 := by
  obtain ⟨hρ,hρ1,hρsq⟩ := splitRatio_facts hm
  have hr : (m + 2 : ℝ) * (splitRatio m) ^ 2 = m-2 := by
    have hh := (eq_div_iff (show (m + 2 : ℝ) ≠ 0 by positivity)).mp hρsq
    simpa only [mul_comm] using hh
  rcases hε with rfl | rfl
  all_goals norm_num only [one_mul,neg_one_mul,add_neg_cancel_right,sub_neg_eq_add]
  all_goals refine ⟨mul_pos (by positivity) (by linarith),mul_pos (by positivity) (by linarith),by ring,?_⟩
  all_goals nlinarith [sq_nonneg t,show t ^ 2 * ((m + 2) * (splitRatio m) ^ 2) = t ^ 2 * (m-2) by rw [hr]]

private lemma restriction_positive {m : ℕ} (w : Sym2 (Fin (2 + m)) → ℝ)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hE : EdgeRestriction m a b w) :
    ∀ e ∈ (K2m m).edgeSet, 0 < w e := by
  intro e he
  induction e using Sym2.ind with
  | _ p q =>
    have hpq : (K2m m).Adj p q := by simpa using he
    revert hpq
    refine Fin.addCases (fun j => ?_) (fun i => ?_) p
    · refine Fin.addCases (fun k => ?_) (fun i => ?_) q
      · intro h
        exact (adj_hub_hub m j k h).elim
      · intro _
        change 0 < w s(hub m j,leaf m i)
        fin_cases j
        · change 0 < w s(hub m 0,leaf m i)
          rw [(hE i).1]; exact ha
        · change 0 < w s(hub m 1,leaf m i)
          rw [(hE i).2]; exact hb
    · refine Fin.addCases (fun j => ?_) (fun k => ?_) q
      · intro _
        change 0 < w s(leaf m i,hub m j)
        rw [Sym2.eq_swap]
        fin_cases j
        · change 0 < w s(hub m 0,leaf m i)
          rw [(hE i).1]; exact ha
        · change 0 < w s(hub m 1,leaf m i)
          rw [(hE i).2]; exact hb
      · intro h
        exact (adj_leaf_leaf m i k h).elim

private lemma ray_facts {m : ℕ} (hm : 3 ≤ m) (t ε : ℝ) (ht : 0 < t)
    (hε : ε = 1 ∨ ε = -1) (w : Sym2 (Fin (2 + m)) → ℝ) (hE : Ray m t ε w) :
    (∀ e ∈ (K2m m).edgeSet, 0 < w e) ∧ lambda2 (K2m m) w = t ∧
    totalRes (K2m m) w = sharpConstant m / t ∧ FullSpectrum m w t := by
  obtain ⟨ha,hb,hs,hab⟩ := ray_parameters hm t ε ht hε
  have hw := restriction_positive w _ _ ha hb hE
  have hval := uniform_extremal hm w hw _ _ t ha hb ht hs hab hE
  have heq : lambda2 (K2m m) w * totalRes (K2m m) w = sharpConstant m := by
    rw [hval.1,hval.2]
    exact mul_div_cancel₀ _ ht.ne'
  refine ⟨hw,hval.1,hval.2,?_⟩
  simpa only [hval.1] using spectrum_at_equality hm w hw heq

/-- The full sharp product endpoint on independent positive labelled edge weights. -/
def SharpProductClaim (m : ℕ) : Prop :=
  (∀ w : Sym2 (Fin (2 + m)) → ℝ, (∀ e ∈ (K2m m).edgeSet, 0 < w e) →
    lambda2 (K2m m) w * totalRes (K2m m) w ≤ sharpConstant m) ∧
  (∀ w : Sym2 (Fin (2 + m)) → ℝ, (∀ e ∈ (K2m m).edgeSet, 0 < w e) →
    (lambda2 (K2m m) w * totalRes (K2m m) w = sharpConstant m ↔
      ∃ t ε : ℝ, 0 < t ∧ (ε = 1 ∨ ε = -1) ∧ Ray m t ε w)) ∧
  (∀ t ε : ℝ, 0 < t → (ε = 1 ∨ ε = -1) →
    (∃ w, Ray m t ε w) ∧
    ∀ w, Ray m t ε w → (∀ e ∈ (K2m m).edgeSet, 0 < w e) ∧
      lambda2 (K2m m) w = t ∧ totalRes (K2m m) w = sharpConstant m / t ∧
      FullSpectrum m w t) ∧
  (¬ ∃ (t s : ℝ) (w : Sym2 (Fin (2 + m)) → ℝ),
    0 < t ∧ 0 < s ∧ Ray m t 1 w ∧ Ray m s (-1) w) ∧
  (∀ (t ε : ℝ) (w : Sym2 (Fin (2 + m)) → ℝ),
    Ray m t ε w → Ray m t (-ε) (exchangeWeights m w)) ∧
  (∀ w w' : Sym2 (Fin (2 + m)) → ℝ, (∀ e ∈ (K2m m).edgeSet, w e = w' e) →
    lambda2 (K2m m) w = lambda2 (K2m m) w' ∧ totalRes (K2m m) w = totalRes (K2m m) w')

/-- The two common-sign positive rays exhaust equality, including every spectral multiplicity. -/
theorem result (m : ℕ) (hm : 3 ≤ m) : SharpProductClaim m := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro w hw
    exact (product_bound_trace hm w hw).1
  · intro w hw
    constructor
    · intro heq
      obtain ⟨a,b,ha,hb,hs,hab,hE⟩ := equality_parameters hm w hw heq
      have ht := (lambda2_spectral (by omega) w hw).1
      rcases parameter_roots hm a b _ hs hab with h | h
      · refine ⟨lambda2 (K2m m) w,1,ht,Or.inl rfl,?_⟩
        simpa only [Ray,EdgeRestriction,one_mul,h.1,h.2] using hE
      · refine ⟨lambda2 (K2m m) w,-1,ht,Or.inr rfl,?_⟩
        simpa only [Ray,EdgeRestriction,neg_one_mul,sub_eq_add_neg,neg_neg,h.1,h.2] using hE
    · rintro ⟨t,ε,ht,hε,hE⟩
      have hh := ray_facts hm t ε ht hε w hE
      rw [hh.2.1,hh.2.2.1]
      exact mul_div_cancel₀ _ ht.ne'
  · intro t ε ht hε
    refine ⟨?_,fun w hE => ray_facts hm t ε ht hε w hE⟩
    exact ⟨uniformWeights m _ _, uniformWeights_edges m _ _⟩
  · rintro ⟨t,s,w,ht,hs,hp,hn⟩
    let i : Fin m := ⟨0,by omega⟩
    have hA := (hp i).1.symm.trans (hn i).1
    have hB := (hp i).2.symm.trans (hn i).2
    simp only [one_mul,neg_one_mul,sub_neg_eq_add] at hA hB
    have hts : t = s := by linarith
    have hρ := (splitRatio_facts hm).1
    rw [← hts] at hA
    nlinarith [mul_pos ht hρ]
  · intro t ε w hE
    have hh := exchange_edges _ _ w hE
    simpa only [Ray,neg_mul,sub_eq_add_neg,neg_neg] using hh
  · intro w w' hE
    exact invariants_congr _ w w' hE

end D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mSharpSpectrum

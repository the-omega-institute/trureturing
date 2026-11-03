/- GID: D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceTripartiteOptimizer
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/FiedlerResistanceTripartiteOptimizer
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: Original labelled tripartite Laplacians and their harmonic resistance ceiling. -/
import D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceConnectedSpectral

/-! Weighted Laplacians on the original labelled vertices. -/
set_option autoImplicit false
open Matrix Finset
noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceTripartiteOptimizer
open FiedlerResistanceInvariantWeightsRefutation FiedlerResistanceK2mOptimizer
open FiedlerResistanceConnectedSpectral

private lemma independent_pair {n m : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (w : Sym2 (Fin n) → ℝ) (f : Fin m → Fin n)
    (hf : Function.Injective f) (hI : ∀ i j, ¬ G.Adj (f i) (f j))
    (t : ℝ) (hP : (wLap G w-t • (1-constProj n)).PosSemidef)
    {i j : Fin m} (hij : i ≠ j) : 2*t ≤ wLap G w (f i) (f i)+wLap G w (f j) (f j) := by
  have hne : f i ≠ f j := hf.ne hij
  have hN : dotProduct (delta (f i) (f j)) (delta (f i) (f j))=2 := by
    rw [delta_dot]
    norm_num [delta,hne,Ne.symm hne]
  have hE : dotProduct (delta (f i) (f j)) (wLap G w *ᵥ delta (f i) (f j)) =
      wLap G w (f i) (f i)+wLap G w (f j) (f j) := by
    rw [delta_dot]
    simp only [delta,Matrix.mulVec_sub,Matrix.mulVec_single_one,Matrix.col_apply,Pi.sub_apply]
    have h01 : wLap G w (f i) (f j)=0 := by simp [wLap,hne,hI]
    have h10 : wLap G w (f j) (f i)=0 := by simp [wLap,Ne.symm hne,hI]
    rw [h01,h10]
    ring
  have h := psd_rayleigh G w t hP (delta (f i) (f j)) (delta_sum _ _)
  rw [hN,hE] at h
  linarith

private lemma independent_trace {n m : ℕ} (hm : 2 ≤ m) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (w : Sym2 (Fin n) → ℝ) (f : Fin m → Fin n)
    (hf : Function.Injective f) (hI : ∀ i j, ¬ G.Adj (f i) (f j))
    (t : ℝ) (hP : (wLap G w-t • (1-constProj n)).PosSemidef) :
    m*t ≤ ∑ i,wLap G w (f i) (f i) := by
  have hgap : 0 ≤ ∑ i,∑ j,if i=j then 0 else
      wLap G w (f i) (f i)+wLap G w (f j) (f j)-2*t := by
    apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    split_ifs with hij
    · rfl
    · linarith [independent_pair G w f hf hI t hP hij]
  rw [pair_gap_sum] at hgap
  have hm1 : (1:ℝ)<m := by exact_mod_cast (show 1<m by omega)
  nlinarith

private lemma independent_annihilation {n m : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (w : Sym2 (Fin n) → ℝ) (f : Fin m → Fin n)
    (hf : Function.Injective f) (hI : ∀ i j, ¬ G.Adj (f i) (f j))
    (t : ℝ) (hP : (wLap G w-t • (1-constProj n)).PosSemidef)
    (htr : (∑ i,wLap G w (f i) (f i))=m*t) (i j : Fin m) :
    (wLap G w-t • (1-constProj n)) *ᵥ delta (f i) (f j)=0 := by
  by_cases hij : i=j
  · subst j; simp [delta]
  let d := fun i => wLap G w (f i) (f i)
  have hnon (i j : Fin m) : 0 ≤ if i=j then 0 else d i+d j-2*t := by
    split_ifs with hij
    · rfl
    · exact sub_nonneg.mpr (independent_pair G w f hf hI t hP hij)
  have hsum : (∑ i,∑ j,if i=j then 0 else d i+d j-2*t)=0 := by
    rw [pair_gap_sum]
    change 2*(m-1:ℝ)*((∑ i,wLap G w (f i) (f i))-m*t)=0
    rw [htr,sub_self,mul_zero]
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ =>
    Finset.sum_nonneg fun l _ => hnon k l)).mp hsum i (mem_univ i)
  have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hnon i k)).mp hi j (mem_univ j)
  simp only [if_neg hij] at hj
  have hne : f i ≠ f j := hf.ne hij
  apply hP.dotProduct_mulVec_zero_iff.mp
  simp only [star_trivial,Matrix.sub_mulVec,Matrix.smul_mulVec,
    Matrix.sub_mulVec,Matrix.one_mulVec,proj_delta,sub_zero,dotProduct_sub,dotProduct_smul,
    smul_eq_mul]
  rw [delta_dot,delta_dot]
  simp only [delta,Matrix.mulVec_sub,Matrix.mulVec_single_one,Matrix.col_apply,Pi.sub_apply]
  have h01 : wLap G w (f i) (f j)=0 := by simp [wLap,hne,hI]
  have h10 : wLap G w (f j) (f i)=0 := by simp [wLap,Ne.symm hne,hI]
  simp [Pi.single_apply,hne,Ne.symm hne,h01,h10,d] at ⊢ hj
  linarith

/-- The original labelled parts of sizes a, b and c, with counting measure. -/
def part (a b c : ℕ) (i : Fin (a+b+c)) : ℕ :=
  if i.val<a then 0 else if i.val<a+b then 1 else 2

def K3 (a b c : ℕ) : SimpleGraph (Fin (a+b+c)) where
  Adj i j := part a b c i ≠ part a b c j
  symm := ⟨by intro i j h; exact h.symm⟩
  loopless := ⟨by intro i; exact not_not_intro rfl⟩

instance K3_dec (a b c : ℕ) : DecidableRel (K3 a b c).Adj := by
  unfold K3; infer_instance

private def va (a b c : ℕ) (i : Fin a) : Fin (a+b+c) := (i.castAdd b).castAdd c
private def vb (a b c : ℕ) (i : Fin b) : Fin (a+b+c) := (i.natAdd a).castAdd c
private def vc (a b c : ℕ) (i : Fin c) : Fin (a+b+c) := i.natAdd (a+b)

private lemma sum_parts {a b c : ℕ} (f : Fin (a+b+c) → ℝ) :
    (∑ i,f i)=(∑ i,f (va a b c i))+(∑ i,f (vb a b c i))+(∑ i,f (vc a b c i)) := by
  rw [Fin.sum_univ_add,Fin.sum_univ_add]
  rfl

private lemma part_va {a b c : ℕ} (i : Fin a) : part a b c (va a b c i)=0 := by
  simp [part,va,i.isLt]
private lemma part_vb {a b c : ℕ} (i : Fin b) : part a b c (vb a b c i)=1 := by
  have hi := i.isLt
  change (if a+i.val<a then 0 else if a+i.val<a+b then 1 else 2)=1
  split_ifs <;> omega
private lemma part_vc {a b c : ℕ} (i : Fin c) : part a b c (vc a b c i)=2 := by
  change (if a+b+i.val<a then 0 else if a+b+i.val<a+b then 1 else 2)=2
  split_ifs <;> omega

private lemma trace_bound {a b c : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (w : Sym2 (Fin (a+b+c)) → ℝ) (t : ℝ)
    (hP : (wLap (K3 a b c) w-t • (1-constProj (a+b+c))).PosSemidef) :
    (a+b+c:ℕ)*t ≤ (wLap (K3 a b c) w).trace := by
  have hA := independent_trace ha (K3 a b c) w (va a b c)
    (by intro i j h; exact Fin.ext (by simpa [va,Fin.ext_iff] using h))
    (by intro i j; simp [K3,part_va]) t hP
  have hB := independent_trace hb (K3 a b c) w (vb a b c)
    (by intro i j h; exact Fin.ext (by simpa [vb,Fin.ext_iff] using h))
    (by intro i j; simp [K3,part_vb]) t hP
  have hC := independent_trace hc (K3 a b c) w (vc a b c)
    (by intro i j h; exact Fin.ext (by simpa [vc,Fin.ext_iff] using h))
    (by intro i j; simp [K3,part_vc]) t hP
  change (a+b+c:ℕ)*t ≤ ∑ i,wLap (K3 a b c) w i i
  rw [sum_parts]
  push_cast
  linarith


private lemma K3_connected {a b c : ℕ} (ha : 0<a) (hc : 0<c) :
    (K3 a b c).Connected := by
  let u := va a b c ⟨0,ha⟩
  let z := vc a b c ⟨0,hc⟩
  have hreach (i : Fin (a+b+c)) : (K3 a b c).Reachable i u := by
    by_cases hi : part a b c i=0
    · have hiz : (K3 a b c).Adj i z := by simp [K3,z,hi,part_vc]
      have hzu : (K3 a b c).Adj z u := by simp [K3,z,u,part_vc,part_va]
      exact hiz.reachable.trans hzu.reachable
    · have hiu : (K3 a b c).Adj i u := by simpa [K3,u,part_va] using hi
      exact hiu.reachable
  rw [SimpleGraph.connected_iff]
  exact ⟨fun i j => (hreach i).trans (hreach j).symm,⟨u⟩⟩

private lemma reciprocal_ceiling {ι : Type*} [Fintype ι] (r : ι → ℝ)
    (t : ℝ) (ht : 0<t) (hr : ∀ i,t ≤ r i)
    (htrace : ((Fintype.card ι:ℝ)+1)*t ≤ ∑ i,r i) :
    t*(∑ i,(r i)⁻¹) ≤ (Fintype.card ι:ℝ)-1/2 ∧
    (t*(∑ i,(r i)⁻¹)=(Fintype.card ι:ℝ)-1/2 →
      (∑ i,r i)=((Fintype.card ι:ℝ)+1)*t ∧
      ∃ j,r j=2*t ∧ ∀ i,i ≠ j → r i=t) := by
  classical
  let q := fun i => r i/t-1
  let Q := ∑ i,q i
  have hrpos (i : ι) : 0<r i := lt_of_lt_of_le ht (hr i)
  have hq (i : ι) : 0 ≤ q i := by
    dsimp [q]
    rw [sub_nonneg,le_div_iff₀ ht]
    simpa using hr i
  have hQeq : Q=(∑ i,r i)/t-(Fintype.card ι:ℝ) := by
    simp [Q,q,Finset.sum_sub_distrib,← Finset.sum_div]
  have hQ : 1 ≤ Q := by
    have hh : (Fintype.card ι:ℝ)+1 ≤ (∑ i,r i)/t :=
      (le_div_iff₀ ht).mpr htrace
    linarith
  have hQp : 0<1+Q := by linarith
  have hqi (i : ι) : q i ≤ Q :=
    Finset.single_le_sum (fun j _ => hq j) (mem_univ i)
  have hterm (i : ι) : q i/(1+Q) ≤ q i/(1+q i) :=
    div_le_div_of_nonneg_left (hq i) (by linarith [hq i]) (by linarith [hqi i])
  have hsum : Q/(1+Q) ≤ ∑ i,q i/(1+q i) := by
    rw [show Q/(1+Q)=∑ i,q i/(1+Q) from Finset.sum_div _ _ _]
    exact Finset.sum_le_sum fun i _ => hterm i
  have hhalf : (1:ℝ)/2 ≤ Q/(1+Q) := by
    rw [div_le_div_iff₀ (by norm_num) hQp]
    linarith
  have hid (i : ι) : t*(r i)⁻¹=1-q i/(1+q i) := by
    dsimp [q]
    field_simp [ht.ne',(hrpos i).ne']
    <;> ring
  have htot : t*(∑ i,(r i)⁻¹)=(Fintype.card ι:ℝ)-∑ i,q i/(1+q i) := by
    rw [Finset.mul_sum]
    simp_rw [hid]
    simp [Finset.sum_sub_distrib]
  refine ⟨by linarith,?_⟩
  intro heq
  have hfrac : (∑ i,q i/(1+q i))=(1:ℝ)/2 := by linarith
  have hQu : Q/(1+Q) ≤ (1:ℝ)/2 := by linarith
  rw [div_le_div_iff₀ hQp (by norm_num)] at hQu
  have hQone : Q=1 := by linarith
  have htr : (∑ i,r i)=((Fintype.card ι:ℝ)+1)*t := by
    rw [hQeq] at hQone
    apply (div_eq_iff ht.ne').mp
    linarith
  refine ⟨htr,?_⟩
  have hd (i : ι) : 0 ≤ q i/(1+q i)-q i/2 := by
    apply sub_nonneg.mpr
    exact div_le_div_of_nonneg_left (hq i) (by linarith [hq i])
      (by linarith [hqi i])
  have hzero : (∑ i,(q i/(1+q i)-q i/2))=0 := by
    rw [Finset.sum_sub_distrib,hfrac,← Finset.sum_div]
    change 1/2-Q/2=0
    rw [hQone]
    norm_num
  have hcases (i : ι) : q i=0 ∨ q i=1 := by
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hd j)).mp hzero i (mem_univ i)
    have hp : 1+q i ≠ 0 := by linarith [hq i]
    have he : q i*(1-q i)=0 := by
      have heq := sub_eq_zero.mp hi
      field_simp [hp] at heq
      nlinarith
    rcases mul_eq_zero.mp he with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  obtain ⟨j,hj⟩ : ∃ j,q j ≠ 0 := by
    by_contra! h
    have hz : Q=0 := by simp [Q,h]
    linarith
  have hjq : q j=1 := (hcases j).resolve_left hj
  have hother (i : ι) (hij : i ≠ j) : q i=0 := by
    have hz : (∑ i ∈ univ.erase j,q i)=0 := by
      have hh := Finset.sum_erase_add univ q (mem_univ j)
      change (∑ i ∈ univ.erase j,q i)+q j=Q at hh
      rw [hjq,hQone] at hh
      linarith
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hq k)).mp hz i
      (Finset.mem_erase.mpr ⟨hij,mem_univ i⟩)
  refine ⟨j,?_,?_⟩
  · dsimp [q] at hjq
    exact (div_eq_iff ht.ne').mp (by linarith)
  · intro i hij
    have hh := hother i hij
    dsimp [q] at hh
    have he : r i/t=1 := by linarith
    simpa using (div_eq_iff ht.ne').mp he

private lemma product_ceiling {a b c : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (w : Sym2 (Fin (a+b+c)) → ℝ) (hL : (wLap (K3 a b c) w).PosSemidef)
    (hB : (wLap (K3 a b c) w+constProj (a+b+c)).PosDef) :
    lambda2 (K3 a b c) w*totalRes (K3 a b c) w ≤
      (a+b+c:ℕ)*((a+b+c:ℕ)-(3:ℝ)/2) ∧
    (lambda2 (K3 a b c) w*totalRes (K3 a b c) w =
      (a+b+c:ℕ)*((a+b+c:ℕ)-(3:ℝ)/2) →
      (wLap (K3 a b c) w).trace=(a+b+c:ℕ)*lambda2 (K3 a b c) w ∧
      ∃ j,(lap_hermitian (K3 a b c) w).eigenvalues j=2*lambda2 (K3 a b c) w ∧
        ∀ i,i ≠ j → (lap_hermitian (K3 a b c) w).eigenvalues i=0 ∨
          (lap_hermitian (K3 a b c) w).eigenvalues i=lambda2 (K3 a b c) w) := by
  classical
  let n := a+b+c
  let e := (lap_hermitian (K3 a b c) w).eigenvalues
  let J := {i : Fin n // e i ≠ 0}
  let t := lambda2 (K3 a b c) w
  have hs := lambda_spectral (by omega) (K3 a b c) w hL hB
  have hcard : Fintype.card J=n-1 := by
    rw [Fintype.card_subtype]
    have hz := zero_count (by omega) (K3 a b c) w hB
    have hh := Finset.card_filter_add_card_filter_not (s := univ) (fun i => e i=0)
    rw [hz] at hh
    simp only [Finset.card_univ,Fintype.card_fin] at hh
    dsimp [n] at ⊢ hh
    omega
  have hsum : (∑ i : J,e i)=(wLap (K3 a b c) w).trace := by
    rw [(lap_hermitian (K3 a b c) w).trace_eq_sum_eigenvalues]
    change (∑ i : J,e i)=∑ i,e i
    rw [← Finset.sum_subtype (univ.filter fun i => e i ≠ 0) (by simp) e]
    exact Finset.sum_filter_ne_zero univ
  have hinv : (∑ i : J,(e i)⁻¹)=∑ i,(e i)⁻¹ := by
    rw [← Finset.sum_subtype (univ.filter fun i => e i ≠ 0) (by simp) (fun i => (e i)⁻¹)]
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases he : e i=0 <;> simp [he]
  have hn1 : 1 ≤ n := by dsimp [n]; omega
  have hcast : (Fintype.card J:ℝ)=(n:ℝ)-1 := by
    rw [hcard,Nat.cast_sub hn1,Nat.cast_one]
  have htrace : ((Fintype.card J:ℝ)+1)*t ≤ ∑ i : J,e i := by
    rw [hcast,sub_add_cancel,hsum]
    exact trace_bound ha hb hc w t hs.2.1
  have hrec := reciprocal_ceiling (fun i : J => e i) t hs.1
    (fun i => hs.2.2 i i.2) htrace
  have hR : totalRes (K3 a b c) w=(n:ℝ)*∑ i : J,(e i)⁻¹ := by
    rw [resistance_spectral (by omega) (K3 a b c) w hL hB,hinv]
  have hnpos : (0:ℝ)<n := by dsimp [n]; positivity
  rw [hcast] at hrec
  constructor
  · rw [hR]
    nlinarith [mul_le_mul_of_nonneg_left hrec.1 hnpos.le]
  · intro heq
    have he : t*(∑ i : J,(e i)⁻¹)=(n:ℝ)-1-1/2 := by
      rw [hR] at heq
      change t*((n:ℝ)*∑ i : J,(e i)⁻¹)=(n:ℝ)*((n:ℝ)-3/2) at heq
      nlinarith
    obtain ⟨htr,j,hj,hother⟩ := hrec.2 he
    refine ⟨?_,j.val,hj,?_⟩
    · rw [hsum] at htr
      simpa only [sub_add_cancel] using htr
    · intro i hij
      by_cases hi : e i=0
      · exact Or.inl hi
      · exact Or.inr (hother ⟨i,hi⟩ (by intro h; exact hij (congrArg Subtype.val h)))


private lemma rankone_constant {n m : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (w : Sym2 (Fin n) → ℝ) (t : ℝ) (ht : 0<t)
    (v : Fin n → ℝ) (hv : dotProduct v v=1)
    (hQ : wLap G w-t • (1-constProj n)=t • Matrix.vecMulVec v v)
    (f : Fin m → Fin n)
    (hkill : ∀ i j,(wLap G w-t • (1-constProj n)) *ᵥ delta (f i) (f j)=0) :
    ∀ i j,v (f i)=v (f j) := by
  obtain ⟨k,hk⟩ : ∃ k,v k ≠ 0 := by
    by_contra! h
    have hz : v=0 := funext h
    simp [hz] at hv
  intro i j
  have hh := congrFun (hkill i j) k
  rw [hQ,Matrix.smul_mulVec,Matrix.vecMulVec_mulVec] at hh
  simp only [Pi.smul_apply,smul_eq_mul,Pi.zero_apply,dotProduct_comm v,
    delta_dot,op_smul_eq_mul] at hh
  have : t*v k*(v (f i)-v (f j))=0 := by nlinarith only [hh]
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left (mul_ne_zero ht.ne' hk))

private lemma rankone_square {n m : ℕ} (hm : 2 ≤ m) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (w : Sym2 (Fin n) → ℝ) (t : ℝ) (ht : 0<t)
    (v : Fin n → ℝ) (hQ : wLap G w-t • (1-constProj n)=t • Matrix.vecMulVec v v)
    (f : Fin m → Fin n) (hf : Function.Injective f)
    (hI : ∀ i j,¬ G.Adj (f i) (f j)) (hconst : ∀ i j,v (f i)=v (f j)) :
    (v (f ⟨0,by omega⟩))^2=(n:ℝ)⁻¹ := by
  let i : Fin m := ⟨0,by omega⟩
  let j : Fin m := ⟨1,by omega⟩
  have hij : f i ≠ f j := hf.ne (by simp [i,j,Fin.ext_iff])
  have hh := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M (f i) (f j)) hQ
  simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,
    if_neg hij,zero_sub,constProj,Matrix.vecMulVec_apply] at hh
  rw [hconst j i] at hh
  have hL : wLap G w (f i) (f j)=0 := by simp [wLap,hij,hI]
  rw [hL] at hh
  change (v (f i))^2=(n:ℝ)⁻¹
  nlinarith

private lemma equality_coordinates {a b c : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (w : Sym2 (Fin (a+b+c)) → ℝ) (hL : (wLap (K3 a b c) w).PosSemidef)
    (hB : (wLap (K3 a b c) w+constProj (a+b+c)).PosDef)
    (heq : lambda2 (K3 a b c) w*totalRes (K3 a b c) w =
      (a+b+c:ℕ)*((a+b+c:ℕ)-(3:ℝ)/2)) :
    c=a+b ∧ ∀ i j,(K3 a b c).Adj i j →
      w s(i,j)=if part a b c i=2 ∨ part a b c j=2 then
        lambda2 (K3 a b c) w/c else 0 := by
  classical
  let n := a+b+c
  let G := K3 a b c
  let t := lambda2 G w
  have hb : 2 ≤ b := le_trans ha hab
  have hc : 2 ≤ c := le_trans hb hbc
  have hs := lambda_spectral (by omega) G w hL hB
  have ht : 0<t := hs.1
  have hP : (wLap G w-t • (1-constProj n)).PosSemidef := hs.2.1
  obtain ⟨htr,j,hj,hother⟩ := (product_ceiling ha hb hc w hL hB).2 heq
  obtain ⟨v,hvsum,hvnorm,hQ⟩ := rankone_of_spectrum (by omega) G w hB t ht j hj hother
  have hAI : Function.Injective (va a b c) := by
    intro i j h; exact Fin.ext (by simpa [va,Fin.ext_iff] using h)
  have hBI : Function.Injective (vb a b c) := by
    intro i j h; exact Fin.ext (by simpa [vb,Fin.ext_iff] using h)
  have hCI : Function.Injective (vc a b c) := by
    intro i j h; exact Fin.ext (by simpa [vc,Fin.ext_iff] using h)
  have hAN : ∀ i j,¬ G.Adj (va a b c i) (va a b c j) := by
    intro i j; simp [G,K3,part_va]
  have hBN : ∀ i j,¬ G.Adj (vb a b c i) (vb a b c j) := by
    intro i j; simp [G,K3,part_vb]
  have hCN : ∀ i j,¬ G.Adj (vc a b c i) (vc a b c j) := by
    intro i j; simp [G,K3,part_vc]
  have hAt := independent_trace ha G w (va a b c) hAI hAN t hP
  have hBt := independent_trace hb G w (vb a b c) hBI hBN t hP
  have hCt := independent_trace hc G w (vc a b c) hCI hCN t hP
  have htrs : (∑ i,wLap G w (va a b c i) (va a b c i))+
      (∑ i,wLap G w (vb a b c i) (vb a b c i))+
      (∑ i,wLap G w (vc a b c i) (vc a b c i))=(a:ℝ)*t+b*t+c*t := by
    have hh := htr
    change (∑ i,wLap G w i i)=(a+b+c:ℕ)*t at hh
    rw [sum_parts] at hh
    push_cast at hh
    linarith
  have hAc := rankone_constant G w t ht v hvnorm hQ (va a b c)
    (independent_annihilation G w (va a b c) hAI hAN t hP (by linarith))
  have hBc := rankone_constant G w t ht v hvnorm hQ (vb a b c)
    (independent_annihilation G w (vb a b c) hBI hBN t hP (by linarith))
  have hCc := rankone_constant G w t ht v hvnorm hQ (vc a b c)
    (independent_annihilation G w (vc a b c) hCI hCN t hP (by linarith))
  let α := v (va a b c ⟨0,by omega⟩)
  let β := v (vb a b c ⟨0,by omega⟩)
  let γ := v (vc a b c ⟨0,by omega⟩)
  have hα : α^2=(n:ℝ)⁻¹ := rankone_square ha G w t ht v hQ (va a b c) hAI hAN hAc
  have hβ : β^2=(n:ℝ)⁻¹ := rankone_square hb G w t ht v hQ (vb a b c) hBI hBN hBc
  have hγ : γ^2=(n:ℝ)⁻¹ := rankone_square hc G w t ht v hQ (vc a b c) hCI hCN hCc
  have hα0 : α ≠ 0 := by
    intro h
    have hn : (0:ℝ)<n := by dsimp [n]; positivity
    rw [h,zero_pow (by decide)] at hα
    exact (ne_of_gt (inv_pos.mpr hn)) hα.symm
  have hbal : (a:ℝ)*α+b*β+c*γ=0 := by
    rw [sum_parts] at hvsum
    simp_rw [hAc _ ⟨0,by omega⟩,hBc _ ⟨0,by omega⟩,hCc _ ⟨0,by omega⟩] at hvsum
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,α,β,γ] using hvsum
  have hbsgn : β=α ∨ β=-α := (sq_eq_sq_iff_eq_or_eq_neg).mp (hβ.trans hα.symm)
  have hcsgn : γ=α ∨ γ=-α := (sq_eq_sq_iff_eq_or_eq_neg).mp (hγ.trans hα.symm)
  have hsign : β=α ∧ γ=-α ∧ c=a+b := by
    have haR : (0:ℝ)<a := by positivity
    have hbR : (0:ℝ)<b := by positivity
    have hcR : (0:ℝ)<c := by positivity
    have habR : (a:ℝ) ≤ b := by exact_mod_cast hab
    have hbcR : (b:ℝ) ≤ c := by exact_mod_cast hbc
    rcases hbsgn with hbsgn | hbsgn <;> rcases hcsgn with hcsgn | hcsgn
    · rw [hbsgn,hcsgn] at hbal
      have : ((a:ℝ)+b+c)*α=0 := by linear_combination hbal
      have hz := (mul_eq_zero.mp this).resolve_right hα0
      linarith only [hz,haR,hbR,hcR,habR,hbcR]
    · refine ⟨hbsgn,hcsgn,?_⟩
      rw [hbsgn,hcsgn] at hbal
      have : ((a:ℝ)+b-c)*α=0 := by linear_combination hbal
      have hh := (mul_eq_zero.mp this).resolve_right hα0
      exact_mod_cast (show (c:ℝ)=a+b by linarith only [hh])
    · rw [hbsgn,hcsgn] at hbal
      have : ((a:ℝ)-b+c)*α=0 := by linear_combination hbal
      have hz := (mul_eq_zero.mp this).resolve_right hα0
      linarith only [hz,haR,hbR,hcR,habR,hbcR]
    · rw [hbsgn,hcsgn] at hbal
      have : ((a:ℝ)-b-c)*α=0 := by linear_combination hbal
      have hz := (mul_eq_zero.mp this).resolve_right hα0
      linarith only [hz,haR,hbR,hcR,habR,hbcR]
  have hv (i : Fin n) : v i=if part a b c i=2 then -α else α := by
    by_cases hi : i.val<a
    · have he : i=va a b c ⟨i.val,hi⟩ := by apply Fin.ext; rfl
      rw [he,hAc _ ⟨0,by omega⟩,part_va]
      rfl
    · by_cases hib : i.val<a+b
      · let k : Fin b := ⟨i.val-a,by omega⟩
        have he : i=vb a b c k := by apply Fin.ext; dsimp [vb,k]; omega
        rw [he,hBc _ ⟨0,by omega⟩,part_vb]
        simpa only [if_neg (by decide : ¬ (1:ℕ)=2)] using hsign.1
      · let k : Fin c := ⟨i.val-(a+b),by have := i.isLt; dsimp [n] at this; omega⟩
        have he : i=vc a b c k := by apply Fin.ext; dsimp [vc,k]; omega
        rw [he,hCc _ ⟨0,by omega⟩,part_vc]
        simpa using hsign.2.1
  refine ⟨hsign.2.2,?_⟩
  intro i k hik
  change G.Adj i k at hik
  change w s(i,k)=(if part a b c i=2 ∨ part a b c k=2 then t/c else 0)
  have hne : i ≠ k := G.ne_of_adj hik
  have hh := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i k) hQ
  simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,
    if_neg hne,zero_sub,constProj,Matrix.vecMulVec_apply] at hh
  have hLoff : wLap G w i k= -w s(i,k) := by simp [wLap,hne,hik]
  rw [hLoff,hv i,hv k] at hh
  change -w s(i,k)-t* -(n:ℝ)⁻¹=t*((if part a b c i=2 then -α else α)*(if part a b c k=2 then -α else α)) at hh
  have hnC : (n:ℝ)=2*c := by dsimp [n]; rw [hsign.2.2]; push_cast; ring
  have hc0 : (c:ℝ) ≠ 0 := by positivity
  have hinv : (n:ℝ)⁻¹=1/(2*c) := by rw [hnC]; simp
  have hsq : α*α=(n:ℝ)⁻¹ := by nlinarith only [hα]
  by_cases hi : part a b c i=2 <;> by_cases hk : part a b c k=2
  · exact (hik (hi.trans hk.symm)).elim
  · simp only [hi,hk,↓reduceIte,true_or] at hh ⊢
    rw [hinv] at hsq hh
    field_simp [hc0] at hsq hh ⊢
    rw [hsq,one_mul] at hh
    nlinarith only [hh]
  · simp only [hi,hk,↓reduceIte,or_true] at hh ⊢
    rw [hinv] at hsq hh
    field_simp [hc0] at hsq hh ⊢
    rw [hsq,one_mul] at hh
    nlinarith only [hh]
  · simp only [hi,hk,↓reduceIte,false_or] at hh ⊢
    rw [hsq] at hh
    linarith only [hh]


/-- Zero extension of the normalized balanced boundary on original unordered pairs. -/
def boundary (a b c : ℕ) : Sym2 (Fin (a+b+c)) → ℝ :=
  Sym2.lift ⟨fun i j => if (part a b c i=2) ≠ (part a b c j=2) then (c:ℝ)⁻¹ else 0,
    by intro i j; by_cases hi : part a b c i=2 <;> by_cases hj : part a b c j=2 <;> simp [hi,hj]⟩

private def signs (a b c : ℕ) (i : Fin (a+b+c)) : ℝ :=
  if part a b c i=2 then -1 else 1

private lemma signs_sum {a b c : ℕ} (hbal : c=a+b) :
    (∑ i,signs a b c i)=0 := by
  rw [sum_parts]
  simp [signs,part_va,part_vb,part_vc,hbal]

private lemma signs_sq {a b c : ℕ} : dotProduct (signs a b c) (signs a b c)=(a+b+c:ℕ) := by
  simp only [dotProduct]
  have hh (i : Fin (a+b+c)) : signs a b c i*signs a b c i=1 := by
    simp [signs]; split_ifs <;> norm_num
  simp_rw [hh]
  simp

private lemma boundary_matrix {a b c : ℕ} (hc : 0<c) (hbal : c=a+b) :
    wLap (K3 a b c) (boundary a b c)=1-constProj (a+b+c)+
      ((a+b+c:ℕ):ℝ)⁻¹ • Matrix.vecMulVec (signs a b c) (signs a b c) := by
  let n := a+b+c
  let M : Matrix (Fin n) (Fin n) ℝ := 1-constProj n+
    (n:ℝ)⁻¹ • Matrix.vecMulVec (signs a b c) (signs a b c)
  have hn : (n:ℝ) ≠ 0 := by dsimp [n]; positivity
  have hnC : (n:ℝ)=2*c := by dsimp [n]; rw [hbal]; push_cast; ring
  have hM : M *ᵥ (1 : Fin n → ℝ)=0 := by
    ext i
    simp [M,Matrix.add_mulVec,Matrix.sub_mulVec,Matrix.smul_mulVec,
      Matrix.vecMulVec_mulVec,Matrix.one_mulVec,proj_mul,dotProduct,signs_sum hbal,hn]
  have hoff (i j : Fin n) (hij : i ≠ j) : wLap (K3 a b c) (boundary a b c) i j=M i j := by
    dsimp [M]
    simp only [wLap,if_neg hij,Matrix.add_apply,Matrix.sub_apply,Matrix.one_apply,
      if_neg hij,zero_sub,constProj,Matrix.smul_apply,smul_eq_mul,Matrix.vecMulVec_apply,
      boundary,Sym2.lift_mk,signs]
    change (if part a b c i ≠ part a b c j then
      -(if (part a b c i=2) ≠ (part a b c j=2) then (c:ℝ)⁻¹ else 0) else 0)=_
    by_cases hi : part a b c i=2 <;> by_cases hj : part a b c j=2
    · simp [hi,hj]
    · have hp : part a b c i ≠ part a b c j := by intro h; exact hj (h ▸ hi)
      simp [hi,hj,hp,hnC,inv_mul_eq_div]
      field_simp
    · have hp : part a b c i ≠ part a b c j := by intro h; exact hi (h.symm ▸ hj)
      simp [hi,hj,hp,hnC,inv_mul_eq_div]
      field_simp
    · simp [hi,hj]
  ext i j
  by_cases hij : i=j
  · subst j
    have hL := congrFun (lap_one (K3 a b c) (boundary a b c)) i
    have hMi := congrFun hM i
    simp only [Matrix.mulVec,Pi.one_apply,mul_one,Pi.zero_apply] at hL hMi
    have hsum : (∑ j,(wLap (K3 a b c) (boundary a b c) i j-M i j))=0 := by
      rw [Finset.sum_sub_distrib,hL,hMi,sub_self]
    rw [Finset.sum_eq_single i] at hsum
    · exact sub_eq_zero.mp hsum
    · intro k hk hki; exact sub_eq_zero.mpr (hoff i k hki.symm)
    · simp
  · exact hoff i j hij

private lemma boundary_nonneg {a b c : ℕ} :
    ∀ i j,(K3 a b c).Adj i j → 0 ≤ boundary a b c s(i,j) := by
  intro i j hij
  simp only [boundary,Sym2.lift_mk]
  split_ifs <;> positivity

private lemma boundary_lambda {a b c : ℕ} (ha : 2 ≤ a) (hc : 0<c) (hbal : c=a+b) :
    lambda2 (K3 a b c) (boundary a b c)=1 := by
  have hM := boundary_matrix hc hbal
  have hP : (wLap (K3 a b c) (boundary a b c)-(1-constProj (a+b+c))).PosSemidef := by
    rw [hM,add_sub_cancel_left]
    have hv : (Matrix.vecMulVec (signs a b c) (signs a b c)).PosSemidef := by
      simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star (signs a b c)
    exact hv.smul (by positivity)
  let i := va a b c ⟨0,by omega⟩
  let j := va a b c ⟨1,by omega⟩
  have hij : i ≠ j := by simp [i,j,va,Fin.ext_iff]
  refine lambda2_eq_of_rayleigh _ _ 1
    (fun x hx => by simpa using psd_rayleigh _ _ 1 (by simpa using hP) x hx)
    (delta i j) (delta_ne hij) (delta_sum _ _) ?_
  rw [hM,Matrix.add_mulVec,Matrix.sub_mulVec,Matrix.one_mulVec,proj_delta,
    sub_zero,Matrix.smul_mulVec,Matrix.vecMulVec_mulVec]
  have hz : dotProduct (signs a b c) (delta i j)=0 := by
    rw [dotProduct_comm,delta_dot]
    simp [i,j,signs,part_va]
  simp [hz]

end D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceTripartiteOptimizer

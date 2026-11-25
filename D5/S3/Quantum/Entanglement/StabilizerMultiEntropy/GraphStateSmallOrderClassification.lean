/- GID: D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphStateSmallOrderClassification
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphStateSmallOrderClassification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Classify connected physical graph states supporting common hit laws at orders approaching one. -/

import D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderWalsh
import D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateConcentratableEntanglement
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderClassification
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderWalsh
section
variable {V : Type*} (A : V → V → Prop)

def Leaf (u v : V) : Prop := A u v ∧ ∀ z, A u z → z=v

def Twin (u v : V) : Prop := ∀ z, z≠u → z≠v → (A u z ↔ A v z)

def Related (u v : V) : Prop := Leaf A u v ∨ Leaf A v u ∨ Twin A u v

variable {A}
theorem twin_refl (u : V) : Twin A u u := fun _ _ _ => Iff.rfl
theorem twin_symm {u v : V} (h : Twin A u v) : Twin A v u :=
  fun z hz hv => (h z hv hz).symm

theorem twin_trans (hs : ∀ i j, A i j ↔ A j i) {u v w : V}
    (h₁ : Twin A u v) (h₂ : Twin A v w) : Twin A u w := by
  by_cases e₁ : u=v
  · subst v; exact h₂
  by_cases e₂ : v=w
  · subst w; exact h₁
  by_cases e₃ : u=w
  · subst w; exact twin_refl _
  intro z hu hw
  by_cases hz : z=v
  · subst z
    exact ((hs u v).trans (h₂ u e₁ e₃)).trans
      (((hs w u).trans (h₁ w (Ne.symm e₃) (Ne.symm e₂))).trans ((hs v w)))
  · exact (h₁ z hu hz).trans (h₂ z hz hw)

private theorem leaf_pair {u v w : V} (h₁ : Leaf A u w) (h₂ : Leaf A v w) : Twin A u v := by
  intro z _ _
  constructor
  · intro hz
    rw [h₁.2 z hz]
    exact h₂.1
  · intro hz
    rw [h₂.2 z hz]
    exact h₁.1

private theorem leaf_then_twin (hs : ∀ i j, A i j ↔ A j i) {u v w : V}
    (h₁ : Leaf A u v) (h₂ : Twin A v w) (huv : u≠v) : Related A u w := by
  by_cases h : u=w
  · subst w; exact Or.inr (Or.inr (twin_refl _))
  have hwu : A w u := (h₂ u huv h).1 ((hs u v).1 h₁.1)
  have hwv : w=v := h₁.2 w ((hs w u).1 hwu)
  subst w
  exact Or.inl h₁

private theorem twin_then_leaf (hs : ∀ i j, A i j ↔ A j i)
    (hd : ∀ i, ¬A i i) {u v w : V}
    (h₁ : Twin A u v) (h₂ : Leaf A v w) : Related A u w := by
  by_cases h₀ : u=v
  · subst u; exact Or.inl h₂
  by_cases h : u=w
  · subst w; exact Or.inr (Or.inr (twin_refl _))
  have hw : v≠w := fun e => hd v (e.symm ▸ h₂.1)
  have huw : A u w := (h₁ w (Ne.symm h) (Ne.symm hw)).2 h₂.1
  refine Or.inl ⟨huw,fun z hz => ?_⟩
  have hzu : z≠u := fun e => hd u (e ▸ hz)
  have hzv : z≠v := by
    intro e
    have hvu : A v u := (hs u v).1 (e ▸ hz)
    exact h (h₂.2 u hvu)
  exact h₂.2 z ((h₁ z hzu hzv).1 hz)

theorem related_symm {u v : V} : Related A u v → Related A v u := by
  rintro (h|h|h)
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (twin_symm h))

/-- Leaf-center links and ordinary twin links form a single equivalence
relation. Leaf-containing equivalence classes need no degree case split. -/
theorem related_trans (hs : ∀ i j, A i j ↔ A j i) (hd : ∀ i, ¬A i i) {u v w : V}
    (h₁ : Related A u v) (h₂ : Related A v w) : Related A u w := by
  rcases h₁ with h₁|h₁|h₁ <;> rcases h₂ with h₂|h₂|h₂
  · have he := h₂.2 u ((hs u v).1 h₁.1)
    subst w; exact Or.inr (Or.inr (twin_refl _))
  · exact Or.inr (Or.inr (leaf_pair h₁ h₂))
  · exact leaf_then_twin hs h₁ h₂ (fun e => hd u (e.symm ▸ h₁.1))
  · have he := h₁.2 w h₂.1
    subst w; exact Or.inr (Or.inr (twin_refl _))
  · have he := h₁.2 w ((hs w v).1 h₂.1)
    subst w; exact Or.inr (Or.inr (twin_refl _))
  · exact twin_then_leaf hs hd (twin_symm h₂) h₁ |> related_symm
  · exact twin_then_leaf hs hd h₁ h₂
  · exact related_symm (leaf_then_twin hs h₂ (twin_symm h₁) (fun e => hd w (e.symm ▸ h₂.1)))
  · exact Or.inr (Or.inr (twin_trans hs h₁ h₂))

theorem related_equiv (hs : ∀ i j, A i j ↔ A j i) (hd : ∀ i, ¬A i i) :
    Equivalence (Related A) :=
  ⟨fun u => Or.inr (Or.inr (twin_refl u)),related_symm,related_trans hs hd⟩

/-- A class carrying a leaf consists exactly of its center and the leaves
with that center; there is no hidden second center in the quotient. -/
theorem class_of_leaf (hs : ∀ i j, A i j ↔ A j i) (hd : ∀ i, ¬A i i)
    {u v : V} (h : Leaf A u v) (w : V) : Related A u w ↔ w=v ∨ Leaf A w v := by
  constructor
  · rintro (hu|hw|ht)
    · exact Or.inl (h.2 w hu.1)
    · exact Or.inl (h.2 w ((hs w u).1 hw.1))
    · by_cases hu : w=u
      · subst w; exact Or.inr h
      by_cases hv : w=v
      · exact Or.inl hv
      have huv : v≠u := fun e => hd u (e ▸ h.1)
      have hadj : A w v := (ht v huv (Ne.symm hv)).1 h.1
      refine Or.inr ⟨hadj,fun i hi => ?_⟩
      have hiw : i≠w := fun e => hd w (e ▸ hi)
      have hiu : i≠u := by
        intro e
        exact hv (h.2 w ((hs w u).1 (e ▸ hi)))
      exact h.2 i ((ht i hiu hiw).2 hi)
  · rintro (rfl|hw)
    · exact Or.inl h
    · exact Or.inr (Or.inr (leaf_pair h hw))

variable (A) in
def AllRelated : Prop := ∀ i j, Related A i j
variable (A) in
def Star : Prop := ∃ c, ∀ i, i≠c → Leaf A i c
variable (A) in
def Clique : Prop := ∀ i j, i≠j → A i j

/-- Non-isolated graphs with a single class are exactly the stars or cliques. -/
theorem all_related_iff (hs : ∀ i j, A i j ↔ A j i) (hd : ∀ i, ¬A i i)
    (hn : ∀ i, ∃ j, A i j) : AllRelated A ↔ Star A ∨ Clique A := by
  constructor
  · intro h
    by_cases hl : ∃ u v, Leaf A u v
    · obtain ⟨u,v,huv⟩ := hl
      exact Or.inl ⟨v,fun i hi =>
        ((class_of_leaf hs hd huv i).1 (h u i)).resolve_left hi⟩
    · apply Or.inr
      intro i j hij
      obtain ⟨k,hik⟩ := hn i
      by_cases hkj : k=j
      · simpa [hkj] using hik
      have hki : i≠k := fun e => hd i (e.symm ▸ hik)
      rcases h k j with ha|ha|ht
      · exact (hl ⟨k,j,ha⟩).elim
      · exact (hl ⟨j,k,ha⟩).elim
      · exact (hs j i).1 ((ht i hki hij).1 ((hs i k).1 hik))
  · rintro (⟨c,hc⟩|hc) i j
    · by_cases hi : i=c
      · subst i
        by_cases hj : j=c
        · subst j; exact Or.inr (Or.inr (twin_refl _))
        · exact Or.inr (Or.inl (hc j hj))
      · by_cases hj : j=c
        · subst j; exact Or.inl (hc i hi)
        · exact Or.inr (Or.inr (leaf_pair (hc i hi) (hc j hj)))
    · exact Or.inr (Or.inr (fun z hzi hzj =>
        iff_of_true (hc i z (Ne.symm hzi)) (hc j z (Ne.symm hzj))))

end
end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderClassification

namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderClassification
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderWalsh
open Finset Matrix
open scoped BigOperators Classical
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateConcentratableEntanglement
noncomputable section

private theorem compl_eq {V : Type*} [Fintype V] (U : Finset V) : complement U = Uᶜ := by
  ext i; simp [complement]

theorem cut_compl {V : Type*} [Fintype V] (A : Matrix V V (ZMod 2))
    (hs : ∀ i j, A i j=A j i) (U : Finset V) :
    cutRank A (complement U) = cutRank A U := by
  unfold cutRank
  have hcc : complement (complement U) = U := by rw [compl_eq,compl_eq,compl_compl]
  rw [hcc]
  have h : (cutMatrix A U (complement U))ᵀ = cutMatrix A (complement U) U := by
    ext i j
    exact hs j.val i.val
  rw [←h,rank_transpose]

theorem cut_empty {V : Type*} [Fintype V] (A : Matrix V V (ZMod 2)) :
    cutRank A ∅=0 := by
  have h := rank_le_card_width (cutMatrix A ∅ (complement ∅))
  have he : Fintype.card (↥(∅ : Finset V)) = 0 := by simp
  rw [he] at h
  exact Nat.eq_zero_of_le_zero h

/-- Native physical signed obstruction on an actual finite graph. The graph
construction only has to supply the rank-one class and crossing rank-two
certificate; the interval and sign follow without a limit argument. -/
theorem actual_gap {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2))
    (hs : ∀ i j, A i j=A j i) (hd : ∀ i, A i i=0)
    (C : Finset (Fin n)) (hC : cutRank A C=1)
    (hS : ∀ i, cutRank A {i}=1) (hP : ∀ i∈C, ∀ j∈Cᶜ, cutRank A {i,j}=2)
    {K : ℝ} (hK : 1<K)
    (hgap : (C.card : ℝ)*(Cᶜ.card : ℝ)*(1-(2:ℝ)^(1-K))<2) :
    ∃ T, Even T.card ∧ (T∩C).Nonempty ∧ (T∩Cᶜ).Nonempty ∧
      inverse (graphTraceMoment A K) T<0 := by
  let x : ℝ := (2:ℝ)^(1-K)
  have hx : x<1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hc (U : Finset (Fin n)) : cutRank A Uᶜ = cutRank A U := by
    have he : Uᶜ = complement U := by ext i; simp [complement]
    exact (congrArg (cutRank A) he).trans (cut_compl A hs U)
  have hm : graphTraceMoment A K = fun U => x^cutRank A U := by
    funext U
    rw [(physical_graph_gce_monotone n K A hs hd hK).1]
    exact (Real.rpow_mul (by norm_num : 0 ≤ (2:ℝ)) _ _).trans (Real.rpow_natCast x _)
  rw [hm]
  exact inverse_gap (cutRank A) C (cut_empty A) hc hC hS hP x hx hgap

end
end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderClassification

namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderClassification
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderWalsh
open Matrix Finset
open scoped BigOperators Classical Matrix

abbrev F := ZMod 2

theorem two_rows_full {J : Type*} [Fintype J] (A : Matrix (Fin 2) J F)
    (h0 : A 0 ≠ 0) (h1 : A 1 ≠ 0) (hne : A 0 ≠ A 1) : A.rank=2 := by
  have hi : LinearIndependent F A.row := by
    rw [Fintype.linearIndependent_iff]
    intro f hf i
    rw [Fin.sum_univ_two] at hf
    change f 0 • A 0 + f 1 • A 1 = 0 at hf
    have hF (c : F) : c=0 ∨ c=1 := by
      fin_cases c
      · exact Or.inl rfl
      · exact Or.inr rfl
    have hneg : -(A 1)=A 1 := funext fun j => ZMod.neg_eq_self_mod_two _
    have hz : f 0=0 ∧ f 1=0 := by
      rcases hF (f 0) with h₀|h₀ <;> rcases hF (f 1) with h₁|h₁
      · exact ⟨h₀,h₁⟩
      · rw [h₀,h₁,zero_smul,one_smul,zero_add] at hf
        exact (h1 hf).elim
      · rw [h₀,h₁,zero_smul,one_smul,add_zero] at hf
        exact (h0 hf).elim
      · rw [h₀,h₁,one_smul,one_smul,add_eq_zero_iff_eq_neg,hneg] at hf
        exact (hne hf).elim
    fin_cases i
    · exact hz.1
    · exact hz.2
  simpa using hi.rank_matrix

theorem two_rows_small {J : Type*} [Fintype J] (A : Matrix (Fin 2) J F)
    (h : A 0=0 ∨ A 1=0 ∨ A 0=A 1) : A.rank≤1 := by
  obtain h|h|h := h
  · have he : A = vecMulVec (![0,1] : Fin 2 → F) (A 1) := by
      ext i j
      fin_cases i
      · simpa [vecMulVec] using congrFun h j
      · simp [vecMulVec]
    rw [he]
    exact rank_vecMulVec_le _ _
  · have he : A = vecMulVec (![1,0] : Fin 2 → F) (A 0) := by
      ext i j
      fin_cases i
      · simp [vecMulVec]
      · simpa [vecMulVec] using congrFun h j
    rw [he]
    exact rank_vecMulVec_le _ _
  · have he : A = vecMulVec (![1,1] : Fin 2 → F) (A 1) := by
      ext i j
      fin_cases i
      · simpa [vecMulVec] using congrFun h j
      · simp [vecMulVec]
    rw [he]
    exact rank_vecMulVec_le _ _

theorem two_rows_iff {J : Type*} [Fintype J] (A : Matrix (Fin 2) J F) :
    A.rank≤1 ↔ A 0=0 ∨ A 1=0 ∨ A 0=A 1 := by
  refine ⟨?_,two_rows_small A⟩
  intro h
  by_contra! hh
  have hr := two_rows_full A hh.1 hh.2.1 hh.2.2
  omega

end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderClassification

namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderClassification
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderWalsh
open Matrix Finset
open scoped BigOperators Classical Matrix
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateConcentratableEntanglement

noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]

def adj (A : Matrix V V F) (i j : V) : Prop := A i j ≠ 0
def cutConnected (A : Matrix V V F) : Prop :=
  ∀ U : Finset V, U.Nonempty → (complement U).Nonempty →
    ∃ i ∈ U, ∃ j ∈ complement U, adj A j i

private def pairIndex {i j : V} (h : i≠j) : Fin 2 ≃ ↥({i,j} : Finset V) := by
  let f : Fin 2 → ↥({i,j} : Finset V) :=
    ![(⟨i,by simp⟩ : ↥({i,j} : Finset V)),⟨j,by simp⟩]
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · intro x y he
    fin_cases x <;> fin_cases y
    · rfl
    · exact (h (congrArg Subtype.val he)).elim
    · exact (h (congrArg Subtype.val he).symm).elim
    · rfl
  · rintro ⟨z,hz⟩
    simp only [mem_insert,mem_singleton] at hz
    rcases hz with rfl|rfl
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩

theorem related_iff_small (A : Matrix V V F) (hs : ∀ i j, A i j=A j i)
    (hn : ∀ i, ∃ j, adj A i j) {i j : V} (hij : i≠j)
    (hd : ∀ i, A i i=0) : Related (adj A) i j ↔ cutRank A {i,j}≤1 := by
  let C := ({i,j} : Finset V)
  let B := ((cutMatrix A C (complement C))ᵀ).submatrix (pairIndex hij) id
  have hr : B.rank=cutRank A C := by
    change (((cutMatrix A C (complement C))ᵀ).submatrix (pairIndex hij) (Equiv.refl _)).rank = _
    rw [rank_submatrix,rank_transpose]
    rfl
  have h₀ (k : complement C) : B 0 k = A i k.val := hs _ _
  have h₁ (k : complement C) : B 1 k = A j k.val := hs _ _
  have out (k : V) : k∈complement C ↔ k≠i ∧ k≠j := by
    simp [C,complement]
  have leaf0 : B 0=0 ↔ Leaf (adj A) i j := by
    constructor
    · intro hz
      have only (z : V) (hz' : adj A i z) : z=j := by
        by_contra! h
        have hne : z≠i := fun e => by exact hz' (e.symm ▸ hd i)
        let k : complement C := ⟨z,(out z).2 ⟨hne,h⟩⟩
        exact hz' ((h₀ k).symm.trans (congrFun hz k))
      obtain ⟨z,hz'⟩ := hn i
      exact ⟨(only z hz') ▸ hz',only⟩
    · intro h
      funext k
      rw [h₀]
      by_contra! hnz
      exact ((out _).1 k.property).2 (h.2 _ hnz)
  have leaf1 : B 1=0 ↔ Leaf (adj A) j i := by
    constructor
    · intro hz
      have only (z : V) (hz' : adj A j z) : z=i := by
        by_contra! h
        have hne : z≠j := fun e => by exact hz' (e.symm ▸ hd j)
        let k : complement C := ⟨z,(out z).2 ⟨h,hne⟩⟩
        exact hz' ((h₁ k).symm.trans (congrFun hz k))
      obtain ⟨z,hz'⟩ := hn j
      exact ⟨(only z hz') ▸ hz',only⟩
    · intro h
      funext k
      rw [h₁]
      by_contra! hnz
      exact ((out _).1 k.property).1 (h.2 _ hnz)
  have ht : B 0=B 1 ↔ Twin (adj A) i j := by
    constructor
    · intro h z hi hj
      let k : complement C := ⟨z,(out z).2 ⟨hi,hj⟩⟩
      have e := (h₀ k).symm.trans ((congrFun h k).trans (h₁ k))
      unfold adj
      rw [e]
    · intro h
      funext k
      rw [h₀,h₁]
      obtain ⟨hi,hj⟩ := (out _).1 k.property
      have hh := h k.val hi hj
      have casesF (a : F) : a=0 ∨ a=1 := by
        fin_cases a
        · exact Or.inl rfl
        · exact Or.inr rfl
      rcases casesF (A i k.val) with hᵢ|hᵢ <;>
        rcases casesF (A j k.val) with hⱼ|hⱼ <;> simp_all [adj]
  have he := two_rows_iff B
  rw [hr,leaf0,leaf1,ht] at he
  exact he.symm

end
end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderClassification

namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderClassification
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderWalsh
open Matrix Finset
open scoped BigOperators Classical Matrix
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateConcentratableEntanglement

noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem cut_pos (A : Matrix V V F) (hc : cutConnected A) (C : Finset V)
    (hC : C.Nonempty) (hD : (complement C).Nonempty) : 1 ≤ cutRank A C := by
  obtain ⟨i,hi,j,hj,he⟩ := hc C hC hD
  let M := cutMatrix A C (complement C)
  let I : Fin 1 → C := fun _ => ⟨i,hi⟩
  let J : Fin 1 → complement C := fun _ => ⟨j,hj⟩
  have heq : A j i = 1 := by
    generalize h₀ : A j i = x at he ⊢
    fin_cases x
    · exact (he h₀).elim
    · rfl
  have hM : M.submatrix J I = (1 : Matrix (Fin 1) (Fin 1) F) := by
    ext a b
    have h : a=b := Subsingleton.elim _ _
    subst b
    simpa [M,I,J,cutMatrix] using heq
  have h := rank_submatrix_le M J I
  rw [hM,rank_one] at h
  simpa [M,cutRank] using h

omit [DecidableEq V] in
theorem singleton_rank (A : Matrix V V F)
    (hd : ∀ i, A i i=0) (hn : ∀ i, ∃ j, adj A i j) (hc : cutConnected A) (i : V) :
    cutRank A {i}=1 := by
  obtain ⟨j,hj⟩ := hn i
  have hD : (complement ({i} : Finset V)).Nonempty := by
    refine ⟨j,?_⟩
    simp [complement]
    intro e
    exact hj (e ▸ hd i)
  apply Nat.le_antisymm _ (cut_pos A hc _ (by simp) hD)
  have h := rank_le_card_width (cutMatrix A {i} (complement {i}))
  simpa [cutRank] using h

private theorem class_cut_le_one (A : Matrix V V F) (hs : ∀ i j, A i j=A j i)
    (hd : ∀ i, A i i=0) (u : V) (C : Finset V)
    (hC : ∀ i, i∈C ↔ Related (adj A) u i) : cutRank A C≤1 := by
  have hsym (i j : V) : adj A i j ↔ adj A j i := by simp only [adj,hs]
  have hdiag (i : V) : ¬adj A i i := by simp [adj,hd]
  have hEquiv := related_equiv (A:=adj A) hsym hdiag
  let M := cutMatrix A C (complement C)
  have hu : u∈C := (hC u).2 (hEquiv.refl u)
  by_cases hl : ∃ i∈C, ∃ j, Leaf (adj A) i j
  · obtain ⟨i,hi,c,hc⟩ := hl
    have hrel (k : V) : k∈C ↔ Related (adj A) i k := by
      rw [hC]
      exact ⟨fun h => hEquiv.trans (hEquiv.symm ((hC i).1 hi)) h,
        fun h => hEquiv.trans ((hC i).1 hi) h⟩
    have hleaf (k : V) : k∈C ↔ k=c ∨ Leaf (adj A) k c :=
      (hrel k).trans (class_of_leaf hsym hdiag hc k)
    let f : complement C → F := fun k => A k.val c
    let g : C → F := fun b => if b.val=c then 1 else 0
    have he : M=vecMulVec f g := by
      ext k b
      have hk : k.val∉C := by simpa [complement] using k.property
      rcases (hleaf b.val).1 b.property with hb|hb
      · simp [M,cutMatrix,vecMulVec,f,g,hb]
      · by_cases hb' : b.val=c
        · simp [M,cutMatrix,vecMulVec,f,g,hb']
        · have hz : A k.val b.val=0 := by
            by_contra! hn
            have hbb := hb.2 k.val ((hsym k.val b.val).1 hn)
            exact hk ((hleaf k.val).2 (Or.inl hbb))
          simp [M,cutMatrix,vecMulVec,g,hb',hz]
    unfold cutRank
    change M.rank≤1
    rw [he]
    exact rank_vecMulVec_le _ _
  · let f : complement C → F := fun k => A k.val u
    have he : M=vecMulVec f (fun _ : C => 1) := by
      ext k b
      have hk : k.val∉C := by simpa [complement] using k.property
      have ht : Twin (adj A) u b.val := by
        rcases (hC b.val).1 b.property with h|h|h
        · exact (hl ⟨u,hu,b.val,h⟩).elim
        · exact (hl ⟨b.val,b.property,u,h⟩).elim
        · exact h
      have hku : k.val≠u := fun e => hk (e.symm ▸ hu)
      have hkb : k.val≠b.val := fun e => hk (e.symm ▸ b.property)
      have hn := (hsym k.val b.val).trans ((ht k.val hku hkb).symm.trans (hsym u k.val))
      have hh (a : F) : a=0 ∨ a=1 := by
        fin_cases a
        · exact Or.inl rfl
        · exact Or.inr rfl
      have hz : A k.val b.val=A k.val u := by
        rcases hh (A k.val b.val) with h₁|h₁ <;> rcases hh (A k.val u) with h₂|h₂ <;>
          simp_all [adj]
      simp [M,cutMatrix,vecMulVec,f,hz]
    unfold cutRank
    change M.rank≤1
    rw [he]
    exact rank_vecMulVec_le _ _

/-- A proper class has rank one and every pair straddling it has rank two.
No graph classification theorem is assumed. -/
theorem class_certificate (A : Matrix V V F) (hs : ∀ i j, A i j=A j i)
    (hd : ∀ i, A i i=0) (hn : ∀ i, ∃ j, adj A i j) (hc : cutConnected A)
    (hfull : ¬Star (adj A) ∧ ¬Clique (adj A)) :
    ∃ C : Finset V, cutRank A C=1 ∧
      (∀ i, cutRank A {i}=1) ∧ (∀ i∈C, ∀ j∈Cᶜ, cutRank A {i,j}=2) := by
  have hsym (i j : V) : adj A i j ↔ adj A j i := by simp only [adj,hs]
  have hdiag (i : V) : ¬adj A i i := by simp [adj,hd]
  have hEquiv := related_equiv (A:=adj A) hsym hdiag
  have hsep : ¬AllRelated (adj A) := by
    intro h
    exact ((all_related_iff hsym hdiag hn).1 h).elim hfull.1 hfull.2
  unfold AllRelated at hsep
  push Not at hsep
  obtain ⟨u,v,huv⟩ := hsep
  let C := univ.filter (Related (adj A) u)
  have hC (i : V) : i∈C ↔ Related (adj A) u i := by simp [C]
  have hu : u∈C := (hC _).2 (hEquiv.refl _)
  have hv : v∈complement C := by simpa [complement,C] using huv
  refine ⟨C,Nat.le_antisymm (class_cut_le_one A hs hd u C hC) (cut_pos A hc C ⟨u,hu⟩ ⟨v,hv⟩),
    singleton_rank A hd hn hc,?_⟩
  intro i hi j hj
  have hj' : j∉C := mem_compl.mp hj
  have hij : i≠j := fun e => hj' (e ▸ hi)
  have hlow : ¬cutRank A {i,j}≤1 := by
    intro h
    exact hj' ((hC j).2 (hEquiv.trans ((hC i).1 hi) ((related_iff_small A hs hn hij hd).2 h)))
  have hhi := rank_le_card_width (cutMatrix A {i,j} (complement {i,j}))
  have hcard : Fintype.card ↥({i,j} : Finset V)=2 := by rw [Fintype.card_coe]; simp [hij]
  rw [hcard] at hhi
  change cutRank A {i,j}≤2 at hhi
  omega

end
end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderClassification

namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderClassification
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderWalsh
open Matrix Finset
open scoped BigOperators Classical Matrix
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateConcentratableEntanglement

noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem binary {a : F} (ha : a≠0) : a=1 := by
  fin_cases a
  · exact (ha rfl).elim
  · rfl

omit [DecidableEq V] in
theorem flat_cut_le_one (A : Matrix V V F) (hs : ∀ i j, A i j=A j i)
    (hf : Star (adj A) ∨ Clique (adj A)) (U : Finset V) : cutRank A U≤1 := by
  rcases hf with ⟨c,hc⟩|hc
  · have hmain (S : Finset V) (hcS : c∈S) : cutRank A S≤1 := by
      let f : complement S → F := fun k => A k.val c
      let g : S → F := fun b => if b.val=c then 1 else 0
      have he : cutMatrix A S (complement S)=vecMulVec f g := by
        ext k b
        by_cases hb : b.val=c
        · simp [cutMatrix,vecMulVec,f,g,hb]
        · have hzero : A k.val b.val=0 := by
            by_contra! hn
            have hnc : k.val≠c := by
              intro e
              have he : c∈complement S := e ▸ k.property
              simp [complement,hcS] at he
            exact hnc ((hc b.val hb).2 k.val (by unfold adj; rwa [hs]))
          simp [cutMatrix,vecMulVec,g,hb,hzero]
      unfold cutRank
      rw [he]
      exact rank_vecMulVec_le _ _
    by_cases h : c∈U
    · exact hmain U h
    · rw [←cut_compl A hs U]
      exact hmain _ (by simp [complement,h])
  · have h : cutMatrix A U (complement U)=vecMulVec (fun _ => (1:F)) (fun _ => (1:F)) := by
      ext k b
      have hk : k.val∉U := by simpa [complement] using k.property
      have hne : k.val≠b.val := fun e => hk (e.symm ▸ b.property)
      simpa [cutMatrix,vecMulVec] using binary (hc k.val b.val hne)
    unfold cutRank
    rw [h]
    exact rank_vecMulVec_le _ _

private theorem rank_flat (A : Matrix V V F) (hs : ∀ i j, A i j=A j i)
    (hc : cutConnected A) (hf : Star (adj A) ∨ Clique (adj A)) (U : Finset V) :
    cutRank A U = if U=∅ ∨ U=univ then 0 else 1 := by
  by_cases h : U=∅ ∨ U=univ
  · rw [ite_eq_left h]
    rcases h with rfl|rfl
    · exact cut_empty A
    · rw [←cut_compl A hs]
      have he : complement (univ : Finset V)=∅ := by simp [complement]
      rw [he,cut_empty]
  · rw [ite_eq_right h]
    apply Nat.le_antisymm (flat_cut_le_one A hs hf U)
    apply cut_pos A hc
    · exact nonempty_iff_ne_empty.mpr (fun e => h (Or.inl e))
    · exact nonempty_iff_ne_empty.mpr (fun he => h (Or.inr (by simpa [complement] using he)))

private theorem sum_sign (T : Finset V) :
    (∑ U : Finset V, sign U T) = if T=∅ then walshNorm V else 0 := by
  by_cases h : T=∅
  · subst T
    rw [ite_eq_left rfl]
    simp [sign,side,ind,walshNorm,Fintype.card_finset]
  · rw [ite_eq_right h]
    have he (U : Finset V) : sign U T = Character.char T U := by
      rw [sign_as_power,Character.char_eq,inter_comm]
    simp_rw [he]
    exact Character.char_sum_zero T (nonempty_iff_ne_empty.mpr h)

/-- Walsh masses on stars and cliques are the explicit empty-atom / uniform
even law, with no approximation in the order. -/
theorem flat_law {x : ℝ} (hx : 0≤x) (hX : x≤1) (A : Matrix V V F)
    (hs : ∀ i j, A i j=A j i) (hc : cutConnected A)
    (hf : Star (adj A) ∨ Clique (adj A)) (T : Finset V) :
    0 ≤ inverse (fun U => x^cutRank A U) T := by
  by_cases hv : (univ : Finset V)=∅
  · have h (U : Finset V) : U=∅ := subset_antisymm (hv ▸ subset_univ U) (empty_subset U)
    have hf₀ (U : Finset V) : x^cutRank A U=1 := by rw [h U,cut_empty,pow_zero]
    have hs₀ (U : Finset V) : sign U T=1 := by rw [h T]; simp [sign,side,ind]
    unfold inverse
    simp_rw [hf₀,hs₀]
    exact div_nonneg (sum_nonneg fun _ _ => by positivity) (by unfold walshNorm; positivity)
  have hm (U : Finset V) : x^cutRank A U =
      x+(1-x)*(ind (U=∅)+ind (U=univ)) := by
    rw [rank_flat A hs hc hf U]
    by_cases h₁ : U=∅ <;> by_cases h₂ : U=univ
    · exact (hv (h₂.symm.trans h₁)).elim
    · simp [h₁,Ne.symm hv,ind]
    · simp [h₂,hv,ind]
    · simp [h₁,h₂,ind]
  have hS : ∑ U : Finset V, (x^cutRank A U)*sign U T =
      x*(∑ U, sign U T)+(1-x)*(sign ∅ T+sign univ T) := by
    simp_rw [hm,add_mul,mul_assoc,add_mul,sum_add_distrib,←mul_sum]
    congr 2; simp [ind,ite_mul,Finset.sum_add_distrib]
  unfold inverse
  rw [hS,sum_sign]
  have h₁ : 0 ≤ (if T=∅ then walshNorm V else 0) := by
    split
    · unfold walshNorm; positivity
    · exact le_rfl
  have h₂ : 0≤sign ∅ T+sign univ T := by
    simp [sign,side,ind]
    split <;> norm_num
  apply div_nonneg _ (by unfold walshNorm; positivity)
  exact add_nonneg (mul_nonneg hx h₁) (mul_nonneg (sub_nonneg.mpr hX) h₂)

end
end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderClassification

namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderClassification
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderWalsh
open Matrix Finset
open scoped BigOperators Classical Matrix
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateConcentratableEntanglement

noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]

def Covered (A : Matrix V V F) (x : ℝ) : Prop :=
  ∀ T, 0 ≤ inverse (fun U => x^cutRank A U) T

/-- Final connected-graph endpoint: existence of admissible orders as
close to x=1 as desired and admissibility at all x in (0,1) are equivalent.
x is the reciprocal of q. A graph outside the class has a finite gap. -/
theorem connected_classification (A : Matrix V V F) (hs : ∀ i j, A i j=A j i)
    (hd : ∀ i, A i i=0) (hn : ∀ i, ∃ j, adj A i j) (hc : cutConnected A) :
    ((∀ ε : ℝ, 0<ε → ∃ x : ℝ, 0<x ∧ x<1 ∧ 1-x<ε ∧ Covered A x)
        ↔ Star (adj A) ∨ Clique (adj A)) ∧
      ((∀ x : ℝ, 0<x → x<1 → Covered A x) ↔ Star (adj A) ∨ Clique (adj A)) := by
  have hf (h : Star (adj A) ∨ Clique (adj A)) {x : ℝ} (h₁ : 0<x) (h₂ : x<1) :
      Covered A x := flat_law h₁.le h₂.le A hs hc h
  have hin : (∀ x : ℝ, 0<x → x<1 → Covered A x) →
      ∀ ε : ℝ, 0<ε → ∃ x : ℝ, 0<x ∧ x<1 ∧ 1-x<ε ∧ Covered A x := by
    intro hall ε hε
    let z := min ε 1 / 2
    have hz : 0<z := by exact half_pos (lt_min hε zero_lt_one)
    have hz' : z≤1/2 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
    have hze : z<ε := by
      have h := min_le_left ε 1
      dsimp [z]
      linarith
    exact ⟨1-z,by linarith,by linarith,by linarith,hall _ (by linarith) (by linarith)⟩
  have hn' : (∀ ε : ℝ, 0<ε → ∃ x : ℝ, 0<x ∧ x<1 ∧ 1-x<ε ∧ Covered A x) →
      Star (adj A) ∨ Clique (adj A) := by
    intro h
    by_contra! hc'
    obtain ⟨C,hC,hS,hP⟩ := class_certificate A hs hd hn hc hc'
    let m := (C.card : ℝ)*(Cᶜ.card : ℝ)
    have hm : 0≤m := by dsimp [m]; positivity
    obtain ⟨x,hx,hX,hnear,hCov⟩ := h (1/(m+1)) (by positivity)
    have hnear' := (lt_div_iff₀ (by positivity : 0<m+1)).1 hnear
    have hgap : m*(1-x)<2 := by
      nlinarith
    have hc0 (U : Finset V) : cutRank A Uᶜ=cutRank A U := by
      have he : Uᶜ=complement U := by ext i; simp [complement]
      exact (congrArg (cutRank A) he).trans (cut_compl A hs U)
    obtain ⟨T,_,_,_,ht⟩ := inverse_gap (cutRank A) C (cut_empty A) hc0 hC hS hP x hX hgap
    exact ht.not_ge (hCov T)
  exact ⟨⟨hn',fun h => hin fun _ => hf h⟩,⟨fun h => hn' (hin h),fun h _ => hf h⟩⟩

theorem quantitative_actual {n : ℕ} (A : Matrix (Fin n) (Fin n) F)
    (hs : ∀ i j, A i j=A j i) (hd : ∀ i, A i i=0) (hn : ∀ i, ∃ j, adj A i j)
    (hc : cutConnected A) (hbad : ¬ Star (adj A) ∧ ¬ Clique (adj A)) :
    ∃ C : Finset (Fin n), ∀ K : ℝ, 1<K →
      (C.card : ℝ)*(Cᶜ.card : ℝ)*(1-(2:ℝ)^(1-K))<2 →
      ∃ T, Even T.card ∧ (T∩C).Nonempty ∧ (T∩Cᶜ).Nonempty ∧
        inverse (graphTraceMoment A K) T<0 := by
  obtain ⟨C,hC,hS,hP⟩ := class_certificate A hs hd hn hc hbad
  exact ⟨C,fun _ hK hgap => actual_gap A hs hd C hC hS hP hK hgap⟩

end
end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderClassification

namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderClassification
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderWalsh
open Matrix Finset
open scoped BigOperators Classical Matrix
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateConcentratableEntanglement
noncomputable section

theorem actual_hit_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) F) (hs : ∀ i j, A i j=A j i)
    (hd : ∀ i, A i i=0) {K : ℝ} (hK : 1<K) :
    hitLaw (graphTraceMoment A K) ↔ Covered A ((2:ℝ)^(1-K)) := by
  have h (U : Finset (Fin n)) : graphTraceMoment A K U = ((2:ℝ)^(1-K))^cutRank A U := by
    rw [(physical_graph_gce_monotone n K A hs hd hK).1]
    exact (Real.rpow_mul (by norm_num : 0 ≤ (2:ℝ)) _ _).trans (Real.rpow_natCast _ _)
  rw [show graphTraceMoment A K = _ from funext h]
  exact hitLaw_iff _ (by rw [cut_empty,pow_zero])

private theorem exists_order (x : ℝ) (hx : 0<x) (hX : x<1) :
    ∃ K : ℝ, 1<K ∧ (2:ℝ)^(1-K)=x := by
  let ℓ := Real.log x / Real.log 2
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hℓ : ℓ<0 := div_neg_of_neg_of_pos (Real.log_neg hx hX) hlog
  refine ⟨1-ℓ,by linarith,?_⟩
  rw [show 1- (1-ℓ)=ℓ by ring,Real.rpow_def_of_pos (by norm_num)]
  unfold ℓ
  rw [mul_comm,div_mul_cancel₀ _ hlog.ne',Real.exp_log hx]

/-- Sharp classification for actual physical graph-state GCE at all real
orders on a connected graph with no isolated vertices. -/
theorem all_actual_orders_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) F)
    (hs : ∀ i j, A i j=A j i) (hd : ∀ i, A i i=0) (hn : ∀ i, ∃ j, adj A i j)
    (hc : cutConnected A) :
    (∀ K : ℝ, 1<K → hitLaw (graphTraceMoment A K)) ↔ Star (adj A) ∨ Clique (adj A) := by
  rw [← (connected_classification A hs hd hn hc).2]
  constructor
  · intro h x hx hX
    obtain ⟨K,hK,he⟩ := exists_order x hx hX
    rw [←he,←actual_hit_iff A hs hd hK]
    exact h K hK
  · intro h K hK
    rw [actual_hit_iff A hs hd hK]
    exact h _ (by positivity)
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))

/-- Even arbitrarily low physical orders already force the same class:
this keeps the original K parameter, not merely a surrogate base. -/
theorem near_actual_orders_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) F)
    (hs : ∀ i j, A i j=A j i) (hd : ∀ i, A i i=0) (hn : ∀ i, ∃ j, adj A i j)
    (hc : cutConnected A) :
    ((∀ ε : ℝ, 0<ε → ∃ K : ℝ, 1<K ∧ K<1+ε ∧ hitLaw (graphTraceMoment A K))
      ↔ Star (adj A) ∨ Clique (adj A)) := by
  constructor
  · intro h
    apply (connected_classification A hs hd hn hc).1.mp
    intro ε hε
    let x := max (1-ε/2) (1/2)
    have hx : 0<x := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    have hX : x<1 := max_lt (by linarith) (by norm_num)
    have hle : 1-ε/2≤x := le_max_left _ _
    obtain ⟨K,hK,he⟩ := exists_order x hx hX
    obtain ⟨K',hK',hK'lt,hLaw⟩ := h (K-1) (by linarith)
    let y : ℝ := (2:ℝ)^(1-K')
    have hy : 0<y := by dsimp [y]; positivity
    have hylt : y<1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    have hxy : x<y := by
      rw [←he]
      exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
    exact ⟨y,hy,hylt,by linarith,(actual_hit_iff A hs hd hK').1 hLaw⟩
  · intro h ε hε
    refine ⟨1+ε/2,by linarith,by linarith,?_⟩
    exact (all_actual_orders_iff A hs hd hn hc).2 h _ (by linarith)

end
end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderClassification

namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderClassification
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderWalsh
open Finset Matrix
open scoped BigOperators Classical symmDiff
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateConcentratableEntanglement
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An explicit straddling even Fourier mode refutes conditional negative
definiteness of any connected graph outside the star/clique family. -/
theorem connected_negative_type_gap (A : Matrix V V F) (hs : ∀ i j, A i j=A j i)
    (hd : ∀ i, A i i=0) (hn : ∀ i, ∃ j, adj A i j) (hc : cutConnected A)
    (hb : ¬ Star (adj A) ∧ ¬ Clique (adj A)) :
    ¬negativeType (fun S => (cutRank A S : ℝ)) := by
  obtain ⟨C,hC,hS,hP⟩ := class_certificate A hs hd hn hc hb
  have hc0 (U : Finset V) : cutRank A Uᶜ=cutRank A U := by
    have he : Uᶜ=complement U := by ext i; simp [complement]
    exact (congrArg (cutRank A) he).trans (cut_compl A hs U)
  obtain ⟨T,_,hT,_,ht⟩ := generator_gap (cutRank A) C (cut_empty A) hc0 hC hS hP
  intro h
  exact ht.not_ge ((negative_type_iff_rates _).1 h T (hT.mono inter_subset_left))

theorem connected_negative_type_iff (A : Matrix V V F) (hs : ∀ i j, A i j=A j i)
    (hd : ∀ i, A i i=0) (hn : ∀ i, ∃ j, adj A i j) (hc : cutConnected A) :
    negativeType (fun S => (cutRank A S : ℝ)) ↔ Star (adj A) ∨ Clique (adj A) := by
  constructor
  · intro h
    by_contra! hbad
    exact connected_negative_type_gap A hs hd hn hc hbad h
  · intro h
    rw [negative_type_iff_rates]
    intro T hT
    have he (S : Finset V) : -(cutRank A S : ℝ) = (0:ℝ)^cutRank A S-1 := by
      have hr := flat_cut_le_one A hs h S
      rcases (Nat.le_one_iff_eq_zero_or_eq_one.mp hr) with hr|hr <;> norm_num [hr]
    have hsum : ∑ S : Finset V, sign S T=0 := by
      have hw (S : Finset V) : sign S T = Character.char T S := by
        rw [sign_symm,sign_char]
      simp_rw [hw]
      exact Character.char_sum_zero T hT
    have hEq : inverse (fun S => -(cutRank A S : ℝ)) T =
        inverse (fun S => (0:ℝ)^cutRank A S) T := by
      simp only [inverse,he,sub_mul,one_mul,sum_sub_distrib,hsum,sub_zero]
    rw [hEq]
    exact flat_law le_rfl zero_le_one A hs hc h T

end
end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderClassification

namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderClassification
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderWalsh
open Matrix Finset
open scoped BigOperators Classical Matrix
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateConcentratableEntanglement
noncomputable section

abbrev SmallMomentTable : Type :=
  ∀ n : ℕ, Matrix (Fin n) (Fin n) F → Finset (Fin n) → ℝ

def smallMomentTable (K : ℝ) : SmallMomentTable :=
  fun _ A => graphTraceMoment A K

theorem physical_gap_readout (K : ℝ) (hK : 1<K) :
    let observed := smallMomentTable K
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) F),
      (∀ i j, A i j=A j i) → (∀ i, A i i=0) → (∀ i, ∃ j, adj A i j) →
      cutConnected A → (¬Star (adj A) ∧ ¬Clique (adj A)) →
      ∃ C : Finset (Fin n),
        (C.card : ℝ)*(Cᶜ.card : ℝ)*(1-(2:ℝ)^(1-K))<2 →
        ∃ T, Even T.card ∧ (T∩C).Nonempty ∧ (T∩Cᶜ).Nonempty ∧
          inverse (observed n A) T<0 := by
  dsimp only
  intro n A hs hd hn hc hb
  obtain ⟨C,h⟩ := quantitative_actual A hs hd hn hc hb
  exact ⟨C,h K hK⟩

end
end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderClassification

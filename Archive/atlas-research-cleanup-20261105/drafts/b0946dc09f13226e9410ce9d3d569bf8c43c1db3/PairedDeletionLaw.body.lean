
namespace D5.S3.Combinatorics.CircularWords.PairedDeletionLaw

open D5.S3.Combinatorics.CircularWords.CircularDeletionTransport
open D5.S3.Combinatorics.CircularWords.CyclicInsertionGap
open D5.S3.Combinatorics.CircularWords.DeletionReadoutReconstruction
open D5.S3.Combinatorics.CircularWords.PairedDeletionFiber
open scoped BigOperators

universe u v
variable {α : Type u} [DecidableEq α]

/-- The complete carrier of nodup oriented cycles on the fixed support. -/
abbrev FixedCycles (A : Finset α) := {C : Cycle α // C.Nodup ∧ C.toFinset = A}

/-- Each paired channel observes two deletions of the same original. -/
def paired (a b : α) (C : Cycle α) : Cycle α × Cycle α :=
  (delete a C, delete b C)

private theorem block_positions {x y : α} {P Q : List α}
    (h : (P ++ [x,y] ++ Q).Nodup) (hxy : x ≠ y) :
    (P ++ [x,y] ++ Q).idxOf x = P.length ∧
    (P ++ [x,y] ++ Q).idxOf y = P.length + 1 := by
  have hd := (List.nodup_append'.mp (show (P ++ ([x,y] ++ Q)).Nodup by
    simpa only [List.append_assoc] using h)).2.2
  have hx : x ∉ P := by
    intro hx
    exact (List.disjoint_iff_ne.mp hd) x hx x (by simp) rfl
  have hy : y ∉ P := by
    intro hy
    exact (List.disjoint_iff_ne.mp hd) y hy y (by simp) rfl
  constructor <;>
    simp [List.append_assoc, List.idxOf_append_of_notMem hx,
      List.idxOf_append_of_notMem hy, hxy]

private theorem adjacent_positions {r x y : α} {W : List α}
    (hW : (r :: W).Nodup) (hxy : x ≠ y)
    (h : cyclicAdjacentAt r x y (r :: W : Cycle α)) :
    W.idxOf x + 1 = W.idxOf y ∨ W.idxOf y + 1 = W.idxOf x := by
  rcases h with ⟨P,Q,h | h⟩
  · have he := anchored_coe_injective hW h
    have ht : W = P ++ [x,y] ++ Q := by simpa only [List.append_eq, List.append_assoc] using he
    rw [ht]
    have hn : (P ++ [x,y] ++ Q).Nodup := ht ▸ hW.tail
    have hp := block_positions hn hxy
    exact Or.inl (by omega)
  · have he := anchored_coe_injective hW h
    have ht : W = P ++ [y,x] ++ Q := by simpa only [List.append_eq, List.append_assoc] using he
    rw [ht]
    have hn : (P ++ [y,x] ++ Q).Nodup := ht ▸ hW.tail
    have hp := block_positions hn hxy.symm
    exact Or.inr (by omega)

private theorem third_position {a b c : α} {P Q : List α}
    (hac : a ≠ c) (hbc : b ≠ c) :
    (P ++ [a,b] ++ Q).idxOf c = (P ++ [b,a] ++ Q).idxOf c := by
  by_cases hc : c ∈ P
  · simp only [List.append_assoc, List.idxOf_append_of_mem hc]
  · simp [List.append_assoc, List.idxOf_append_of_notMem hc, hac, hbc]

/-- With a common cut outside the three labels, a nontrivial a,b swap
cannot have a nontrivial b,c fibre at both ends. The fourth label supplies
that cut, so the argument includes wrap-around and support size four. -/
theorem swap_has_leaf {A : Finset α} (hA : 4 ≤ A.card)
    {a b c : α} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    {C D E H : Cycle α}
    (nC : C.Nodup) (nD : D.Nodup) (nE : E.Nodup) (nH : H.Nodup)
    (sC : C.toFinset = A) (sD : D.toFinset = A)
    (sE : E.toFinset = A) (sH : H.toFinset = A)
    (hCD : paired a b C = paired a b D) (hDC : D ≠ C)
    (hCE : paired b c C = paired b c E) (hEC : E ≠ C)
    (hDH : paired b c D = paired b c H) (hHD : H ≠ D) : False := by
  obtain ⟨r,hrA,hr⟩ : ∃ r ∈ A, r ∉ ({a,b,c} : Finset α) := by
    by_contra hn
    have hs : A ⊆ ({a,b,c} : Finset α) := by
      intro r hrA
      by_contra hr
      exact hn ⟨r,hrA,hr⟩
    have := Finset.card_le_card hs
    have : ({a,b,c} : Finset α).card ≤ 3 := Finset.card_le_three
    omega
  have hra : r ≠ a := by intro h; exact hr (by simp [h])
  have hrb : r ≠ b := by intro h; exact hr (by simp [h])
  have hrc : r ≠ c := by intro h; exact hr (by simp [h])
  have ab := (paired_fiber_iff_at_root hrA ha hb hra hrb hab nC nD sC sD).mp
    (Prod.mk.inj hCD)
  have bcC := (paired_fiber_iff_at_root hrA hb hc hrb hrc hbc nC nE sC sE).mp
    (Prod.mk.inj hCE)
  have bcD := (paired_fiber_iff_at_root hrA hb hc hrb hrc hbc nD nH sD sH).mp
    (Prod.mk.inj hDH)
  rcases ab with he | hs
  · exact hDC he.symm
  rcases bcC with he | hsC
  · exact hEC he.symm
  rcases bcD with he | hsD
  · exact hHD he.symm
  have adjC : cyclicAdjacentAt r b c C := by
    rcases hsC with ⟨P,Q,h | h⟩
    · exact ⟨P,Q,Or.inl h.1⟩
    · exact ⟨P,Q,Or.inr h.1⟩
  have adjD : cyclicAdjacentAt r b c D := by
    rcases hsD with ⟨P,Q,h | h⟩
    · exact ⟨P,Q,Or.inl h.1⟩
    · exact ⟨P,Q,Or.inr h.1⟩
  rcases hs with ⟨P,Q,h | h⟩
  · have nW : (r :: P ++ [a,b] ++ Q).Nodup :=
      Cycle.nodup_coe_iff.mp (h.1 ▸ nC)
    have nV : (r :: P ++ [b,a] ++ Q).Nodup :=
      Cycle.nodup_coe_iff.mp (h.2 ▸ nD)
    have pC := adjacent_positions nW hbc (h.1 ▸ adjC)
    have pD := adjacent_positions nV hbc (h.2 ▸ adjD)
    have pW := block_positions nW.tail hab
    have pV := block_positions nV.tail hab.symm
    have pT := third_position (P := P) (Q := Q) hac hbc
    simp only [List.append_eq, List.append_assoc] at pC pD pW pV pT
    rcases pC with hC | hC <;> rcases pD with hD | hD <;> omega
  · have nW : (r :: P ++ [b,a] ++ Q).Nodup :=
      Cycle.nodup_coe_iff.mp (h.1 ▸ nC)
    have nV : (r :: P ++ [a,b] ++ Q).Nodup :=
      Cycle.nodup_coe_iff.mp (h.2 ▸ nD)
    have pC := adjacent_positions nW hbc (h.1 ▸ adjC)
    have pD := adjacent_positions nV hbc (h.2 ▸ adjD)
    have pW := block_positions nW.tail hab.symm
    have pV := block_positions nV.tail hab
    have pT := third_position (P := P) (Q := Q) hac hbc
    simp only [List.append_eq, List.append_assoc] at pC pD pW pV pT
    rcases pC with hC | hC <;> rcases pD with hD | hD <;> omega

/-- Every fixed-support cycle occurs among the permutations of A.toList;
therefore this is the full finite carrier, for arbitrary ambient labels. -/
theorem fixedCycles_finite (A : Finset α) :
    {C : Cycle α | C.Nodup ∧ C.toFinset = A}.Finite := by
  classical
  let S : Finset (Cycle α) := A.toList.permutations.toFinset.image (fun L : List α => (L : Cycle α))
  apply (Set.toFinite (↑S : Set (Cycle α))).subset
  intro C hC
  change C ∈ S
  induction C using Quotient.inductionOn with
  | _ L =>
    have hn : L.Nodup := Cycle.nodup_coe_iff.mp hC.1
    have hs : L.toFinset = A := hC.2
    have hp : L.Perm A.toList := List.perm_of_nodup_nodup_toFinset_eq
      hn A.nodup_toList (by simpa using hs)
    exact Finset.mem_image.mpr ⟨L, by simpa using List.mem_permutations.mpr hp, rfl⟩

/-- Every finite support has an actual legal original. -/
theorem fixedCycles_nonempty (A : Finset α) : Nonempty (FixedCycles A) := by
  refine ⟨⟨(A.toList : Cycle α), ?_⟩⟩
  constructor
  · exact Cycle.nodup_coe_iff.mpr A.nodup_toList
  · simp

noncomputable instance fixedCyclesFintype (A : Finset α) : Fintype (FixedCycles A) :=
  (fixedCycles_finite A).fintype

/-- Signed mass of one output fibre. Output values need no chosen real encoding. -/
noncomputable def pushforward {ι : Type v} [Fintype ι] {Y : Type*}
    (f : ι → Y) (w : ι → ℝ) (y : Y) : ℝ := by
  classical
  exact ∑ i ∈ Finset.univ.filter (fun i => f i = y), w i

private theorem singleton_mass {ι : Type v} [Fintype ι] {Y : Type*}
    (f : ι → Y) (w : ι → ℝ) (i : ι)
    (hs : ∀ j, f j = f i → j = i) : pushforward f w (f i) = w i := by
  classical
  have he : Finset.univ.filter (fun j => f j = f i) = {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨hs j, fun h => h ▸ rfl⟩
  simp only [pushforward, he, Finset.sum_singleton]

/-- For any finite injectively realized family of legal cycles, the two separate
paired laws have zero common signed kernel. No adjacency, forest or desired
injectivity conclusion is a hypothesis. Families may omit swap partners. -/
theorem signed_kernel {ι : Type v} [Fintype ι]
    {A : Finset α} (hA : 4 ≤ A.card)
    {a b c : α} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (X : ι → Cycle α) (hi : Function.Injective X)
    (hn : ∀ i, (X i).Nodup) (hs : ∀ i, (X i).toFinset = A)
    (w : ι → ℝ)
    (hF : ∀ y, pushforward (fun i => paired a b (X i)) w y = 0)
    (hG : ∀ y, pushforward (fun i => paired b c (X i)) w y = 0) :
    w = 0 := by
  classical
  let F := fun i => paired a b (X i)
  let G := fun i => paired b c (X i)
  have hleaf (i j k : ι) (hij : F j = F i) (hne : j ≠ i)
      (hik : G k = G i) (hk : k ≠ i) : ∀ l, G l = G j → l = j := by
    intro l hl
    by_contra hlj
    exact swap_has_leaf hA ha hb hc hab hbc hac
      (hn i) (hn j) (hn k) (hn l) (hs i) (hs j) (hs k) (hs l)
      hij.symm (fun h => hne (hi h)) hik.symm (fun h => hk (hi h))
      hl.symm (fun h => hlj (hi h))
  funext i
  change w i = 0
  by_cases hfi : ∀ j, F j = F i → j = i
  · exact (singleton_mass F w i hfi).symm.trans (hF (F i))
  · push_neg at hfi
    obtain ⟨j,hij,hji⟩ := hfi
    by_cases hgi : ∀ k, G k = G i → k = i
    · exact (singleton_mass G w i hgi).symm.trans (hG (G i))
    · push_neg at hgi
      obtain ⟨k,hik,hki⟩ := hgi
      have hwj : w j = 0 :=
        (singleton_mass G w j (hleaf i j k hij hji hik hki)).symm.trans (hG (G j))
      have htwo : Finset.univ.filter (fun l => F l = F i) = {i,j} := by
        ext l
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro hl
          by_cases hli : l = i
          · exact Or.inl hli
          · right
            apply hi
            exact pair_fiber_at_most_two (by omega) ha hb hab
              (hn i) (hn l) (hn j) (hs i) (hs l) (hs j)
              (Prod.mk.inj hl.symm) (Prod.mk.inj hij.symm)
              (fun h => hli (hi h)) (fun h => hji (hi h))
        · rintro (rfl | rfl)
          · rfl
          · exact hij
      have he := hF (F i)
      simp only [pushforward] at he
      change (∑ l ∈ Finset.univ.filter (fun l => F l = F i), w l) = 0 at he
      rw [htwo] at he
      simpa [Finset.sum_pair (Ne.symm hji), hwj] using he

/-- The two paired pushforwards identify all real signed weights on a finite
legal realization, hence in particular all probability weights. -/
theorem signed_injective {ι : Type v} [Fintype ι]
    {A : Finset α} (hA : 4 ≤ A.card)
    {a b c : α} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (X : ι → Cycle α) (hi : Function.Injective X)
    (hn : ∀ i, (X i).Nodup) (hs : ∀ i, (X i).toFinset = A)
    (μ ν : ι → ℝ)
    (hF : pushforward (fun i => paired a b (X i)) μ =
      pushforward (fun i => paired a b (X i)) ν)
    (hG : pushforward (fun i => paired b c (X i)) μ =
      pushforward (fun i => paired b c (X i)) ν) : μ = ν := by
  have hz := signed_kernel hA ha hb hc hab hbc hac X hi hn hs (μ - ν)
    (fun y => by
      have he := congrFun hF y
      simpa only [pushforward, Pi.sub_apply, Finset.sum_sub_distrib, sub_eq_zero] using he)
    (fun y => by
      have he := congrFun hG y
      simpa only [pushforward, Pi.sub_apply, Finset.sum_sub_distrib, sub_eq_zero] using he)
  exact sub_eq_zero.mp hz

/-- Full fixed-support law injectivity, without restricting the law to a chosen
subfamily. The Fintype instance enumerates every legal oriented cycle. -/
theorem full_signed_injective {A : Finset α} (hA : 4 ≤ A.card)
    {a b c : α} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (μ ν : FixedCycles A → ℝ)
    (hF : pushforward (fun C : FixedCycles A => paired a b C.val) μ =
      pushforward (fun C : FixedCycles A => paired a b C.val) ν)
    (hG : pushforward (fun C : FixedCycles A => paired b c C.val) μ =
      pushforward (fun C : FixedCycles A => paired b c C.val) ν) : μ = ν := by
  exact signed_injective hA ha hb hc hab hbc hac Subtype.val Subtype.val_injective
    (fun C => C.prop.1) (fun C => C.prop.2) μ ν hF hG

/-- Probability-law specialization with nonnegativity and total mass one. -/
theorem full_probability_injective {A : Finset α} (hA : 4 ≤ A.card)
    {a b c : α} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (μ ν : FixedCycles A → ℝ)
    (_hμ : (∀ C, 0 ≤ μ C) ∧ ∑ C, μ C = 1)
    (_hν : (∀ C, 0 ≤ ν C) ∧ ∑ C, ν C = 1)
    (hF : pushforward (fun C : FixedCycles A => paired a b C.val) μ =
      pushforward (fun C : FixedCycles A => paired a b C.val) ν)
    (hG : pushforward (fun C : FixedCycles A => paired b c C.val) μ =
      pushforward (fun C : FixedCycles A => paired b c C.val) ν) : μ = ν := by
  exact full_signed_injective hA ha hb hc hab hbc hac μ ν hF hG

end D5.S3.Combinatorics.CircularWords.PairedDeletionLaw

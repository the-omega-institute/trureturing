/- GID: D5/S3/Combinatorics/Graph/Walks/HamiltonConnected
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/HamiltonConnected
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Hamiltonian]
   utility: none
   digest: Fixed-endpoint path surgery for the Chvatal-Erdos Hamilton-connectedness criterion. -/
import D5.S3.Combinatorics.Graph.Walks.ConnectivityFan
import D5.S3.Combinatorics.Graph.Walks.OrderedTwoCutSlicing
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

/-! Fixed-endpoint path surgery and the strict Chvatal-Erdos criterion. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.HamiltonConnected

open SimpleGraph OrderedTwoCutSlicing
open scoped Classical
universe u
variable {V : Type u} {G : SimpleGraph V}

private lemma append_path {a b c : V} (p : G.Walk a b) (q : G.Walk b c)
    (hp : p.IsPath) (hq : q.IsPath)
    (hmeet : ∀ z ∈ p.support, z ∈ q.support → z = b) :
    (p.append q).IsPath := by
  rw [Walk.isPath_def, Walk.support_append, List.nodup_append]
  refine ⟨hp.support_nodup, hq.support_nodup.sublist (List.tail_sublist _), ?_⟩
  intro z hz w hw heq
  subst heq
  have hz' := hmeet z hz (List.mem_of_mem_tail hw)
  subst hz'
  have hn := hq.support_nodup
  rw [← Walk.cons_tail_support] at hn
  exact (List.nodup_cons.mp hn).1 hw

/-- The two cuts retain their literal prescribed endpoints, including adjacent cuts. -/
private lemma two_cut_extension
    {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    {i j : ℕ} (hij : i < j) (hj : j < p.length)
    (d : G.Walk (p.getVert i) (p.getVert j)) (hd : d.IsPath)
    (hclean : ∀ z ∈ d.support, z ∈ p.support →
      z = p.getVert i ∨ z = p.getVert j)
    (he : G.Adj (p.getVert (i + 1)) (p.getVert (j + 1))) :
    ∃ q : G.Walk a b, q.IsPath ∧ q.length = p.length + d.length - 1 := by
  obtain ⟨q₀,q₁,q₂,h₀,h₁,h₂,hs,_,_,hl₀,hl₁,hl₂⟩ :=
    exists_path_slicing_at_two_ordered_edges p hp hij hj rfl rfl rfl rfl
  have hn : (q₀.support ++ q₁.support ++ q₂.support).Nodup := hs.symm ▸ hp.support_nodup
  have h01 : ∀ {z w}, z ∈ q₀.support → w ∈ q₁.support → z ≠ w := by
    intro z w hz hw
    exact (List.nodup_append.mp (List.nodup_append.mp hn).1).2.2 z hz w hw
  have h02 : ∀ {z w}, z ∈ q₀.support → w ∈ q₂.support → z ≠ w := by
    intro z w hz hw
    exact (List.nodup_append.mp hn).2.2 z
      (List.mem_append.mpr (Or.inl hz)) w hw
  have h12 : ∀ {z w}, z ∈ q₁.support → w ∈ q₂.support → z ≠ w := by
    intro z w hz hw
    exact (List.nodup_append.mp hn).2.2 z
      (List.mem_append.mpr (Or.inr hz)) w hw
  have hmem₀ : ∀ z ∈ q₀.support, z ∈ p.support := by
    intro z hz; rw [← hs]; exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hz)))
  have hmem₁ : ∀ z ∈ q₁.support, z ∈ p.support := by
    intro z hz; rw [← hs]; exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hz)))
  have hmem₂ : ∀ z ∈ q₂.support, z ∈ p.support := by
    intro z hz; rw [← hs]; exact List.mem_append.mpr (Or.inr hz)
  have hr : (q₁.reverse.append (Walk.cons he q₂)).IsPath := by
    apply append_path _ _ h₁.reverse
    · rw [Walk.cons_isPath_iff]
      exact ⟨h₂, fun hz => h12 q₁.start_mem_support hz rfl⟩
    · intro z hz hz'
      rw [Walk.support_reverse, List.mem_reverse] at hz
      rw [Walk.support_cons, List.mem_cons] at hz'
      exact hz'.resolve_right (fun hm => h12 hz hm rfl)
  have hdr : (d.append (q₁.reverse.append (Walk.cons he q₂))).IsPath := by
    apply append_path _ _ hd hr
    intro z hz hz'
    rw [Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse,
      Walk.support_cons, List.mem_cons] at hz'
    have hzp : z ∈ p.support := by
      rcases hz' with hm | rfl | hm
      · exact hmem₁ z hm
      · exact hmem₁ _ q₁.start_mem_support
      · exact hmem₂ z hm
    rcases hclean z hz hzp with heq | heq
    · subst heq
      rcases hz' with hm | heq | hm
      · exact (h01 q₀.end_mem_support hm rfl).elim
      · exact (h01 q₀.end_mem_support q₁.start_mem_support heq).elim
      · exact (h02 q₀.end_mem_support hm rfl).elim
    · exact heq
  let q := q₀.append (d.append (q₁.reverse.append (Walk.cons he q₂)))
  have hq : q.IsPath := by
    apply append_path _ _ h₀ hdr
    intro z hz hz'
    rw [Walk.mem_support_append_iff, Walk.mem_support_append_iff,
      Walk.support_reverse, List.mem_reverse, Walk.support_cons, List.mem_cons] at hz'
    rcases hz' with hm | hm | heq | hm
    · rcases hclean z hm (hmem₀ z hz) with heq | heq
      · exact heq
      · subst heq; exact (h01 hz q₁.end_mem_support rfl).elim
    · exact (h01 hz hm rfl).elim
    · subst heq; exact (h01 hz q₁.start_mem_support rfl).elim
    · exact (h02 hz hm rfl).elim
  refine ⟨q,hq,?_⟩
  simp only [q, Walk.length_append, Walk.length_reverse, Walk.length_cons]
  omega

private lemma one_cut_extension
    {a b : V} (p : G.Walk a b) (hp : p.IsPath) {i : ℕ} (hi : i < p.length)
    (d : G.Walk (p.getVert i) (p.getVert (i + 1))) (hd : d.IsPath)
    (hclean : ∀ z ∈ d.support, z ∈ p.support →
      z = p.getVert i ∨ z = p.getVert (i + 1)) :
    ∃ q : G.Walk a b, q.IsPath ∧ q.length = p.length + d.length - 1 := by
  let l := p.take i
  let r := p.drop (i + 1)
  have hs : l.support ++ r.support = p.support := by
    simp only [l,r,Walk.support_take,Walk.drop_support_eq_support_drop_min,
      Nat.min_eq_left (by omega : i+1 ≤ p.length)]
    exact List.take_append_drop (i + 1) p.support
  have hdis : ∀ {z w}, z ∈ l.support → w ∈ r.support → z ≠ w := by
    intro z w hz hw
    exact (List.nodup_append.mp (hs.symm ▸ hp.support_nodup)).2.2 z hz w hw
  have hlmem : ∀ z ∈ l.support, z ∈ p.support := by
    intro z hz; rw [← hs]; exact List.mem_append.mpr (Or.inl hz)
  have hrmem : ∀ z ∈ r.support, z ∈ p.support := by
    intro z hz; rw [← hs]; exact List.mem_append.mpr (Or.inr hz)
  have hdr : (d.append r).IsPath := by
    apply append_path _ _ hd (hp.drop _)
    intro z hz hz'
    rcases hclean z hz (hrmem z hz') with heq | heq
    · subst heq; exact (hdis l.end_mem_support hz' rfl).elim
    · exact heq
  have hq : (l.append (d.append r)).IsPath := by
    apply append_path _ _ (hp.take _) hdr
    intro z hz hz'
    rw [Walk.mem_support_append_iff] at hz'
    rcases hz' with hm | hm
    · rcases hclean z hm (hlmem z hz) with heq | heq
      · exact heq
      · subst heq; exact (hdis hz r.start_mem_support rfl).elim
    · exact (hdis hz hm rfl).elim
  refine ⟨l.append (d.append r),hq,?_⟩
  simp only [l,r,Walk.length_append,Walk.take_length,Walk.drop_length,
    Nat.min_eq_left (Nat.le_of_lt hi)]
  omega

private lemma fan_detour {a b x : V} (p : G.Walk a b)
    {r : ℕ} (endpoint : Fin r → V) (arms : ∀ t, G.Walk x (endpoint t))
    (ha : ∀ t, (arms t).IsPath ∧ ∀ z ∈ (arms t).support,
      z ∈ p.support → z = endpoint t)
    (hx : x ∉ p.support)
    (ht : ∀ t, endpoint t ∈ p.support)
    (hm : ∀ t s, t ≠ s → ∀ z ∈ (arms t).support,
      z ∈ (arms s).support → z = x)
    {t s : Fin r} (hne : t ≠ s) :
    ((arms t).reverse.append (arms s)).IsPath ∧
    2 ≤ ((arms t).reverse.append (arms s)).length ∧
    (∀ z ∈ ((arms t).reverse.append (arms s)).support, z ∈ p.support →
      z = endpoint t ∨ z = endpoint s) := by
  refine ⟨?_,?_,?_⟩
  · apply append_path _ _ (ha t).1.reverse (ha s).1
    intro z hz hz'
    exact hm t s hne z (by simpa only [Walk.support_reverse, List.mem_reverse] using hz) hz'
  · have hlen : ∀ t, 1 ≤ (arms t).length := by
      intro t
      by_contra hn
      have heq := Walk.eq_of_length_eq_zero (by omega : (arms t).length = 0)
      exact hx (heq ▸ ht t)
    simp only [Walk.length_append,Walk.length_reverse]
    have := hlen t; have := hlen s; omega
  · intro z hz hzp
    rw [Walk.mem_support_append_iff,Walk.support_reverse,List.mem_reverse] at hz
    exact hz.elim (fun h => Or.inl ((ha t).2 z h hzp))
      (fun h => Or.inr ((ha s).2 z h hzp))

/-- A maximal path with fixed distinct endpoints obstructs a clean external fan. -/
private lemma maximal_path_fan_obstruction [DecidableEq V]
    {a b x : V} (p : G.Walk a b) (hp : p.IsPath) (hab : a ≠ b)
    (hmax : ∀ q : G.Walk a b, q.IsPath → q.length ≤ p.length)
    (hx : x ∉ p.support) {r : ℕ}
    (endpoint : Fin r → V) (arms : ∀ t, G.Walk x (endpoint t))
    (ht : ∀ t, endpoint t ∈ p.support)
    (ha : ∀ t, (arms t).IsPath ∧ ∀ z ∈ (arms t).support,
      z ∈ p.support → z = endpoint t)
    (hm : ∀ t s, t ≠ s → ∀ z ∈ (arms t).support,
      z ∈ (arms s).support → z = x)
    (hinj : Function.Injective endpoint) :
    r < p.support.toFinset.card ∧
    ∃ I : Set V, x ∈ I ∧ G.IsIndepSet I ∧ r ≤ I.ncard := by
  classical
  have hplen : 1 ≤ p.length := by
    by_contra hn
    exact hab (Walk.eq_of_length_eq_zero (p := p) (by omega))
  have hlong : ∀ {i}, i < p.length →
      ∀ d : G.Walk (p.getVert i) (p.getVert (i + 1)), d.IsPath → 2 ≤ d.length →
      (∀ z ∈ d.support, z ∈ p.support →
        z = p.getVert i ∨ z = p.getVert (i + 1)) → False := by
    intro i hi d hd hl hc
    obtain ⟨q,hq,hql⟩ := one_cut_extension p hp hi d hd hc
    have := hmax q hq
    omega
  have hunsaturated : r < p.support.toFinset.card := by
    by_contra hn
    have hcover : Finset.univ.image endpoint = p.support.toFinset := by
      apply Finset.eq_of_subset_of_card_le
      · intro z hz
        obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hz
        simpa using ht t
      · rw [Finset.card_image_of_injective _ hinj,Finset.card_univ,Fintype.card_fin]
        omega
    obtain ⟨t,_,ht₀⟩ := Finset.mem_image.mp
      (show p.getVert 0 ∈ Finset.univ.image endpoint by
        rw [hcover]; simpa using p.getVert_mem_support 0)
    obtain ⟨s,_,hs₀⟩ := Finset.mem_image.mp
      (show p.getVert 1 ∈ Finset.univ.image endpoint by
        rw [hcover]; simpa using p.getVert_mem_support 1)
    have hts : t ≠ s := by
      intro heq
      have hv := ht₀.symm.trans (heq ▸ hs₀)
      exact (p.adj_getVert_succ (by omega : 0 < p.length)).ne hv
    have hd := fan_detour p endpoint arms ha hx ht hm hts
    let d := ((arms t).reverse.append (arms s)).copy ht₀ hs₀
    apply hlong (by omega : 0 < p.length) d
    · simpa only [d,Walk.isPath_copy] using hd.1
    · simpa only [d,Walk.length_copy] using hd.2.1
    · intro z hz hzp
      simpa only [ht₀,hs₀] using hd.2.2 z (by simpa only [d,Walk.support_copy] using hz) hzp
  refine ⟨hunsaturated,?_⟩
  let J := {t : Fin r // endpoint t ≠ b}
  let pos : J → ℕ := fun t => Classical.choose
    (Walk.mem_support_iff_exists_getVert.mp (ht t.val))
  have hpos : ∀ t : J, p.getVert (pos t) = endpoint t.val ∧ pos t ≤ p.length :=
    fun t => Classical.choose_spec (Walk.mem_support_iff_exists_getVert.mp (ht t.val))
  have hstrict : ∀ t : J, pos t < p.length := by
    intro t
    have hle := (hpos t).2
    by_contra hn
    have heq : pos t = p.length := by omega
    exact t.property ((hpos t).1.symm.trans (by rw [heq,Walk.getVert_length]))
  let next : J → V := fun t => p.getVert (pos t + 1)
  have hnextmem : ∀ t, next t ∈ p.support := fun t => p.getVert_mem_support _
  have hnextadj : ∀ t, G.Adj (endpoint t.val) (next t) := by
    intro t
    rw [← (hpos t).1]
    exact p.adj_getVert_succ (hstrict t)
  have hnextinj : Function.Injective next := by
    intro t s heq
    have heq' := hp.getVert_injOn (by have := hstrict t; simp only [Set.mem_ofPred_eq]; omega)
      (by have := hstrict s; simp only [Set.mem_ofPred_eq]; omega) heq
    apply Subtype.ext
    apply hinj
    rw [← (hpos t).1,← (hpos s).1]
    congr 1
    omega
  have hxnext : ∀ t, ¬ G.Adj x (next t) := by
    intro t hadj
    have hmissing : next t ∉ (arms t.val).reverse.support := by
      intro hz
      have heq := (ha t.val).2 _ (by simpa only [Walk.support_reverse,List.mem_reverse] using hz)
        (hnextmem t)
      exact (hnextadj t).ne heq.symm
    let d := ((arms t.val).reverse.concat hadj).copy (hpos t).1.symm rfl
    apply hlong (hstrict t) d
    · simpa only [d,Walk.isPath_copy] using (ha t.val).1.reverse.concat hmissing hadj
    · have hlen : 1 ≤ (arms t.val).length := by
        by_contra hn
        exact hx (Walk.eq_of_length_eq_zero (by omega : (arms t.val).length = 0) ▸ ht t.val)
      simp only [d,Walk.length_copy,Walk.length_concat,Walk.length_reverse]
      omega
    · intro z hz hzp
      simp only [d,Walk.support_copy,Walk.support_concat,Walk.support_reverse,
        List.mem_append,List.mem_reverse,List.mem_singleton] at hz
      rcases hz with hz | rfl
      · exact Or.inl ((ha t.val).2 z hz hzp |>.trans (hpos t).1.symm)
      · exact Or.inr rfl
  have hpair_ordered : ∀ t s : J, pos t < pos s → ¬ G.Adj (next t) (next s) := by
    intro t s hts hadj
    have hne : t.val ≠ s.val := by
      intro heq
      have hv : p.getVert (pos t) = p.getVert (pos s) :=
        (hpos t).1.trans (heq ▸ (hpos s).1.symm)
      have := hp.getVert_injOn (hpos t).2 (hpos s).2 hv
      omega
    have hd := fan_detour p endpoint arms ha hx ht hm hne
    let d := ((arms t.val).reverse.append (arms s.val)).copy (hpos t).1.symm (hpos s).1.symm
    obtain ⟨q,hq,hql⟩ := two_cut_extension p hp hts (hstrict s) d
      (by simpa only [d,Walk.isPath_copy] using hd.1) (by
        intro z hz hzp
        simpa only [(hpos t).1,(hpos s).1] using
          hd.2.2 z (by simpa only [d,Walk.support_copy] using hz) hzp) hadj
    have hl : 2 ≤ d.length := by simpa only [d,Walk.length_copy] using hd.2.1
    have := hmax q hq
    omega
  have hpair : ∀ t s : J, t ≠ s → ¬ G.Adj (next t) (next s) := by
    intro t s hne hadj
    have hposne : pos t ≠ pos s := by
      intro heq
      apply hne
      apply Subtype.ext
      apply hinj
      exact (hpos t).1.symm.trans (heq ▸ (hpos s).1)
    rcases lt_or_gt_of_ne hposne with hlt | hgt
    · exact hpair_ordered t s hlt hadj
    · exact hpair_ordered s t hgt hadj.symm
  let f : Fin r → Option J := fun t => if h : endpoint t ≠ b then some ⟨t,h⟩ else none
  have hf : Function.Injective f := by
    intro t s heq
    by_cases ht' : endpoint t ≠ b <;> by_cases hs' : endpoint s ≠ b
    · have heq' : (⟨t,ht'⟩ : J) = ⟨s,hs'⟩ := by
        simpa only [f,dite_eq_left ht',dite_eq_left hs',Option.some.injEq] using heq
      exact congrArg Subtype.val heq' 
    · simp [f,ht',hs'] at heq
    · simp [f,ht',hs'] at heq
    · exact hinj ((not_ne_iff.mp ht').trans (not_ne_iff.mp hs').symm)
  have hcount := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin,Fintype.card_option] at hcount
  let I := insert x (Finset.univ.image next)
  have hcard : I.card = Fintype.card J + 1 := by
    rw [Finset.card_insert_of_notMem,Finset.card_image_of_injective _ hnextinj,
      Finset.card_univ]
    intro hz
    obtain ⟨t,_,heq⟩ := Finset.mem_image.mp hz
    exact hx (heq ▸ hnextmem t)
  refine ⟨(I : Set V),by simp [I],?_,?_⟩
  · intro z hz w hw hne hadj
    simp only [I,Finset.coe_insert,Finset.coe_image,Finset.coe_univ,
      Set.image_univ,Set.mem_insert_iff,Set.mem_range] at hz hw
    rcases hz with rfl | ⟨t,rfl⟩ <;> rcases hw with rfl | ⟨s,rfl⟩
    · exact hne rfl
    · exact hxnext s hadj
    · exact hxnext t hadj.symm
    · exact hpair t s (fun heq => hne (heq ▸ rfl)) hadj
  · rw [Set.ncard_coe_finset,hcard]
    exact hcount

/-- Chvatal-Erdos, Theorem 3: strict independence threshold gives Hamiltonian
paths between every prescribed pair of distinct vertices, for all finite orders. -/
theorem exists_isHamiltonian_of_connectivity_independence [Finite V]
    (G : SimpleGraph V) (k : ℕ)
    (hconn : ∀ S : Set V, S.ncard < k → (G.induce Sᶜ).Connected)
    (hindependence : ∀ S : Set V, G.IsIndepSet S → S.ncard < k) :
    ∀ a b : V, a ≠ b → ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  letI := Fintype.ofFinite V
  intro a b hab
  have hk : 0 < k := by
    simpa using hindependence ∅ (by simp)
  obtain ⟨walk⟩ := (hconn ∅ (by simpa using hk)).preconnected
    ⟨a,by simp⟩ ⟨b,by simp⟩
  let initial : G.Walk a b :=
    (walk.map (Embedding.induce (∅ : Set V)ᶜ).toHom).bypass
  have hinitial : initial.IsPath := Walk.bypass_isPath _
  let lengths : Set ℕ := {n | ∃ p : G.Walk a b, p.IsPath ∧ p.length = n}
  have hfinite : lengths.Finite := Set.Finite.subset (Set.finite_le_nat (Fintype.card V))
    (by rintro n ⟨p,hp,rfl⟩; exact hp.length_lt.le)
  obtain ⟨_,⟨⟨p,hp,rfl⟩,hmax⟩⟩ :=
    hfinite.exists_maximal ⟨initial.length,initial,hinitial,rfl⟩
  have hmax' : ∀ q : G.Walk a b, q.IsPath → q.length ≤ p.length := by
    intro q hq
    have := hmax ⟨q,hq,rfl⟩
    omega
  refine ⟨p,hp.isHamiltonian_of_mem ?_⟩
  intro x
  by_contra hx
  obtain ⟨endpoint,arms,ha,hm,hinj⟩ := ConnectivityFan.exists_fan hconn
    p.support.toFinset (by simpa using hx)
  obtain ⟨hsmall,I,_,hI,hcard⟩ := maximal_path_fan_obstruction p hp hab hmax' hx endpoint arms
    (fun t => by simpa using (ha t).1)
    (fun t => ⟨(ha t).2.1,fun z hz hzp => (ha t).2.2 z hz (by simpa using hzp)⟩)
    hm hinj
  have hsat : min k p.support.toFinset.card = k := by omega
  have hbound := hindependence I hI
  omega

#print axioms maximal_path_fan_obstruction
#print axioms exists_isHamiltonian_of_connectivity_independence

end D5.S3.Combinatorics.Graph.Walks.HamiltonConnected

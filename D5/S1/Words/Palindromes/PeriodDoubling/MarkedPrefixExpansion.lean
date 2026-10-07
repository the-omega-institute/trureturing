/- GID: D5/S1/Words/Palindromes/PeriodDoubling/MarkedPrefixExpansion
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/MarkedPrefixExpansion
   mirror-E: none(waiver:literal-marked-stream-construction)
   anchors: []
   utility: none
   digest: A literal separated marked prefix determines every sufficiently padded signed stream. -/

/-
proof_shape: content (marked_prefix_expansion)
escape_witness: Constructing the sparse marked expansion identifies the full stream and its tail.
admission_basis: escape-witness
Direct frozen dependencies: none; imported period-doubling modules are delivered together.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.PeriodDoubling.MarkedPrefixArithmetic
import D5.S1.Words.Palindromes.PeriodDoubling.CanonicalSignedDigits
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
namespace D5.S1.Words.Palindromes.PeriodDoubling
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem marked_prefix_expansion (n m p : ℕ) (T : ℤ)
    (h : markedPrefix n m p T) (ds : List ℤ)
    (hc : ∀ z ∈ ds, z=-1 ∨ z=0 ∨ z=1)
    (hs : ds.IsChain (fun a b => a=0 ∨ b=0))
    (hv : ds.foldr (fun z x => z+2*x) 0=2*(((n+1)/2 : ℕ) : ℤ))
    (hlen : p+3*m+2≤ds.length) :
    ∃ (lower : List ℤ) (k : ℕ), lower.length=p+1 ∧
      lower.foldr (fun z x => z+2*x) 0=2*T ∧
      (∀ i : ℕ, lower[i]?.getD 0≠0 → i+2≤p) ∧
      ds=lower++(List.replicate m [1,0,0]).flatten++List.replicate (k+1) 0 ∧
      ([0,0]++lower).reverse[0]?.getD 0=0 ∧
      ([0,0]++lower).reverse[1]?.getD 0=0 := by
  obtain ⟨hvalue,tail,ht,hct,hst,hpt⟩:=h
  let low : List ℤ := List.ofFn (fun i : Fin p => tail[i.val]?.getD 0)
  have llen : low.length=p := by simp [low]
  have entry (i : ℕ) : low[i]?.getD 0=tail[i]?.getD 0 := by
    by_cases hi : i<p
    · simp [low,hi]
    · have hz : tail[i]?.getD 0=0 := by
        by_contra hn
        have hh:=hpt i hn;omega
      simp [low,hi,hz]
  have lc : ∀ z ∈ low, z=-1 ∨ z=0 ∨ z=1 := by
    intro z hz
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hz
    by_cases hi : i.val<tail.length
    · rw [List.getElem?_eq_getElem hi,Option.getD_some]
      exact hct _ (List.getElem_mem hi)
    · simp [List.getElem?_eq_none (by omega : tail.length≤i.val)]
  have lp : ∀ i : ℕ, low[i]?.getD 0≠0 → i+3≤p := by
    intro i hi;exact hpt i (by simpa only [entry] using hi)
  have ls : low.IsChain (fun a b => a=0 ∨ b=0) := by
    rw [List.isChain_iff_getElem]
    intro i hi
    have hi' : i<p := by omega
    have hj' : i+1<p := by omega
    have a : low[i]=tail[i]?.getD 0 := by simpa only [List.getElem?_eq_getElem (by omega : i<low.length),Option.getD_some] using entry i
    have b : low[i+1]=tail[i+1]?.getD 0 := by simpa only [List.getElem?_eq_getElem (by omega : i+1<low.length),Option.getD_some] using entry (i+1)
    rw [a,b]
    by_cases ht' : i+1<tail.length
    · have hh:=List.isChain_iff_getElem.mp hst i ht'
      simpa only [List.getElem?_eq_getElem (by omega : i<tail.length),
        List.getElem?_eq_getElem ht',Option.getD_some] using hh
    · exact Or.inr (by simp [List.getElem?_eq_none (by omega : tail.length≤i+1)])
  have lv : low.foldr (fun z x => z+2*x) 0=T := by
    have extvalue (xs ys : List ℤ) (he : ∀ i : ℕ, xs[i]?.getD 0=ys[i]?.getD 0) :
        xs.foldr (fun z x => z+2*x) 0=ys.foldr (fun z x => z+2*x) 0 := by
      induction xs generalizing ys with
      | nil =>
        have hz : ∀ z ∈ ys,z=0 := by
          intro z hz
          obtain ⟨i,hi,he'⟩:=List.mem_iff_getElem.mp hz
          have hh:=he i
          simpa [List.getElem?_eq_getElem hi,he'] using hh.symm
        induction ys with
        | nil => rfl
        | cons y ys ih =>
          have hy:=hz y (by simp)
          simp only [List.foldr_nil,List.foldr_cons,hy,zero_add]
          rw [← ih (fun i => by simpa using he (i+1)) (fun z hz' => hz z (by simp [hz']))]
          simp
      | cons x xs ih =>
        cases ys with
        | nil =>
          have hx:=he 0
          have htail:=ih [] (fun i => by simpa using he (i+1))
          simp only [List.foldr_cons,List.foldr_nil]
          simp at hx;rw [hx,htail];simp
        | cons y ys =>
          have hh : x=y := by simpa using he 0
          have htail:=ih ys (fun i => by simpa using he (i+1))
          simp only [List.foldr_cons,hh,htail]
    exact (extvalue low tail entry).trans ht
  have seed (xs : List ℤ) (v : ℤ) :
      xs.foldr (fun z x => z+2*x) v = xs.foldr (fun z x => z+2*x) 0+2^xs.length*v := by
    induction xs with
    | nil => simp
    | cons x xs ih => simp only [List.foldr_cons,List.length_cons,pow_succ,ih];ring
  have zero (k : ℕ) : (List.replicate k (0:ℤ)).foldr (fun z x => z+2*x) 0=0 := by
    induction k with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ,ih]
  have blockval (m : ℕ) : ((List.replicate m ([1,0,0] : List ℤ)).flatten).foldr
      (fun z x => z+2*x) 0=(markedPowers m 0 : ℤ) := by
    induction m with
    | zero => simp [markedPowers]
    | succ m ih =>
      have recurrence : markedPowers (m+1) 0=8*markedPowers m 0+1 := by
        unfold markedPowers
        rw [Finset.sum_range_succ']
        simp only [Nat.zero_add,Nat.mul_add,Nat.mul_one,pow_add]
        simp only [show (2:ℕ)^3=8 by decide,← Finset.sum_mul]
        ring
      simp only [List.replicate_succ,List.flatten_cons,List.cons_append,List.nil_append,List.foldr_cons,ih,recurrence]
      push_cast;ring
  have scale : markedPowers m p=2^p*markedPowers m 0 := by
    simp only [markedPowers,Nat.zero_add,pow_add,Finset.mul_sum]
  let k := ds.length-(p+3*m+2)
  let lower := (0:ℤ)::low
  let blocks : List ℤ := (List.replicate m [1,0,0]).flatten
  let candidate := lower++blocks++List.replicate (k+1) 0
  have cl : candidate.length=ds.length := by
    simp [candidate,lower,blocks,List.length_flatten,List.map_replicate,llen,k]
    omega
  have bc : ∀ z ∈ blocks,z=-1 ∨ z=0 ∨ z=1 := by
    intro z hz
    simp only [blocks,List.mem_flatten,List.mem_replicate] at hz
    obtain ⟨l,⟨_,rfl⟩,hz⟩:=hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl <;> simp
  have blocks_sparse (r : ℕ) : ((List.replicate r ([1,0,0] : List ℤ)).flatten).IsChain
      (fun a b => a=0 ∨ b=0) := by
    induction r with
    | zero => simp
    | succ r ih =>
      simp only [List.replicate_succ,List.flatten_cons,List.cons_append,List.nil_append]
      apply List.isChain_cons_cons.mpr
      refine ⟨Or.inr rfl,List.isChain_cons_cons.mpr ⟨Or.inl rfl,?_⟩⟩
      cases r with
      | zero => simp
      | succ r =>
        simpa [List.replicate_succ,List.flatten_cons]
          using (List.isChain_cons_cons.mpr ⟨Or.inl rfl,ih⟩ :
            ((0:ℤ)::(List.replicate (r+1) [1,0,0]).flatten).IsChain (fun a b => a=0 ∨ b=0))
  have bs : blocks.IsChain (fun a b => a=0 ∨ b=0) := blocks_sparse m
  have lowerc : ∀ z ∈ lower,z=-1 ∨ z=0 ∨ z=1 := by
    intro z hz;rcases List.mem_cons.mp hz with rfl|hz
    · simp
    · exact lc z hz
  have lowers : lower.IsChain (fun a b => a=0 ∨ b=0) := by
    dsimp [lower]
    cases hlow : low with
    | nil => simp
    | cons d es => exact List.isChain_cons_cons.mpr ⟨Or.inl rfl,by simpa only [hlow] using ls⟩
  have lowerp : ∀ i : ℕ, lower[i]?.getD 0≠0 → i+2≤p := by
    intro i hi;cases i with
    | zero => simp [lower] at hi
    | succ i => have hh:=lp i (by simpa [lower] using hi);omega
  have lastzero : lower.getLast?.getD 0=0 := by
    rw [List.getLast?_eq_getElem?]
    by_contra hn
    have hh:=lowerp (lower.length-1) hn
    simp only [lower,List.length_cons,llen] at hh
    omega
  have mids : (lower++blocks).IsChain (fun a b => a=0 ∨ b=0) := by
    apply List.IsChain.append lowers bs
    intro a ha b hb
    have hh:=congrArg (fun o : Option ℤ => o.getD 0) (show lower.getLast?=some a from ha)
    have h : a=0 := by simpa only [Option.getD_some,lastzero] using hh.symm
    exact Or.inl h
  have cs : candidate.IsChain (fun a b => a=0 ∨ b=0) := by
    apply List.IsChain.append mids (List.isChain_replicate_of_rel _ (Or.inl rfl))
    intro a ha b hb
    exact Or.inr (List.mem_replicate.mp (List.mem_of_mem_head? hb)).2
  have cc : ∀ z ∈ candidate,z=-1 ∨ z=0 ∨ z=1 := by
    intro z hz
    rcases List.mem_append.mp hz with hz|hz
    · rcases List.mem_append.mp hz with hz|hz
      · exact lowerc z hz
      · exact bc z hz
    · exact Or.inr (Or.inl (List.mem_replicate.mp hz).2)
  have cv : candidate.foldr (fun z x => z+2*x) 0=2*(((n+1)/2 : ℕ) : ℤ) := by
    dsimp only [candidate]
    rw [List.foldr_append]
    rw [zero,List.foldr_append,seed]
    simp only [lower,List.foldr_cons,zero_add,lv,blocks,blockval,List.length_cons,llen,pow_succ]
    have hh : ((markedPowers m p : ℕ) : ℤ)=(2:ℤ)^p*(markedPowers m 0 : ℤ) := by
      rw [scale];push_cast;rfl
    rw [hvalue,hh];ring
  have gap (i : ℕ) (hi : p<i) : ([0,0]++lower)[i]?.getD 0=0 := by
    cases i with
    | zero => simp [lower]
    | succ i =>
      cases i with
      | zero => simp [lower]
      | succ i =>
        cases i with
        | zero => simp [lower]
        | succ i =>
          change low[i]?.getD 0=0
          by_contra hn
          have hh:=lp i hn;omega
  have hd : ds=candidate := nonadjacent_digits_unique ds candidate hc cc hs cs cl.symm (hv.trans cv.symm)
  refine ⟨lower,k,by simp [lower,llen],by simp [lower,lv],lowerp,hd,?_,?_⟩
  · rw [List.getElem?_reverse (by simp [lower,llen] <;> omega)]
    exact gap _ (by simp [lower,llen] <;> omega)
  · rw [List.getElem?_reverse (by simp [lower,llen] <;> omega)]
    exact gap _ (by simp [lower,llen] <;> omega)
end D5.S1.Words.Palindromes.PeriodDoubling

#print axioms D5.S1.Words.Palindromes.PeriodDoubling.marked_prefix_expansion

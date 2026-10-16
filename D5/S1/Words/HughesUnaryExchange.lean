/- GID: D5/S1/Words/HughesUnaryExchange
   generality: G
   mirror-B: D5/B/S1/Words/HughesUnaryExchange
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unary mass perturbations control every native maximal block exchange. -/

import D5.S1.Words.HughesUnaryInsertion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.HughesUnaryExchange

open D5.S1.Words.HughesBlockExchange
open D5.S1.Words.UnaryGapWords
open D5.S1.Words.HughesUnaryInsertion
open D5.S1.Words.Complexity.ShuffleOrders.Binary.BinaryScheduleOrder

variable {α : Type*}

private theorem occupied_update (e : List Nat) (i k : Nat) :
    occupied e ≤ occupied (e.modify i (· + k)) ∧
      occupied (e.modify i (· + k)) ≤ occupied e + 1 := by
  induction e generalizing i with
  | nil => simp [occupied]
  | cons x e ih =>
    cases i with
    | zero =>
      by_cases hx : 0 < x <;> by_cases hy : 0 < x + k <;>
        simp [occupied, List.countP_cons, hx, hy] <;> omega
    | succ i =>
      have hi := ih i
      simp only [List.modify_succ_cons, occupied, List.countP_cons] at *
      omega

private theorem dropLast_update (e : List Nat) (i k : Nat) :
    occupied e.dropLast ≤ occupied (e.modify i (· + k)).dropLast ∧
      occupied (e.modify i (· + k)).dropLast ≤ occupied e.dropLast + 1 := by
  induction e generalizing i with
  | nil => simp [occupied]
  | cons x e ih =>
    by_cases he : e = []
    · subst e
      cases i <;> simp [occupied]
    · cases i with
      | zero =>
        simp only [List.modify_zero_cons, List.dropLast_cons_of_ne_nil he]
        by_cases hx : 0 < x <;> by_cases hy : 0 < x + k <;>
          simp [occupied, List.countP_cons, hx, hy] <;> omega
      | succ i =>
        have hem : e.modify i (· + k) ≠ [] := by
          intro hz
          have hl := congrArg List.length hz
          simp only [List.length_modify, List.length_nil] at hl
          exact he (List.length_eq_zero_iff.mp hl)
        have hi := ih i
        simp only [List.modify_succ_cons, List.dropLast_cons_of_ne_nil he,
          List.dropLast_cons_of_ne_nil hem, occupied, List.countP_cons] at *
        omega

private theorem internal_update (e : List Nat) (i k : Nat) :
    internalOccupied e ≤ internalOccupied (e.modify i (· + k)) ∧
      internalOccupied (e.modify i (· + k)) ≤ internalOccupied e + 1 := by
  cases e with
  | nil => simp [internalOccupied, occupied]
  | cons x e =>
    cases i with
    | zero => simp [internalOccupied]
    | succ i => simpa [internalOccupied] using dropLast_update e i k


private def other (p : Side) : Side := if p = .first then .second else .first

private theorem erase_projection (a : α) (p : Side) (n : Nat)
    (v X A Y : List α) (P R : List Side)
    (hP : P.length = X.length) (hR : R.length = Y.length)
    (hp : projection p (X ++ A ++ Y) (P ++ List.replicate A.length p ++ R) =
      List.replicate n a)
    (hq : projection (other p) (X ++ A ++ Y)
      (P ++ List.replicate A.length p ++ R) = v) :
    A = List.replicate A.length a ∧ A.length ≤ n ∧
    projection p (X ++ Y) (P ++ R) = List.replicate (n - A.length) a ∧
    projection (other p) (X ++ Y) (P ++ R) = v := by
  rw [projection_append _ (X ++ A) Y _ R (by simp [hP]),
    projection_append _ X A P _ hP.symm, projection_pure] at hp hq
  simp only [↓reduceIte] at hp
  have hne : p ≠ other p := by cases p <;> decide
  simp only [hne, ite_false, List.append_nil] at hq
  have hletters : ∀ x ∈ projection p X P ++ A ++ projection p Y R, x = a := by
    rw [hp]
    intro x hx
    exact (List.mem_replicate.mp hx).2
  have ha : A = List.replicate A.length a := List.eq_replicate_length.mpr (by
    intro x hx
    apply hletters x
    simp [hx])
  have hr : projection p X P ++ projection p Y R =
      List.replicate (projection p X P ++ projection p Y R).length a :=
    List.eq_replicate_length.mpr (by
      intro x hx
      apply hletters x
      rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hx)))
      · exact List.mem_append.mpr (Or.inr hx))
  have hl := congrArg List.length hp
  simp only [List.length_append, List.length_replicate] at hl
  refine ⟨ha, by omega, ?_, ?_⟩
  · rw [projection_append _ X Y P R hP.symm, hr]
    congr 1
    simp only [List.length_append]
    omega
  · rw [projection_append _ X Y P R hP.symm]
    exact hq

private theorem erase_first (a : α) (n : Nat) (v X A Y : List α) (P R : List Side)
    (hP : P.length = X.length) (hR : R.length = Y.length)
    (hM : ValidMask (List.replicate n a) v (X ++ A ++ Y)
      (P ++ List.replicate A.length .first ++ R)) :
    A = List.replicate A.length a ∧ A.length ≤ n ∧
      ValidMask (List.replicate (n - A.length) a) v (X ++ Y) (P ++ R) := by
  obtain ⟨_, hp, hq⟩ := (mask_projections _ _ _ _).mp hM
  obtain ⟨ha, hn, hp', hq'⟩ := erase_projection a .first n v X A Y P R hP hR hp hq
  exact ⟨ha, hn, (mask_projections _ _ _ _).mpr
    ⟨by simp [hP, hR], hp', hq'⟩⟩

private theorem erase_second (a : α) (n : Nat) (u X A Y : List α) (P R : List Side)
    (hP : P.length = X.length) (hR : R.length = Y.length)
    (hM : ValidMask u (List.replicate n a) (X ++ A ++ Y)
      (P ++ List.replicate A.length .second ++ R)) :
    A = List.replicate A.length a ∧ A.length ≤ n ∧
      ValidMask u (List.replicate (n - A.length) a) (X ++ Y) (P ++ R) := by
  obtain ⟨_, hq, hp⟩ := (mask_projections _ _ _ _).mp hM
  obtain ⟨ha, hn, hp', hq'⟩ := erase_projection a .second n u X A Y P R hP hR hp hq
  exact ⟨ha, hn, (mask_projections _ _ _ _).mpr
    ⟨by simp [hP, hR], hq', hp'⟩⟩

private theorem inserted_cut (a : α) (m : Nat) (v X Y : List α) (k : Nat)
    (hv : X ++ Y ∈ Sh (List.replicate m a) v) :
    ∃ d f : Nat, degree (List.replicate m a) v (X ++ Y) = (d : WithTop Nat) ∧
      degree (List.replicate (m + k) a) v (X ++ List.replicate k a ++ Y) =
        (f : WithTop Nat) ∧ d ≤ f ∧ f ≤ d + 1 := by
  obtain ⟨cs,h,ha,hh,rfl⟩ := gap_exists a v
  obtain ⟨e,⟨he,hs,hw⟩,_⟩ := (inserted_gap_iff a m cs h _ ha hh).mp hv
  obtain ⟨hi,hel,hes,hew⟩ := gap_insert a cs h e X Y k ha hh he hw
  have hsum : (e.modify (spine a X).length (· + k)).sum = m + k := by omega
  have hd := (inserted_degree a m cs h e ha hh he hs).2
  have hf := (inserted_degree a (m+k) cs h _ ha hh hel hsum).2
  rw [← hw] at hd
  rw [← hew] at hf
  exact ⟨occupied e, occupied (e.modify (spine a X).length (· + k)), hd, hf,
    (occupied_update e _ k).1, (occupied_update e _ k).2⟩

private theorem reverse_cut (a : α) (n : Nat) (u X Y : List α) (k : Nat)
    (hu : u ≠ []) (hv : X ++ Y ∈ Sh u (List.replicate n a)) :
    ∃ d f : Nat, degree u (List.replicate n a) (X ++ Y) = (d : WithTop Nat) ∧
      degree u (List.replicate (n + k) a) (X ++ List.replicate k a ++ Y) =
        (f : WithTop Nat) ∧ d ≤ f ∧ f ≤ d + 1 := by
  obtain ⟨cs,h,ha,hh,rfl⟩ := gap_exists a u
  obtain ⟨e,⟨he,hs,hw⟩,_⟩ := (reverse_gap_iff a n cs h _ ha hh).mp hv
  obtain ⟨hi,hel,hes,hew⟩ := gap_insert a cs h e X Y k ha hh he hw
  have hsum : (e.modify (spine a X).length (· + k)).sum = n + k := by omega
  have hd := reverse_degree_all a n cs h e ha hh he hs hu
  have hf := reverse_degree_all a (n+k) cs h _ ha hh hel hsum hu
  rw [← hw] at hd
  rw [← hew] at hf
  refine ⟨_,_,hd,hf,?_,?_⟩
  · split_ifs <;> have := (internal_update e (spine a X).length k).1 <;> omega
  · split_ifs <;> have := (internal_update e (spine a X).length k).2 <;> omega

private theorem minimum_degree (u v w : List α) (M : List Side) (r : Nat)
    (hM : IsMinimumMask u v w M r) : degree u v w = (r : WithTop Nat) := by
  apply le_antisymm
  · simpa [degree, hM.2.1] using minRuns_le _ _ hM.1
  · apply (le_minRuns _ _).mpr
    intro N hN
    exact_mod_cast hM.2.2 N hN

private theorem reinsert_first (a : α) (n k : Nat) (v X B Y : List α)
    (hk : k ≤ n) (N : List Side)
    (hv : ValidMask (List.replicate (n-k) a) v (X ++ B ++ Y) N) :
    ∃ r t : Nat,
      degree (List.replicate n a) v (X ++ List.replicate k a ++ B ++ Y) = (r : WithTop Nat) ∧
      degree (List.replicate n a) v (X ++ B ++ List.replicate k a ++ Y) = (t : WithTop Nat) ∧
      r ≤ t + 1 ∧ t ≤ r + 1 := by
  obtain ⟨d,r,hd,hr,hdr,hrd⟩ := inserted_cut a (n-k) v X (B++Y) k
    ⟨N, by simpa [List.append_assoc] using hv⟩
  obtain ⟨f,t,hf,ht,hft,htf⟩ := inserted_cut a (n-k) v (X++B) Y k ⟨N,hv⟩
  have hdf' : (d : WithTop Nat) = (f : WithTop Nat) :=
    hd.symm.trans (by simpa only [List.append_assoc] using hf)
  have hdf : d = f := by exact_mod_cast hdf'
  have hn : n-k+k=n := by omega
  refine ⟨r,t,by simpa [hn,List.append_assoc] using hr, by simpa [hn] using ht,?_,?_⟩
  all_goals omega

private theorem reinsert_second (a : α) (n k : Nat) (u X B Y : List α)
    (hu : u ≠ []) (hk : k ≤ n) (N : List Side)
    (hv : ValidMask u (List.replicate (n-k) a) (X ++ B ++ Y) N) :
    ∃ r t : Nat,
      degree u (List.replicate n a) (X ++ List.replicate k a ++ B ++ Y) = (r : WithTop Nat) ∧
      degree u (List.replicate n a) (X ++ B ++ List.replicate k a ++ Y) = (t : WithTop Nat) ∧
      r ≤ t + 1 ∧ t ≤ r + 1 := by
  obtain ⟨d,r,hd,hr,hdr,hrd⟩ := reverse_cut a (n-k) u X (B++Y) k hu
    ⟨N, by simpa [List.append_assoc] using hv⟩
  obtain ⟨f,t,hf,ht,hft,htf⟩ := reverse_cut a (n-k) u (X++B) Y k hu ⟨N,hv⟩
  have hdf' : (d : WithTop Nat) = (f : WithTop Nat) :=
    hd.symm.trans (by simpa only [List.append_assoc] using hf)
  have hdf : d = f := by exact_mod_cast hdf'
  have hn : n-k+k=n := by omega
  refine ⟨r,t,by simpa [hn,List.append_assoc] using hr, by simpa [hn] using ht,?_,?_⟩
  all_goals omega

/-- Moving the actual unary-labelled block cannot change the minimum by more than one.
Both original projections of the common deleted word are retained. -/
theorem exchange_lower (a : α) (n : Nat) (u v : List α) (E : BlockCut α)
    (M : List Side) (hu : u ≠ []) (hM : ValidMask u v (original E) M)
    (hE : Admissible E M)
    (hun : u = List.replicate n a ∨ v = List.replicate n a) :
    ∃ r t : Nat, degree u v (original E) = (r : WithTop Nat) ∧
      degree u v (successor E) = (t : WithTop Nat) ∧ r ≤ t + 1 := by
  obtain ⟨ha,hb,C,hfits,hMC,hsplit,hcase⟩ := hE
  change C.X.length = E.X.length ∧ C.A.length = E.A.length ∧
    C.B.length = E.B.length ∧ C.Y.length = E.Y.length at hfits
  change M = C.X ++ C.A ++ C.B ++ C.Y at hMC
  rcases hfits with ⟨hx, hca, hcb, hy⟩
  rcases hun with hun | hun
  · subst u
    rcases hcase with ⟨hA,hB,_⟩ | ⟨hA,hB,_⟩
    · have hm : ValidMask (List.replicate n a) v (E.X ++ E.A ++ (E.B++E.Y))
          (C.X ++ List.replicate E.A.length .first ++ (C.B++C.Y)) := by
        simpa [original,hMC,hA,List.append_assoc] using hM
      obtain ⟨haa,hkn,hdel⟩ := erase_first a n v E.X E.A (E.B++E.Y) C.X (C.B++C.Y)
        hx (by simp [hcb,hy]) hm
      obtain ⟨r,t,hr,ht,hrt,_⟩ := reinsert_first a n E.A.length v E.X E.B E.Y hkn _
        (by simpa [List.append_assoc] using hdel)
      exact ⟨r,t,by simpa [original,← haa] using hr,
        by simpa [successor,← haa] using ht,hrt⟩
    · have hm : ValidMask (List.replicate n a) v ((E.X++E.A) ++ E.B ++ E.Y)
          ((C.X++C.A) ++ List.replicate E.B.length .first ++ C.Y) := by
        simpa [original,hMC,hB] using hM
      obtain ⟨haa,hkn,hdel⟩ := erase_first a n v (E.X++E.A) E.B E.Y (C.X++C.A) C.Y
        (by simp [hx,hca]) hy hm
      obtain ⟨t,r,ht,hr,_,hrt⟩ := reinsert_first a n E.B.length v E.X E.A E.Y hkn _ hdel
      exact ⟨r,t,by simpa [original,← haa] using hr,
        by simpa [successor,← haa] using ht,hrt⟩
  · subst v
    rcases hcase with ⟨hA,hB,_⟩ | ⟨hA,hB,_⟩
    · have hm : ValidMask u (List.replicate n a) ((E.X++E.A) ++ E.B ++ E.Y)
          ((C.X++C.A) ++ List.replicate E.B.length .second ++ C.Y) := by
        simpa [original,hMC,hB] using hM
      obtain ⟨haa,hkn,hdel⟩ := erase_second a n u (E.X++E.A) E.B E.Y (C.X++C.A) C.Y
        (by simp [hx,hca]) hy hm
      obtain ⟨t,r,ht,hr,_,hrt⟩ := reinsert_second a n E.B.length u E.X E.A E.Y hu hkn _ hdel
      exact ⟨r,t,by simpa [original,← haa] using hr,
        by simpa [successor,← haa] using ht,hrt⟩
    · have hm : ValidMask u (List.replicate n a) (E.X ++ E.A ++ (E.B++E.Y))
          (C.X ++ List.replicate E.A.length .second ++ (C.B++C.Y)) := by
        simpa [original,hMC,hA,List.append_assoc] using hM
      obtain ⟨haa,hkn,hdel⟩ := erase_second a n u E.X E.A (E.B++E.Y) C.X (C.B++C.Y)
        hx (by simp [hcb,hy]) hm
      obtain ⟨r,t,hr,ht,hrt,_⟩ := reinsert_second a n E.A.length u E.X E.B E.Y hu hkn _
        (by simpa [List.append_assoc] using hdel)
      exact ⟨r,t,by simpa [original,← haa] using hr,
        by simpa [successor,← haa] using ht,hrt⟩

/-- Every admissible exchange of every minimum mask is exact when either
ordered nonempty source is unary. -/
theorem result (u v : List α) (E : BlockCut α) (M : List Side) (r : Nat)
    (hu : u ≠ []) (hv : v ≠ []) (hmin : IsMinimumMask u v (original E) M r)
    (hr : 1 < r) (hE : Admissible E M)
    (hun : (∃ a m, 0 < m ∧ u = List.replicate m a) ∨
      (∃ a n, 0 < n ∧ v = List.replicate n a)) :
    degree u v (successor E) = ((r-1 : Nat) : WithTop Nat) := by
  have hm := minimum_degree u v (original E) M r hmin
  have hlo : ∃ s t : Nat, degree u v (original E) = (s : WithTop Nat) ∧
      degree u v (successor E) = (t : WithTop Nat) ∧ s ≤ t+1 := by
    rcases hun with ⟨a,n,hn,he⟩ | ⟨a,n,hn,he⟩
    · exact exchange_lower a n u v E M hu hmin.1 hE (Or.inl he)
    · exact exchange_lower a n u v E M hu hmin.1 hE (Or.inr he)
  obtain ⟨s,t,hs,ht,hst⟩ := hlo
  have hsr : s = r := by exact_mod_cast hs.symm.trans hm
  obtain ⟨N,hN,_,hNr⟩ := intended_successor u v E M hmin.1 hE
  have hupper : t ≤ rho N := by
    have hh := minRuns_le _ _ hN
    change degree u v (successor E) ≤ _ at hh
    rw [ht] at hh
    exact_mod_cast hh
  have hMr := hmin.2.1
  have hn : rho N + 1 = r := by omega
  rw [ht]
  congr 1
  omega

end D5.S1.Words.HughesUnaryExchange

/- GID: D5/S1/Words/Palindromes/FridPrefix/ChunkTransport
   generality: I
   mirror-B: D5/B/S1/Words/Palindromes/FridPrefix/ChunkTransport
   mirror-E: none(waiver:exact-paired-block-transport)
   anchors: []
   utility: none
   digest: Endpoint paths regroup into six-bit paths with their literal binary chunk values. -/

/-
proof_shape: content (endpoint_chunked).
escape_witness: construction of a chunk path from an arbitrary actual paired-bit path.
admission_basis: escape-witness.
Direct frozen dependencies: none; remaining dependencies are pinned Mathlib or this delivery.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.FridPrefix.EndpointAutomaton
import Mathlib.Data.Nat.Digits.Lemmas

namespace D5.S1.Words.FridPrefix
set_option maxHeartbeats 0 in

theorem endpoint_chunked (us vs : List (List (Fin 2)))
    (hlen : us.length=vs.length)
    (hu : ∀ u ∈ us, u.length=6) (hv : ∀ v ∈ vs, v.length=6)
    (ha : us.flatten.zip vs.flatten ∈ endpoint.accepts) :
    ((us.zip vs).map (fun p =>
      (Nat.ofDigits 2 (p.1.reverse.map Fin.val),Nat.ofDigits 2 (p.2.reverse.map Fin.val))))
      ∈ (chunkEndpoint 6).accepts := by
  have numeral_cons (a : Fin 2) (u : List (Fin 2)) :
      Nat.ofDigits 2 ((a::u).reverse.map Fin.val) =
        a.val*2^u.length+Nat.ofDigits 2 (u.reverse.map Fin.val) := by
    rw [List.reverse_cons,List.map_append,Nat.ofDigits_append]
    simp [Nat.ofDigits,Nat.add_comm,Nat.mul_comm]
  have move {q t : Fin 17} (u v : List (Fin 2)) (hl : u.length=v.length)
      (path : endpoint.Path q t (u.zip v)) :
      (Nat.ofDigits 2 (u.reverse.map Fin.val),Nat.ofDigits 2 (v.reverse.map Fin.val),t.val)
        ∈ movesFrom q.val u.length := by
    induction u generalizing v q with
    | nil =>
      have he : v=[] := List.length_eq_zero_iff.mp (by simpa using hl.symm)
      subst v
      cases path
      simp [movesFrom,Nat.ofDigits]
    | cons a u ih =>
      cases v with
      | nil => simp at hl
      | cons b v =>
        cases path with
        | cons r q t d w hm pt =>
          have hh := ih v (by simpa using hl) pt
          simp only [List.length_cons,movesFrom,List.mem_flatMap]
          refine ⟨(a.val,b.val,r.val),hm,?_⟩
          apply List.mem_map.mpr
          refine ⟨_,hh,?_⟩
          simp only [numeral_cons]
          rw [show v.length=u.length by simpa using hl.symm]
  have regroup {q t : Fin 17} (us vs : List (List (Fin 2)))
      (hl : us.length=vs.length) (hu : ∀ u∈us,u.length=6) (hv : ∀ v∈vs,v.length=6)
      (path : endpoint.Path q t (us.flatten.zip vs.flatten)) :
      Nonempty ((chunkEndpoint 6).Path q t ((us.zip vs).map (fun p =>
        (Nat.ofDigits 2 (p.1.reverse.map Fin.val),Nat.ofDigits 2 (p.2.reverse.map Fin.val))))) := by
    induction us generalizing vs q with
    | nil =>
      have he : vs=[] := List.length_eq_zero_iff.mp (by simpa using hl.symm)
      subst vs
      cases path
      exact ⟨NFA.Path.nil _⟩
    | cons u us ih =>
      cases vs with
      | nil => simp at hl
      | cons v vs =>
        have hlu := hu u (by simp)
        have hlv := hv v (by simp)
        have hword : (u::us).flatten.zip (v::vs).flatten =
            u.zip v ++ us.flatten.zip vs.flatten := by
          simp only [List.flatten_cons]
          exact List.zip_append (by omega)
        have hp := NFA.mem_evalFrom_iff_nonempty_path.mpr ⟨path⟩
        rw [hword,NFA.evalFrom_append,NFA.mem_evalFrom_iff_exists] at hp
        obtain ⟨r,hr,ht⟩ := hp
        obtain ⟨first⟩ := NFA.mem_evalFrom_iff_nonempty_path.mp hr
        obtain ⟨tail⟩ := NFA.mem_evalFrom_iff_nonempty_path.mp ht
        obtain ⟨rest⟩ := ih vs (by simpa using hl)
          (fun w hw => hu w (List.mem_cons_of_mem _ hw))
          (fun w hw => hv w (List.mem_cons_of_mem _ hw)) tail
        have hm := move u v (by omega) first
        rw [hlu] at hm
        exact ⟨NFA.Path.cons _ _ _ _ _ hm rest⟩
  obtain ⟨q,hq,t,ht,⟨path⟩⟩ := NFA.accepts_iff_exists_path.mp ha
  exact NFA.accepts_iff_exists_path.mpr ⟨q,hq,t,ht,regroup us vs hlen hu hv path⟩

end D5.S1.Words.FridPrefix

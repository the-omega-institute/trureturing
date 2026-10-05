import D5.Scale38ScanProbe
open D5.S3.Arith.FibonacciAtomic
open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address readout chi)

set_option autoImplicit false

theorem first_exit {m n : Nat} (F : Fin m → Source) (z i : Fin m)
    (q : Nat → Address) (exit : Fin m → Nat) (hi : i ≠ z)
    (zero : ∀ t < n, chi (readout (q t) (F z)) = 0)
    (before : ∀ i t, t < n → t < exit i → readout (q t) (F i) = readout (q t) (F z))
    (nonleaf : ∀ i, i ≠ z → exit i < n ∧ chi (readout (q (exit i)) (F i)) = 1) :
    ((List.range n).map q).find? (fun a => decide (chi (readout a (F i)) = 1)) =
      some (q (exit i)) := by
  have hbound := (nonleaf i hi).1
  apply List.find?_eq_some_iff_getElem.mpr
  refine ⟨by simp only [(nonleaf i hi).2, decide_true], exit i,
    by simpa only [List.length_map, List.length_range] using (nonleaf i hi).1, ?_, ?_⟩
  · simp only [List.getElem_map, List.getElem_range]
  · intro j hj
    simp only [List.getElem_map, List.getElem_range]
    rw [before i j (by omega) hj, zero j (by omega)]
    decide

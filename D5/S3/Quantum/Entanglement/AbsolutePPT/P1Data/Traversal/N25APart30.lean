/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart30
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart30
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart30.traversal_2025,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart30.traversal_2048,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart30.traversal_2051,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart30.traversal_2056,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart30.traversal_2071,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart30.traversal_2072,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart30.traversal_2073
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart23
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart24
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart29
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_2007 (fuel : Nat) (hf : 2007 < fuel) :
    walk nodes fuel 2007 = List.range' 1993 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2007).rule = .split 2 (507/128) 2005 2006 := by rfl
      simp only [walk, hr]
      rw [traversal_2005 f (by omega), traversal_2006 f (by omega)]
      change (List.range' 1993 13 ++ List.range' (1993+13) 1) ++
        [1993+(13+1)] = List.range' 1993 ((13+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1993) (n := 13+1)).symm

private theorem traversal_2008 (fuel : Nat) (hf : 2008 < fuel) :
    walk nodes fuel 2008 = List.range' 2008 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2008).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2009 (fuel : Nat) (hf : 2009 < fuel) :
    walk nodes fuel 2009 = List.range' 1993 17 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2009).rule = .split 1 (25/32) 2007 2008 := by rfl
      simp only [walk, hr]
      rw [traversal_2007 f (by omega), traversal_2008 f (by omega)]
      change (List.range' 1993 15 ++ List.range' (1993+15) 1) ++
        [1993+(15+1)] = List.range' 1993 ((15+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1993) (n := 15+1)).symm

private theorem traversal_2010 (fuel : Nat) (hf : 2010 < fuel) :
    walk nodes fuel 2010 = List.range' 2010 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2010).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2011 (fuel : Nat) (hf : 2011 < fuel) :
    walk nodes fuel 2011 = List.range' 1993 19 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2011).rule = .split 0 (1/40) 2009 2010 := by rfl
      simp only [walk, hr]
      rw [traversal_2009 f (by omega), traversal_2010 f (by omega)]
      change (List.range' 1993 17 ++ List.range' (1993+17) 1) ++
        [1993+(17+1)] = List.range' 1993 ((17+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1993) (n := 17+1)).symm

private theorem traversal_2012 (fuel : Nat) (hf : 2012 < fuel) :
    walk nodes fuel 2012 = List.range' 2012 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2012).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2013 (fuel : Nat) (hf : 2013 < fuel) :
    walk nodes fuel 2013 = List.range' 1993 21 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2013).rule = .split 3 (45/16) 2011 2012 := by rfl
      simp only [walk, hr]
      rw [traversal_2011 f (by omega), traversal_2012 f (by omega)]
      change (List.range' 1993 19 ++ List.range' (1993+19) 1) ++
        [1993+(19+1)] = List.range' 1993 ((19+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1993) (n := 19+1)).symm

private theorem traversal_2014 (fuel : Nat) (hf : 2014 < fuel) :
    walk nodes fuel 2014 = List.range' 2014 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2014).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2015 (fuel : Nat) (hf : 2015 < fuel) :
    walk nodes fuel 2015 = List.range' 1993 23 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2015).rule = .split 2 (263/64) 2013 2014 := by rfl
      simp only [walk, hr]
      rw [traversal_2013 f (by omega), traversal_2014 f (by omega)]
      change (List.range' 1993 21 ++ List.range' (1993+21) 1) ++
        [1993+(21+1)] = List.range' 1993 ((21+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1993) (n := 21+1)).symm

private theorem traversal_2016 (fuel : Nat) (hf : 2016 < fuel) :
    walk nodes fuel 2016 = List.range' 2016 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2016).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2017 (fuel : Nat) (hf : 2017 < fuel) :
    walk nodes fuel 2017 = List.range' 1993 25 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2017).rule = .split 1 (15/16) 2015 2016 := by rfl
      simp only [walk, hr]
      rw [traversal_2015 f (by omega), traversal_2016 f (by omega)]
      change (List.range' 1993 23 ++ List.range' (1993+23) 1) ++
        [1993+(23+1)] = List.range' 1993 ((23+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1993) (n := 23+1)).symm

private theorem traversal_2018 (fuel : Nat) (hf : 2018 < fuel) :
    walk nodes fuel 2018 = List.range' 2018 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2018).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2019 (fuel : Nat) (hf : 2019 < fuel) :
    walk nodes fuel 2019 = List.range' 1993 27 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2019).rule = .split 0 (1/20) 2017 2018 := by rfl
      simp only [walk, hr]
      rw [traversal_2017 f (by omega), traversal_2018 f (by omega)]
      change (List.range' 1993 25 ++ List.range' (1993+25) 1) ++
        [1993+(25+1)] = List.range' 1993 ((25+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1993) (n := 25+1)).symm

private theorem traversal_2020 (fuel : Nat) (hf : 2020 < fuel) :
    walk nodes fuel 2020 = List.range' 1962 59 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2020).rule = .split 3 (21/8) 1992 2019 := by rfl
      simp only [walk, hr]
      rw [traversal_1992 f (by omega), traversal_2019 f (by omega)]
      change (List.range' 1962 31 ++ List.range' (1962+31) 27) ++
        [1962+(31+27)] = List.range' 1962 ((31+27)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1962) (n := 31+27)).symm

private theorem traversal_2021 (fuel : Nat) (hf : 2021 < fuel) :
    walk nodes fuel 2021 = List.range' 2021 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2021).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2022 (fuel : Nat) (hf : 2022 < fuel) :
    walk nodes fuel 2022 = List.range' 1962 61 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2022).rule = .split 2 (141/32) 2020 2021 := by rfl
      simp only [walk, hr]
      rw [traversal_2020 f (by omega), traversal_2021 f (by omega)]
      change (List.range' 1962 59 ++ List.range' (1962+59) 1) ++
        [1962+(59+1)] = List.range' 1962 ((59+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1962) (n := 59+1)).symm

private theorem traversal_2023 (fuel : Nat) (hf : 2023 < fuel) :
    walk nodes fuel 2023 = List.range' 1607 417 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2023).rule = .split 1 (5/8) 1961 2022 := by rfl
      simp only [walk, hr]
      rw [traversal_1961 f (by omega), traversal_2022 f (by omega)]
      change (List.range' 1607 355 ++ List.range' (1607+355) 61) ++
        [1607+(355+61)] = List.range' 1607 ((355+61)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1607) (n := 355+61)).symm

private theorem traversal_2024 (fuel : Nat) (hf : 2024 < fuel) :
    walk nodes fuel 2024 = List.range' 1596 429 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2024).rule = .split 3 (9/4) 1606 2023 := by rfl
      simp only [walk, hr]
      rw [traversal_1606 f (by omega), traversal_2023 f (by omega)]
      change (List.range' 1596 11 ++ List.range' (1596+11) 417) ++
        [1596+(11+417)] = List.range' 1596 ((11+417)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1596) (n := 11+417)).symm

theorem traversal_2025 (fuel : Nat) (hf : 2025 < fuel) :
    walk nodes fuel 2025 = List.range' 1403 623 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2025).rule = .split 2 (61/16) 1595 2024 := by rfl
      simp only [walk, hr]
      rw [traversal_1595 f (by omega), traversal_2024 f (by omega)]
      change (List.range' 1403 193 ++ List.range' (1403+193) 429) ++
        [1403+(193+429)] = List.range' 1403 ((193+429)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1403) (n := 193+429)).symm

private theorem traversal_2026 (fuel : Nat) (hf : 2026 < fuel) :
    walk nodes fuel 2026 = List.range' 2026 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2026).rule = .bound .leftEnd 8 (151583/393216) (338953/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2027 (fuel : Nat) (hf : 2027 < fuel) :
    walk nodes fuel 2027 = List.range' 2027 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2027).rule = .bound .leftEnd 8 (38951/98304) (330511/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2028 (fuel : Nat) (hf : 2028 < fuel) :
    walk nodes fuel 2028 = List.range' 2028 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2028).rule = .bound .leftEnd 8 (73681/196608) (699011/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2029 (fuel : Nat) (hf : 2029 < fuel) :
    walk nodes fuel 2029 = List.range' 2029 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2029).rule = .bound .leftEnd 1 (73681/196608) (699011/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2030 (fuel : Nat) (hf : 2030 < fuel) :
    walk nodes fuel 2030 = List.range' 2028 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2030).rule = .split 1 (55/32) 2028 2029 := by rfl
      simp only [walk, hr]
      rw [traversal_2028 f (by omega), traversal_2029 f (by omega)]
      change (List.range' 2028 1 ++ List.range' (2028+1) 1) ++
        [2028+(1+1)] = List.range' 2028 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2028) (n := 1+1)).symm

private theorem traversal_2031 (fuel : Nat) (hf : 2031 < fuel) :
    walk nodes fuel 2031 = List.range' 2031 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2031).rule = .bound .leftEnd 1 (73681/196608) (699011/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2032 (fuel : Nat) (hf : 2032 < fuel) :
    walk nodes fuel 2032 = List.range' 2028 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2032).rule = .split 0 (1/40) 2030 2031 := by rfl
      simp only [walk, hr]
      rw [traversal_2030 f (by omega), traversal_2031 f (by omega)]
      change (List.range' 2028 3 ++ List.range' (2028+3) 1) ++
        [2028+(3+1)] = List.range' 2028 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2028) (n := 3+1)).symm

private theorem traversal_2033 (fuel : Nat) (hf : 2033 < fuel) :
    walk nodes fuel 2033 = List.range' 2027 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2033).rule = .split 3 (27/16) 2027 2032 := by rfl
      simp only [walk, hr]
      rw [traversal_2027 f (by omega), traversal_2032 f (by omega)]
      change (List.range' 2027 1 ++ List.range' (2027+1) 5) ++
        [2027+(1+5)] = List.range' 2027 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2027) (n := 1+5)).symm

private theorem traversal_2034 (fuel : Nat) (hf : 2034 < fuel) :
    walk nodes fuel 2034 = List.range' 2034 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2034).rule = .bound .leftEnd 8 (38951/98304) (330511/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2035 (fuel : Nat) (hf : 2035 < fuel) :
    walk nodes fuel 2035 = List.range' 2035 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2035).rule = .bound .leftEnd 3 (38951/98304) (330511/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2036 (fuel : Nat) (hf : 2036 < fuel) :
    walk nodes fuel 2036 = List.range' 2034 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2036).rule = .split 0 (1/40) 2034 2035 := by rfl
      simp only [walk, hr]
      rw [traversal_2034 f (by omega), traversal_2035 f (by omega)]
      change (List.range' 2034 1 ++ List.range' (2034+1) 1) ++
        [2034+(1+1)] = List.range' 2034 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2034) (n := 1+1)).symm

private theorem traversal_2037 (fuel : Nat) (hf : 2037 < fuel) :
    walk nodes fuel 2037 = List.range' 2037 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2037).rule = .bound .leftEnd 8 (73681/196608) (699011/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2038 (fuel : Nat) (hf : 2038 < fuel) :
    walk nodes fuel 2038 = List.range' 2038 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2038).rule = .bound .leftEnd 3 (73681/196608) (699011/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2039 (fuel : Nat) (hf : 2039 < fuel) :
    walk nodes fuel 2039 = List.range' 2037 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2039).rule = .split 1 (55/32) 2037 2038 := by rfl
      simp only [walk, hr]
      rw [traversal_2037 f (by omega), traversal_2038 f (by omega)]
      change (List.range' 2037 1 ++ List.range' (2037+1) 1) ++
        [2037+(1+1)] = List.range' 2037 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2037) (n := 1+1)).symm

private theorem traversal_2040 (fuel : Nat) (hf : 2040 < fuel) :
    walk nodes fuel 2040 = List.range' 2040 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2040).rule = .infeasible 10 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2041 (fuel : Nat) (hf : 2041 < fuel) :
    walk nodes fuel 2041 = List.range' 2037 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2041).rule = .split 0 (1/40) 2039 2040 := by rfl
      simp only [walk, hr]
      rw [traversal_2039 f (by omega), traversal_2040 f (by omega)]
      change (List.range' 2037 3 ++ List.range' (2037+3) 1) ++
        [2037+(3+1)] = List.range' 2037 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2037) (n := 3+1)).symm

private theorem traversal_2042 (fuel : Nat) (hf : 2042 < fuel) :
    walk nodes fuel 2042 = List.range' 2034 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2042).rule = .split 3 (27/16) 2036 2041 := by rfl
      simp only [walk, hr]
      rw [traversal_2036 f (by omega), traversal_2041 f (by omega)]
      change (List.range' 2034 3 ++ List.range' (2034+3) 5) ++
        [2034+(3+5)] = List.range' 2034 ((3+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2034) (n := 3+5)).symm

private theorem traversal_2043 (fuel : Nat) (hf : 2043 < fuel) :
    walk nodes fuel 2043 = List.range' 2027 17 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2043).rule = .split 2 (187/64) 2033 2042 := by rfl
      simp only [walk, hr]
      rw [traversal_2033 f (by omega), traversal_2042 f (by omega)]
      change (List.range' 2027 7 ++ List.range' (2027+7) 9) ++
        [2027+(7+9)] = List.range' 2027 ((7+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2027) (n := 7+9)).symm

private theorem traversal_2044 (fuel : Nat) (hf : 2044 < fuel) :
    walk nodes fuel 2044 = List.range' 2026 19 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2044).rule = .split 1 (25/16) 2026 2043 := by rfl
      simp only [walk, hr]
      rw [traversal_2026 f (by omega), traversal_2043 f (by omega)]
      change (List.range' 2026 1 ++ List.range' (2026+1) 17) ++
        [2026+(1+17)] = List.range' 2026 ((1+17)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2026) (n := 1+17)).symm

private theorem traversal_2045 (fuel : Nat) (hf : 2045 < fuel) :
    walk nodes fuel 2045 = List.range' 2045 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2045).rule = .bound .leftEnd 8 (151583/393216) (338953/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2046 (fuel : Nat) (hf : 2046 < fuel) :
    walk nodes fuel 2046 = List.range' 2046 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2046).rule = .bound .leftEnd 3 (151583/393216) (338953/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2047 (fuel : Nat) (hf : 2047 < fuel) :
    walk nodes fuel 2047 = List.range' 2045 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2047).rule = .split 1 (25/16) 2045 2046 := by rfl
      simp only [walk, hr]
      rw [traversal_2045 f (by omega), traversal_2046 f (by omega)]
      change (List.range' 2045 1 ++ List.range' (2045+1) 1) ++
        [2045+(1+1)] = List.range' 2045 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2045) (n := 1+1)).symm

theorem traversal_2048 (fuel : Nat) (hf : 2048 < fuel) :
    walk nodes fuel 2048 = List.range' 2026 23 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2048).rule = .split 0 (1/20) 2044 2047 := by rfl
      simp only [walk, hr]
      rw [traversal_2044 f (by omega), traversal_2047 f (by omega)]
      change (List.range' 2026 19 ++ List.range' (2026+19) 3) ++
        [2026+(19+3)] = List.range' 2026 ((19+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2026) (n := 19+3)).symm

private theorem traversal_2049 (fuel : Nat) (hf : 2049 < fuel) :
    walk nodes fuel 2049 = List.range' 2049 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2049).rule = .bound .leftEnd 8 (70081/196608) (735011/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2050 (fuel : Nat) (hf : 2050 < fuel) :
    walk nodes fuel 2050 = List.range' 2050 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2050).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_2051 (fuel : Nat) (hf : 2051 < fuel) :
    walk nodes fuel 2051 = List.range' 2049 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2051).rule = .split 3 (33/16) 2049 2050 := by rfl
      simp only [walk, hr]
      rw [traversal_2049 f (by omega), traversal_2050 f (by omega)]
      change (List.range' 2049 1 ++ List.range' (2049+1) 1) ++
        [2049+(1+1)] = List.range' 2049 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2049) (n := 1+1)).symm

private theorem traversal_2052 (fuel : Nat) (hf : 2052 < fuel) :
    walk nodes fuel 2052 = List.range' 2052 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2052).rule = .bound .leftEnd 8 (70081/196608) (735011/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2053 (fuel : Nat) (hf : 2053 < fuel) :
    walk nodes fuel 2053 = List.range' 2053 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2053).rule = .bound .leftEnd 8 (70081/196608) (735011/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2054 (fuel : Nat) (hf : 2054 < fuel) :
    walk nodes fuel 2054 = List.range' 2054 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2054).rule = .bound .leftEnd 3 (70081/196608) (735011/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2055 (fuel : Nat) (hf : 2055 < fuel) :
    walk nodes fuel 2055 = List.range' 2053 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2055).rule = .split 1 (45/32) 2053 2054 := by rfl
      simp only [walk, hr]
      rw [traversal_2053 f (by omega), traversal_2054 f (by omega)]
      change (List.range' 2053 1 ++ List.range' (2053+1) 1) ++
        [2053+(1+1)] = List.range' 2053 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2053) (n := 1+1)).symm

theorem traversal_2056 (fuel : Nat) (hf : 2056 < fuel) :
    walk nodes fuel 2056 = List.range' 2052 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2056).rule = .split 0 (1/40) 2052 2055 := by rfl
      simp only [walk, hr]
      rw [traversal_2052 f (by omega), traversal_2055 f (by omega)]
      change (List.range' 2052 1 ++ List.range' (2052+1) 3) ++
        [2052+(1+3)] = List.range' 2052 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2052) (n := 1+3)).symm

private theorem traversal_2057 (fuel : Nat) (hf : 2057 < fuel) :
    walk nodes fuel 2057 = List.range' 2057 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2057).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2058 (fuel : Nat) (hf : 2058 < fuel) :
    walk nodes fuel 2058 = List.range' 2058 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2058).rule = .bound .leftEnd 8 (33845/98304) (23791/32768) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2059 (fuel : Nat) (hf : 2059 < fuel) :
    walk nodes fuel 2059 = List.range' 2059 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2059).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2060 (fuel : Nat) (hf : 2060 < fuel) :
    walk nodes fuel 2060 = List.range' 2058 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2060).rule = .split 3 (69/32) 2058 2059 := by rfl
      simp only [walk, hr]
      rw [traversal_2058 f (by omega), traversal_2059 f (by omega)]
      change (List.range' 2058 1 ++ List.range' (2058+1) 1) ++
        [2058+(1+1)] = List.range' 2058 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2058) (n := 1+1)).symm

private theorem traversal_2061 (fuel : Nat) (hf : 2061 < fuel) :
    walk nodes fuel 2061 = List.range' 2057 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2061).rule = .split 2 (393/128) 2057 2060 := by rfl
      simp only [walk, hr]
      rw [traversal_2057 f (by omega), traversal_2060 f (by omega)]
      change (List.range' 2057 1 ++ List.range' (2057+1) 3) ++
        [2057+(1+3)] = List.range' 2057 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2057) (n := 1+3)).symm

private theorem traversal_2062 (fuel : Nat) (hf : 2062 < fuel) :
    walk nodes fuel 2062 = List.range' 2062 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2062).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2063 (fuel : Nat) (hf : 2063 < fuel) :
    walk nodes fuel 2063 = List.range' 2063 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2063).rule = .bound .leftEnd 8 (33845/98304) (23791/32768) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2064 (fuel : Nat) (hf : 2064 < fuel) :
    walk nodes fuel 2064 = List.range' 2064 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2064).rule = .bound .leftEnd 3 (33845/98304) (23791/32768) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2065 (fuel : Nat) (hf : 2065 < fuel) :
    walk nodes fuel 2065 = List.range' 2063 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2065).rule = .split 1 (95/64) 2063 2064 := by rfl
      simp only [walk, hr]
      rw [traversal_2063 f (by omega), traversal_2064 f (by omega)]
      change (List.range' 2063 1 ++ List.range' (2063+1) 1) ++
        [2063+(1+1)] = List.range' 2063 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2063) (n := 1+1)).symm

private theorem traversal_2066 (fuel : Nat) (hf : 2066 < fuel) :
    walk nodes fuel 2066 = List.range' 2066 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2066).rule = .bound .leftEnd 3 (33845/98304) (23791/32768) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2067 (fuel : Nat) (hf : 2067 < fuel) :
    walk nodes fuel 2067 = List.range' 2063 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2067).rule = .split 0 (1/80) 2065 2066 := by rfl
      simp only [walk, hr]
      rw [traversal_2065 f (by omega), traversal_2066 f (by omega)]
      change (List.range' 2063 3 ++ List.range' (2063+3) 1) ++
        [2063+(3+1)] = List.range' 2063 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2063) (n := 3+1)).symm

private theorem traversal_2068 (fuel : Nat) (hf : 2068 < fuel) :
    walk nodes fuel 2068 = List.range' 2068 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2068).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_2069 (fuel : Nat) (hf : 2069 < fuel) :
    walk nodes fuel 2069 = List.range' 2063 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2069).rule = .split 3 (69/32) 2067 2068 := by rfl
      simp only [walk, hr]
      rw [traversal_2067 f (by omega), traversal_2068 f (by omega)]
      change (List.range' 2063 5 ++ List.range' (2063+5) 1) ++
        [2063+(5+1)] = List.range' 2063 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2063) (n := 5+1)).symm

private theorem traversal_2070 (fuel : Nat) (hf : 2070 < fuel) :
    walk nodes fuel 2070 = List.range' 2062 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2070).rule = .split 2 (393/128) 2062 2069 := by rfl
      simp only [walk, hr]
      rw [traversal_2062 f (by omega), traversal_2069 f (by omega)]
      change (List.range' 2062 1 ++ List.range' (2062+1) 7) ++
        [2062+(1+7)] = List.range' 2062 ((1+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2062) (n := 1+7)).symm

theorem traversal_2071 (fuel : Nat) (hf : 2071 < fuel) :
    walk nodes fuel 2071 = List.range' 2057 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2071).rule = .split 1 (45/32) 2061 2070 := by rfl
      simp only [walk, hr]
      rw [traversal_2061 f (by omega), traversal_2070 f (by omega)]
      change (List.range' 2057 5 ++ List.range' (2057+5) 9) ++
        [2057+(5+9)] = List.range' 2057 ((5+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 2057) (n := 5+9)).symm

theorem traversal_2072 (fuel : Nat) (hf : 2072 < fuel) :
    walk nodes fuel 2072 = List.range' 2072 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2072).rule = .boxTail := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_2073 (fuel : Nat) (hf : 2073 < fuel) :
    walk nodes fuel 2073 = List.range' 2073 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 2073).rule = .bound .leftEnd 3 (33481/98304) (96165/131072) := by rfl
      simp only [walk, hr]
      rfl
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A

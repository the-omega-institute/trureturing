"""Insert 129 independently enumerated preimages into the probe's local proof."""
import json
from pathlib import Path

r = json.loads(Path('probe/enumeration.json').read_text())
w = r['preimages_765432819'][:129]
assert len(w) == len(set(map(tuple, w))) == 129
literal = lambda p: '[' + ','.join(map(str, p)) + ']'
text = '''
namespace C414

/-- A counterexample at n = 9; each of 129 preimages is checked separately. -/
theorem result : ¬ claim := by
  intro h
  let witnesses : List (List Nat) := [
'''
text += ',\n'.join('    ' + literal(p) for p in w) + ']\n'
text += '''  have hw : ∀ t ∈ witnesses,
      IsPerm 9 t ∧ SC false t = [7,6,5,4,3,2,8,1,9] := by
    simp only [witnesses, List.forall_mem_cons]
    repeat' apply And.intro
    all_goals decide +kernel
  have hdistinct : witnesses.toFinset.card = 129 := by decide +kernel
  have hsubset : witnesses.toFinset ⊆ Fibre false 9 [7,6,5,4,3,2,8,1,9] := by
    intro t ht
    have ht' := hw t (List.mem_toFinset.mp ht)
    simpa only [Fibre, Sn, List.mem_toFinset, List.mem_filter,
      List.mem_permutations', beq_iff_eq, IsPerm] using ht'
  have hlower := Finset.card_le_card hsubset
  rw [hdistinct] at hlower
  have hupper := ((h 9 (by decide)).1).2 [7,6,5,4,3,2,8,1,9] (by decide +kernel)
  change F false 9 [7,6,5,4,3,2,8,1,9] ≤ 128 at hupper
  change 129 ≤ F false 9 [7,6,5,4,3,2,8,1,9] at hlower
  omega

end C414

namespace C52

/-- Two distinct fibre values greater than 4 refute the first conjunct at n = 5. -/
theorem result : ¬ claim := by
  intro h
  have h5 := (h 5 (by decide)).1
  obtain ⟨m, hm, _, hunique⟩ := h5.2
  have hsmall : F false 5 [3,2,4,1,5] = 5 := by decide +kernel
  have hlarge : F false 5 [4,3,2,1,5] = 8 := by decide +kernel
  have hfirst := hunique [3,2,4,1,5] (by decide +kernel) (by omega)
  have hsecond := hunique [4,3,2,1,5] (by decide +kernel) (by omega)
  omega

end C52

#print axioms C414.result
#print axioms C52.result

end ZhaoProbe
'''
p = Path('probe/ZhaoProbe.lean')
s = p.read_text().split('-- BEGIN GENERATED WITNESS PROOFS')[0]
p.write_text(s + '-- BEGIN GENERATED WITNESS PROOFS\n' + text)

"""Generate item-split kernel cost probes for the 40320-input upper bound.

The 120 permutations of [4,5,6,7,8] partition S_8 after insertion of 3,2,1.
Each block has 6*7*8 = 336 inputs; blocks have disjoint deletion images.
This is a cost experiment, not a proof of the full upper bound.
"""
import argparse
from pathlib import Path
from enumerate import stack_sort


def insert_all(x, p):
    return [p[:i] + [x] + p[i:] for i in range(len(p) + 1)]


def permutations_prime(p):
    if not p:
        return [[]]
    return [q for t in permutations_prime(p[1:]) for q in insert_all(p[0], t)]


parser = argparse.ArgumentParser()
parser.add_argument('--blocks', type=int, default=16)
a = parser.parse_args()
base = permutations_prime([4, 5, 6, 7, 8])
core = Path('probe/ZhaoProbe.lean').read_text().split('namespace C414')[0]
text = core + '''
/- COST-ONLY: no conjecture result is claimed in this file. -/
private def block (tail : List Nat) : List (List Nat) :=
  (List.permutations'Aux 3 tail).flatMap fun t =>
    (List.permutations'Aux 2 t).flatMap (List.permutations'Aux 1)

'''
for i, t in enumerate(base[:a.blocks]):
    b = [r for p in insert_all(3, t) for q in insert_all(2, p) for r in insert_all(1, q)]
    preimages = [p for p in b if stack_sort(p) == (7,6,5,4,3,2,1,8)]
    text += f'-- Block {i}: 336 inputs, {len(preimages)} preimages.\n'
    text += 'example : ∀ p ∈ block ' + str(t).replace(' ', '') + ',\n'
    text += '    SC false p = [7,6,5,4,3,2,1,8] ↔ p ∈ (' + str(preimages).replace(' ', '') + ' : List (List Nat)) := by\n'
    chunks = [b[j:j + 48] for j in range(0, len(b), 48)]
    listing = ' ++ '.join(str(c).replace(' ', '') for c in chunks)
    text += '  have hlist : block ' + str(t).replace(' ', '') + ' = ' + listing + ' := by decide +kernel\n'
    text += """  rw [hlist]
  simp only [List.forall_mem_append]
  repeat' apply And.intro
  all_goals simp only [List.forall_mem_cons]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

"""
text += 'end ZhaoProbe\n'
Path('probe/Zhao419Cost.lean').write_text(text)
print(f'{a.blocks} blocks, {a.blocks * 336} map evaluations')

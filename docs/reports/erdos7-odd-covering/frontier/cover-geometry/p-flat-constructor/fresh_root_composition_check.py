"""Exact fresh-root -> p-flat composition check using the two sibling APIs.

Copy all three files together to run independently of the repository.
The fixture contains even cofactors and is not an odd-cover witness.
"""
import importlib.util
import json
from pathlib import Path


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    loaded = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(loaded)
    return loaded


def main():
    directory = Path(__file__).resolve().parent
    fresh = module('fresh_root', directory/'fresh_root_constructor.py')
    flat = module('p_flat', directory/'p_flat_constructor.py')
    first = fresh.fresh_root_construct(fresh.dyadic_fixture(7, 3), 7, 5, allow_even=True)
    fresh.require(first['q'] == first['t']+2, 'composition requires q=t+2')
    fresh.require({a for a, m in first['output'] if m == 5} == {0, 1},
                  'root replacement must supply exactly the two closing roots')
    second = flat.p_flat_construct(first['output'], 5, 3, allow_even=True)
    fresh.require(len({m for _, m in second['output']}) == len(second['output']),
                  'final distinct modulus palette')
    print(json.dumps({'success': True, 'first_input_period': first['input_period'],
           'first_output_period': first['output_period'],
           'final_output_period': second['output_period'],
           'final_labels': len(second['output']),
           'final_excess': second['output_excess'],
           'scope': 'even-cofactor fixture, not an all-odd cover witness'},
          sort_keys=True, indent=2))


if __name__ == '__main__':
    main()

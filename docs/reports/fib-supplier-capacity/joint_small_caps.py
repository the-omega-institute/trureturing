"""Finite evidence for the TM63 all-policy small-cap result.

Python 3.9+, standard library only.  The certificate checks the actual
Clifford source words in the complete h=4 composition domain, the literal
targets, the two-call policy, and the binary one-call obstruction.  It does
not implement a supplier, controller search, or a repository judge.
Mixed-history arithmetic and an exact three-valued Read witness check the
source correspondence used by the paper; Read itself is not binary.
"""

import argparse
from fractions import Fraction
import importlib.util
import itertools
import json
from pathlib import Path


SPEC = importlib.util.spec_from_file_location(
    "tm61_arithmetic", Path(__file__).with_name("h15_joint_cover.py"))
ARITH = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(ARITH)
require = ARITH.require


CAPS = (16, 17, 18, 19)
REPRESENTATIVES = ((2, 3), (3, 4), (3, 5), (4, 5))


def source_word(z, w):
    r, s = 2 * z - w, w - z
    return "a" * (2 * r - 1) + "b" * (2 * s) + "a" + \
        "b" * (2 * s - 1) + "a" * (2 * r) + "b"


def leaf_count_after_rho(word):
    return len(ARITH.rho(word))


def target_from_counts(a_count, b_count):
    require(a_count % 4 == 0 and b_count % 4 == 0,
            "source composition is not a four-block composition")
    r, s = a_count // 4, b_count // 4
    z, w = r + s, r + 2 * s
    if w > 4:
        return (0, 1, 4 * z)
    composition = (4 * r, 4 * s)
    return ((2, (((0, 0, 0),) * 3, composition)) if z + w <= 4
            else (1, composition, 1, 1))


def literal_target_h4(z, w):
    if w > 4:
        return (0, 1, 4 * z)
    composition = (4 * (2 * z - w), 4 * (w - z))
    return ((2, (((0, 0, 0),) * 3, composition)) if z + w <= 4
            else (1, composition, 1, 1))


def all_unit_words(max_len=16):
    """All unit leaf words in the h=4 source domain."""
    words = []
    for length in range(1, max_len + 1):
        for letters in itertools.product("ab", repeat=length):
            word = "".join(letters)
            current = word
            valid = True
            for _ in range(3):
                if ARITH.leaf_product(current) != ARITH.IDENTITY:
                    valid = False
                    break
                current = ARITH.rho(current)
            if not valid:
                continue
            a_count, b_count = word.count("a"), word.count("b")
            if a_count == 0 or b_count == 0:
                continue
            r, s = a_count // 4, b_count // 4
            if a_count % 4 or b_count % 4 or r + s > 4:
                continue
            words.append(word)
    return words


def source_rows(words):
    rows = []
    for word in words:
        target = target_from_counts(word.count("a"), word.count("b"))
        rows.append({
            "length": len(word),
            "a": word.count("a"),
            "b": word.count("b"),
            "target": target,
            "rho_length": leaf_count_after_rho(word),
        })
    return rows


def representative_table(cap):
    """The two-call policy's exact response table."""
    context_length = cap - 12
    table = []
    for z, w in REPRESENTATIVES:
        word = source_word(z, w)
        target = literal_target_h4(z, w)
        rho_response = "A" if leaf_count_after_rho(word) <= cap else "R"
        if rho_response == "A":
            current = leaf_count_after_rho(word)
        else:
            current = len(word)
        context_response = "A" if current + context_length <= cap else "R"
        table.append({
            "coordinate": [z, w],
            "target": target,
            "initial_length": len(word),
            "rho_length": leaf_count_after_rho(word),
            "first_response": rho_response,
            "second_context_length": context_length,
            "second_response": context_response,
            "response_word": rho_response + context_response,
        })
    require([row["response_word"] for row in table] == ["AA", "AR", "RA", "RR"],
            "two-call response code is not four-way separating")
    require(all(row["second_context_length"] > 0 for row in table),
            "policy used an empty context")
    return table


def check_all_source_rows(rows, cap):
    """Check the policy on every actual unit word, including folded rows."""
    target_responses = {}
    for row in rows:
        target = tuple(row["target"] if isinstance(row["target"], list)
                       else row["target"])
        word_length, rho_length = row["length"], row["rho_length"]
        first = "A" if rho_length <= cap else "R"
        current = rho_length if first == "A" else word_length
        context_length = cap - 12
        second = "A" if current + context_length <= cap else "R"
        code = first + second
        target_responses.setdefault(repr(target), set()).add(code)
        if target == (1, (4, 4), 1, 1):
            require(code == "AA", "first finite target not on AA branch")
        elif target == (1, (8, 4), 1, 1):
            require(code == "AR", "second finite target not on AR branch")
        elif target == (0, 1, 12):
            require(code == "RA", "folded 12 target not on RA branch")
        elif target == (0, 1, 16):
            require(code == "RR", "folded 16 target not on RR branch")
        else:
            raise ValueError("unexpected h=4 literal target")
    require(all(len(codes) == 1 for codes in target_responses.values()),
            "a target's response changed across actual source words")
    require(len(target_responses) == 4, "complete h=4 target image is not four")
    return target_responses


def window(word):
    values = []
    for _ in range(3):
        values.append(ARITH.leaf_product(word))
        word = ARITH.rho(word)
    return tuple(values)


def transport_j(value):
    """TM28's three-step J, in the existing exact Clifford matrices."""
    a, b, c, d = value
    coefficient_b = (b - Fraction(4, 5) * c) / 2
    coefficient_ab = (b + Fraction(4, 5) * c) / 2
    coefficient_i = (a + d - coefficient_ab) / 2
    coefficient_a = (a - d - coefficient_b) / 2
    ab = ARITH.multiply(ARITH.A, ARITH.B)
    # J(1)=1, J(A)=A+B, J(B)=-B, J(AB)=1-AB.
    return tuple((coefficient_i + coefficient_ab) * identity
                 + coefficient_a * alpha
                 + (coefficient_a - coefficient_b) * beta
                 - coefficient_ab * alpha_beta
                 for identity, alpha, beta, alpha_beta
                 in zip(ARITH.IDENTITY, ARITH.A, ARITH.B, ab))


def transport_f(values):
    return (values[1], values[2], transport_j(values[0]))


def window_product(left, right):
    return tuple(ARITH.multiply(x, y) for x, y in zip(left, right))


def mixed_history_evidence():
    """Replay fixed original-action histories on all six compositions.

    Each step also checks an actual Read.  The finite check supplements,
    rather than enumerates, the paper's arbitrary-history induction.
    """
    coordinates = ((2, 3), (3, 4), (3, 5), (4, 5), (4, 6), (4, 7))
    unit = (ARITH.IDENTITY,) * 3
    require(transport_f(unit) == unit, "F does not fix the unit triple")
    checked_steps = equality_acceptances = rejected_steps = 0
    response_rows = []
    for cap in CAPS:
        histories = (
            (("right", "a"), ("rho", ""), ("left", "b"),
             ("rho", ""), ("right", "ba")),
            (("left", "ba"), ("right", "a"), ("rho", ""),
             ("left", "a" * cap)),
            (("rho", ""), ("right", "a" * (cap - 12)),
             ("left", "b"), ("rho", "")),
        )
        for coordinate in coordinates:
            original = source_word(*coordinate)
            require(window(original) == unit, "mixed-history source not unit")
            for history_index, history in enumerate(histories):
                current, left, right, j = original, unit, unit, 0
                responses = []
                for side, context in history:
                    if side == "rho":
                        candidate = ARITH.rho(current)
                        require(window(candidate) == transport_f(window(current)),
                                "single rho does not follow F")
                    else:
                        require(bool(context), "empty context in fixed history")
                        candidate = (context + current if side == "left"
                                     else current + context)
                    accepted = len(candidate) <= cap
                    responses.append("A" if accepted else "R")
                    if accepted:
                        equality_acceptances += len(candidate) == cap
                        current = candidate
                        if side == "rho":
                            left, right, j = (transport_f(left),
                                              transport_f(right), j + 1)
                        elif side == "left":
                            left = window_product(window(context), left)
                        else:
                            right = window_product(right, window(context))
                    else:
                        rejected_steps += 1
                    unknown = unit
                    for _ in range(j):
                        unknown = transport_f(unknown)
                    predicted = window_product(window_product(left, unknown), right)
                    require(window(current) == predicted,
                            "ordered mixed-history window invariant fails")
                    require(ARITH.leaf_product(current) == predicted[0],
                            "actual exact Read differs from window prediction")
                    checked_steps += 1
                response_rows.append({
                    "H": cap, "coordinate": list(coordinate),
                    "history": history_index, "responses": "".join(responses),
                })
    require(equality_acceptances > 0 and rejected_steps > 0,
            "fixed histories omit equality or rejection")
    return {
        "source_compositions": len(coordinates), "caps": list(CAPS),
        "histories_per_source_and_cap": 3,
        "steps_and_exact_reads_checked": checked_steps,
        "equality_acceptances": equality_acceptances,
        "rejected_steps": rejected_steps,
        "histories": [[list(action) for action in history]
                      for history in (
                          (("right", "a"), ("rho", ""), ("left", "b"),
                           ("rho", ""), ("right", "ba")),
                          (("left", "ba"), ("right", "a"), ("rho", ""),
                           ("left", "a^H")),
                          (("rho", ""), ("right", "a^(H-12)"),
                           ("left", "b"), ("rho", "")))],
        "response_rows": response_rows,
    }


def source_correspondence_witnesses():
    """Reachable finite witnesses, not successful controller candidates."""
    original = source_word(2, 3)
    before = original + "a"
    after = ARITH.rho(before)
    require(len(before) <= 16 and len(after) <= 16,
            "single-rho witness is not a legal accepted history")
    require(ARITH.leaf_product(before) == ARITH.A
            and ARITH.leaf_product(after) == ARITH.B,
            "single-rho witness has wrong exact Read values")
    require(transport_j(ARITH.A) != ARITH.B,
            "three-step J was mistaken for single rho")

    context_product = ARITH.leaf_product("ba")
    merged_read_rows = []
    read_image = set()
    for z, w in ((2, 3), (3, 4), (3, 5), (4, 5), (4, 6), (4, 7)):
        current = source_word(z, w)
        repetitions = 0
        expected = ARITH.IDENTITY
        while len(current) + 2 <= 16:
            current += "ba"
            repetitions += 1
            expected = ARITH.multiply(expected, context_product)
        # Rejection keeps the actual source; one common Read state follows.
        value = ARITH.leaf_product(current)
        require(value == expected, "merged Read is not S^m")
        read_image.add(value)
        merged_read_rows.append({
            "coordinate": [z, w], "target": literal_target_h4(z, w),
            "accepted_context_repetitions": repetitions,
            "last_accepted_length": len(current),
            "first_rejected_candidate_length": len(current) + 2,
            "exact_read": "S^" + str(repetitions),
        })
    require(len(read_image) == 3, "merged Read witness lacks three responses")
    require([row["accepted_context_repetitions"] for row in merged_read_rows]
            == [4, 2, 2, 0, 0, 0], "merged Read repetitions changed")
    return {
        "single_rho_after_context": {
            "H": 16, "source_leaf_word": original,
            "actions": ["right_append_a", "rho"], "responses": "AA",
            "lengths": [len(original), len(before), len(after)],
            "exact_reads_after_actions": ["A", "B"], "J_of_A": "A+B",
        },
        "merged_read_after_context_loop": {
            "H": 16, "actual_right_context": "ba",
            "accept_continuation": "same_context_request",
            "reject_continuation": "one_common_exact_Read_request",
            "distinct_reachable_read_responses": 3,
            "rows": merged_read_rows,
            "successful_four_target_solver": False,
        },
    }


def recompute():
    words = all_unit_words()
    rows = source_rows(words)
    require(len(rows) == 920, "complete h=4 unit-word count changed")
    compositions = sorted({(row["a"], row["b"]) for row in rows})
    require(compositions == [(4, 4), (4, 8), (4, 12), (8, 4), (8, 8),
                              (12, 4)],
            "h=4 composition support changed")

    read_values = {ARITH.leaf_product(word) for word in words}

    cap_rows = []
    for cap in CAPS:
        table = representative_table(cap)
        image = check_all_source_rows(rows, cap)
        # Every initial complete source has the same unit Read response;
        # a modification response is exactly A or R.  This is the finite
        # one-call obstruction used by the paper's all-action argument.
        require(read_values == {ARITH.IDENTITY},
                "initial Read is not constant on complete h=4 sources")
        cap_rows.append({
            "H": cap,
            "target_count": 4,
            "source_word_count": len(rows),
            "initial_read_image": len(read_values),
            "one_call_max_response_image": 2,
            "two_call_policy": {
                "first_action": "rho",
                "continuation_action": "right_append_a^(H-12)",
                "reachable_request_values": 3,
                "worst_case_modification_calls": 2,
                "worst_case_total_source_calls": 2,
                "response_codes": [row["response_word"] for row in table],
            },
            "representatives": table,
            "target_response_image": {
                key: sorted(value) for key, value in sorted(image.items())
            },
        })

    # Kraft equality for the four two-call leaves, and the binary lower
    # bound for any one-call policy.
    kraft_sum = sum(2 ** -2 for _ in REPRESENTATIVES)
    require(kraft_sum == 1, "two-call prefix code is not Kraft-tight")
    return {
        "schema": "fib-tm63-joint-small-caps-v1",
        "source_domain": {
            "h": 4,
            "caps": list(CAPS),
            "unit_leaf_words": len(rows),
            "compositions": [list(pair) for pair in compositions],
            "all_bracketings_lifted_by": "Atomic360/TM47 behavior congruence",
        },
        "prefix_free_check": {
            "target_count_per_authentic_symbol": 4,
            "binary_modification_alphabet": ["A", "R"],
            "two_call_codewords": ["AA", "AR", "RA", "RR"],
            "kraft_sum": kraft_sum,
            "one_call_response_image_upper_bound": 2,
        },
        "caps": cap_rows,
        "mixed_history_evidence": mixed_history_evidence(),
        "source_correspondence_witnesses": source_correspondence_witnesses(),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certificate", type=Path,
                        default=Path(__file__).with_suffix(".json"))
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    result = recompute()
    canonical = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.write:
        args.certificate.write_text(canonical)
    else:
        require(args.certificate.read_text() == canonical,
                "retained finite evidence differs")
    print(json.dumps({
        "unit_leaf_words": result["source_domain"]["unit_leaf_words"],
        "caps": [{"H": row["H"],
                  "response_codes": row["two_call_policy"]["response_codes"],
                  "requests": row["two_call_policy"]["reachable_request_values"]}
                 for row in result["caps"]],
    }, sort_keys=True))


if __name__ == "__main__":
    main()

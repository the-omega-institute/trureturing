#!/usr/bin/env python3
"""The one required check of the CI workflow: every unit ran exactly when the change hit it.

Environment: NEEDS is `toJSON(needs)` of the aggregating job, which needs the
detection job `detect` and every unit job; HITS is the detection output
`hits`, a JSON object mapping each unit to whether the change hit it.

Green when detection succeeded, the units in HITS are exactly the other jobs
in NEEDS, every hit unit succeeded and every missed unit was skipped. Any
other combination is red (exit 1); malformed input exits 2.
"""
import json
import os
import sys

RESULTS = ("success", "failure", "cancelled", "skipped")


class InputError(ValueError):
    pass


def load(name):
    text = os.environ.get(name)
    if text is None:
        raise InputError(f"{name} is required")
    try:
        return json.loads(text)
    except json.JSONDecodeError as error:
        raise InputError(f"{name} is not JSON: {error}") from error


def main():
    try:
        needs = load("NEEDS")
        if not isinstance(needs, dict) or "detect" not in needs:
            raise InputError("NEEDS must be an object containing the detect job")
        results = {}
        for name, job in needs.items():
            result = job.get("result") if isinstance(job, dict) else None
            if result not in RESULTS:
                raise InputError(f"NEEDS job {name} has no valid result")
            results[name] = result
        detect = results.pop("detect")
        if detect != "success":
            print(f"CI_REQUIRED_RED detect result={detect}: change detection did not succeed")
            return 1
        hits = load("HITS")
        if (not isinstance(hits, dict) or not hits
                or any(not isinstance(value, bool) for value in hits.values())):
            raise InputError("HITS must be a nonempty object of booleans")
    except InputError as error:
        print(f"CI_REQUIRED_ERROR {error}", file=sys.stderr)
        return 2

    problems = []
    for name in sorted(set(results) - set(hits)):
        problems.append(f"job {name} has no unit section in the detection specification")
    for name in sorted(set(hits) - set(results)):
        problems.append(f"unit {name} has no job in needs")
    for name in sorted(set(hits) & set(results)):
        hit, result = hits[name], results[name]
        line = f"unit={name} hit={str(hit).lower()} result={result}"
        if result == ("success" if hit else "skipped"):
            print(f"CI_REQUIRED {line}")
        else:
            problems.append(line)
    for problem in problems:
        print(f"CI_REQUIRED_RED {problem}")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())

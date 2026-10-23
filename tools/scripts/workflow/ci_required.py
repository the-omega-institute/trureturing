#!/usr/bin/env python3
"""The one required check of the CI workflow: every unit ran exactly when the change hit it.

Environment: NEEDS is `toJSON(needs)` of the aggregating job, which needs the
detection job `detect` and every unit job; HITS is the detection output
`hits`, a JSON object mapping each unit to whether the change hit it.

Green when detection succeeded, the units in HITS are exactly the other jobs
in NEEDS, every hit unit succeeded with its corresponding execution identity,
and every missed unit was skipped. Any
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
        return json.loads(text, object_pairs_hook=lambda pairs: unique_object(name, pairs))
    except json.JSONDecodeError as error:
        raise InputError(f"{name} is not JSON: {error}") from error


def unique_object(name, pairs):
    keys = [key for key, _ in pairs]
    if len(set(keys)) != len(keys):
        raise InputError(f"{name} has a duplicate member")
    return dict(pairs)


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
    prerequisite = results.pop("source", None)
    if "current" in hits:
        if prerequisite is None:
            problems.append("current source prerequisite is missing from needs")
        elif hits["current"]:
            outputs = needs["source"].get("outputs", {})
            status = outputs.get("source_status") if isinstance(outputs, dict) else None
            continuation = outputs.get("continuation") if isinstance(outputs, dict) else None
            if prerequisite != "success" or status != "accepted" or continuation != "true":
                problems.append(f"prerequisite source result={prerequisite} status={status!r} continuation={continuation!r}")
            else:
                print("CI_REQUIRED prerequisite=source result=success status=accepted")
        elif prerequisite != "skipped":
            problems.append(f"unhit current source prerequisite result={prerequisite}")
        else:
            print("CI_REQUIRED prerequisite=source status=not-applicable")
    elif prerequisite is not None:
        problems.append("source prerequisite has no current unit in HITS")
    if hits.get("tests-fib") and not hits.get("current"):
        problems.append("selected tests-fib requires selected current")
    for name in sorted(set(results) - set(hits)):
        problems.append(f"job {name} has no unit section in the detection specification")
    for name in sorted(set(hits) - set(results)):
        problems.append(f"unit {name} has no job in needs")
    for name in sorted(set(hits) & set(results)):
        hit, result = hits[name], results[name]
        line = f"unit={name} hit={str(hit).lower()} result={result}"
        outputs = needs[name].get("outputs")
        executed = outputs.get("unit") if isinstance(outputs, dict) else None
        if hit and result == "success" and executed != name:
            problems.append(f"unit={name} execution identity={executed!r}")
        elif result == ("success" if hit else "skipped"):
            print(f"CI_REQUIRED {line}")
        else:
            problems.append(line + (" status=blocked" if hit and result == "skipped" else ""))
    for problem in problems:
        print(f"CI_REQUIRED_RED {problem}")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())

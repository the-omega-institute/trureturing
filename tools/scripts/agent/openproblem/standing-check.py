#!/usr/bin/env python3
"""Check a lane PR body's review standing before dispatching the next round.

usage: standing-check.py PR [--round N | --closed] [--carriers SEAT=CARRIER,...] [--body FILE] [--selftest]

Pass --round N with the round you are about to dispatch. Without it the table's own highest round
is taken as the last completed one, which cannot detect a round that ran and was never written down.
Pass --closed before merging instead: it requires the last round to carry no reject and no open round.

The review standing is the one part of a lane PR body that goes stale purely by omission: closing a
round is three edits — apply the findings, add the closed round's result rows, state the next round's
layout — and doing only two of them is invisible until three seats spend twenty minutes each finding it.

Checks, all mechanical:
  1. every round number from 1 up to the highest one present has rows in the standing table;
  2. every round in the table has three seat rows (architecture, quality, tests);
  3. no row carries a placeholder decision (`pending`, `-`, `?`, empty);
  4. every round in the table has a tally line naming it;
  5. a next-round layout line exists, and names the round being dispatched (--round, else table top + 1);
  6. `tests` is never nyxid-oracle, in any round or in the next-round layout;
  7. the nyxid-oracle seat differs between consecutive rounds, and between the last table round and
     the next-round layout.
  8. with --carriers, the assignment you are about to dispatch equals the one the layout line
     records. The layout line IS the recorded draw and the sshx contract forbids redrawing it,
     but the body cannot catch a dispatch that diverged from it: writing the round's rows
     replaces the layout line, so the two records never coexist. State the dispatch here and
     they are compared at the one moment both exist.

Exit 0 clean, 1 findings, 2 bad usage. Findings print one per line as `STANDING <CODE> <detail>`.

Case history this guards (each a real blocking finding, each costing a full review round):
  #8422 round 3: table held round 1 only, prose still named round 2 as the open round (3 seats).
  #8422 round 4 and #8407 round 3: same omission, one round later.
  #8358: three tallies out of round order, no next-round layout line at all.
  #8698 rounds 5 and 6: the recorded layout and the seats actually launched disagreed; each cost
     a full review round, and the second one was found by the very seat it misattributed.
"""
import re
import subprocess
import sys

SEATS = ("architecture", "quality", "tests")
ROW = re.compile(r"^\|\s*(\d+)\s*\|[^|]*\|\s*([A-Za-z]+)\s*\|\s*([^|]*?)\s*\|\s*([^|]*?)\s*\|\s*$")
TALLY = re.compile(r"[Rr]ound\s+(\d+)\s*(?:tally|`)", re.M)
TALLY_LIST = re.compile(r"[Rr]ound\s+tallies\s*:(.*?)(?:\n\n|\Z)", re.S)
LAYOUT = re.compile(r"[Rr]ound\s+(\d+)\s+seat\s+layout\b(.*?)(?:\n\n|\Z)", re.S)
PLACEHOLDER = {"", "-", "?", "pending", "n/a", "tbd"}


def nyxid_of(rows_for_round):
    """The seat holding nyxid-oracle in one round, or None."""
    for seat, carrier, _ in rows_for_round:
        if "nyxid" in carrier.lower():
            return seat
    return None


def carrier_family(name):
    """The carrier token a display string names: 'nyxid-oracle / ChatGPT Pro' -> 'nyxid-oracle'."""
    return name.split("/")[0].strip().lower()


# `is` must be a whole word here: with `\s*` the optional "is" eats the first two letters of a
# carrier named "isolated-token-subagent" and the parse yields "olated-token-subagent" (live #8698).
SEAT_ASSIGN = r"\b{seat}\b[`\s]*(?:seat\s*)?(?:is\s+)?[:=]?\s*([A-Za-z][\w-]*)"


def layout_seats(text):
    """seat -> carrier token as the layout line ASSIGNS it (first mention wins).

    Only the first match per seat is an assignment. These lines routinely end with the true
    sentence "`tests` is never nyxid-oracle"; reading every match would turn that into a claim.
    """
    out = {}
    for seat in SEATS:
        m = re.search(SEAT_ASSIGN.format(seat=seat), text, re.I)
        if m:
            out[seat] = m.group(1).lower()
    return out


def layout_findings(text, rnd, carriers):
    """Compare the recorded draw against the assignment about to be dispatched.

    The layout line IS the recorded draw: the sshx contract fixes it before the round's first
    seat launches and forbids redrawing it. Nothing in the body can detect a dispatch that
    diverged from it, because the layout line is replaced once the round's rows are written --
    the two records never coexist. So the dispatcher states its assignment here, at the one
    moment both exist. #8698 rounds 5 and 6 each cost a full review round to this divergence.
    """
    if carriers is None:
        return []
    findings = []
    assigned = layout_seats(text)
    for seat in SEATS:
        want, got = assigned.get(seat), carriers.get(seat)
        if want is None:
            findings.append(
                f"STANDING LAYOUT-INCOMPLETE round {rnd} layout assigns no carrier to {seat}"
            )
            continue
        if got is None:
            findings.append(
                f"STANDING LAYOUT-INCOMPLETE round {rnd} dispatch names no carrier for {seat}, "
                f"which the layout assigns to {want}"
            )
            continue
        if carrier_family(got) != want:
            findings.append(
                f"STANDING LAYOUT-MISMATCH round {rnd} layout assigns {seat} to {want} but the "
                f"dispatch states {carrier_family(got)}; the recorded draw is final"
            )
    return findings


def check(body, next_round=None, closed=False, carriers=None):
    findings = []
    rounds = {}
    for line in body.splitlines():
        m = ROW.match(line)
        if not m:
            continue
        rnd, seat, carrier, decision = int(m.group(1)), m.group(2).lower(), m.group(3), m.group(4)
        if seat not in SEATS:
            continue
        rounds.setdefault(rnd, []).append((seat, carrier, decision))

    if not rounds:
        # A first-publication body has no completed round: the template (impl-base-brief.md,
        # standing rule 2) makes it carry an empty table plus a "Round 1 seat layout" line stating
        # the drawn carriers. That is the correct state before round 1, not an omission, and it is
        # checked the same way as any other layout line (round number, tests never nyxid). Only a
        # body with neither rows nor a layout line is NO-TABLE.
        if (next_round is None or next_round == 1) and not closed and LAYOUT.search(body):
            layouts = LAYOUT.findall(body)
            nums = [int(n) for n, _ in layouts]
            if max(nums) != 1:
                findings.append(
                    f"STANDING LAYOUT-ROUND layout names round {max(nums)} but no round has completed"
                )
            text = dict((int(n), t) for n, t in layouts)[max(nums)]
            for m in re.finditer(SEAT_ASSIGN.format(seat="tests"), text, re.I):
                if m.group(1).lower().startswith("nyxid"):
                    findings.append("STANDING TESTS-NYXID round 1 layout assigns tests to nyxid-oracle")
                    break
            findings.extend(layout_findings(text, max(nums), carriers))
            return findings
        findings.append("STANDING NO-TABLE no completed-round rows found")
        return findings

    top = max(rounds)
    # Without --round, a body whose table simply stops early is indistinguishable from one whose
    # rounds really did stop there: nothing inside the body records a round that was run but never
    # written down. That is exactly the omission this guards (#8422 round 3, #8407 round 3), so the
    # caller supplies the round it is ABOUT TO DISPATCH and the table must hold every round below it.
    if next_round is not None:
        if top != next_round - 1:
            findings.append(
                f"STANDING ROUND-BEHIND dispatching round {next_round} but the table's highest "
                f"completed round is {top}; rounds {top + 1}..{next_round - 1} are unrecorded"
            )
        top = max(top, next_round - 1)
    for r in range(1, top + 1):
        if r not in rounds:
            findings.append(f"STANDING MISSING-ROUND round {r} has no rows while round {top} does")
            continue
        seats = [s for s, _, _ in rounds[r]]
        for seat in SEATS:
            if seat not in seats:
                findings.append(f"STANDING MISSING-SEAT round {r} has no {seat} row")
        for seat, carrier, decision in rounds[r]:
            if decision.strip().strip("`").lower() in PLACEHOLDER:
                findings.append(f"STANDING PLACEHOLDER round {r} {seat} decision is {decision!r}")
            if seat == "tests" and "nyxid" in carrier.lower():
                findings.append(f"STANDING TESTS-NYXID round {r} assigns tests to nyxid-oracle")

    tallied = set(int(x) for x in TALLY.findall(body))
    listed = TALLY_LIST.search(body)
    if listed:
        tallied |= set(int(x) for x in re.findall(r"round\s+(\d+)", listed.group(1), re.I))
    for r in sorted(rounds):
        if r not in tallied:
            findings.append(f"STANDING NO-TALLY round {r} has rows but no tally line")

    if closed:
        # --closed is the merge precondition, not a round dispatch: §5.11 requires no unresolved
        # reject, and an open round's layout line would contradict "no round is open".
        last = [d.strip().strip("`").lower() for _, _, d in rounds[top]]
        bad = [d for d in last if d.startswith("reject")]
        if bad:
            findings.append(f"STANDING OPEN-REJECT round {top} still carries {len(bad)} reject; §5.11 blocks the merge")
        if LAYOUT.search(body):
            findings.append("STANDING LAYOUT-WHILE-CLOSED a next-round layout line is present while the standing is closed")
        return findings

    layouts = LAYOUT.findall(body)
    if not layouts:
        findings.append(f"STANDING NO-NEXT-LAYOUT no 'Round N seat layout' line; round {top} is the last recorded")
    else:
        nums = [int(n) for n, _ in layouts]
        nxt = max(nums)
        want = next_round if next_round is not None else top + 1
        if nxt != want:
            findings.append(
                f"STANDING LAYOUT-ROUND layout names round {nxt} but the round being dispatched is {want}"
            )
        text = dict((int(n), t) for n, t in layouts)[nxt]
        # Read the word the layout ASSIGNS to tests, not any nyxid mention downstream of it: these
        # layout lines routinely end with the true sentence "`tests` is never nyxid-oracle", and a
        # proximity match on that sentence is a false positive (three live lanes, 2026-09-17).
        for m in re.finditer(r"\btests\b[`\s]*(?:seat\s*)?(?:is\s*)?[:=]?\s*([A-Za-z][\w-]*)", text, re.I):
            if m.group(1).lower().startswith("nyxid"):
                findings.append(f"STANDING TESTS-NYXID round {nxt} layout assigns tests to nyxid-oracle")
                break
        findings.extend(layout_findings(text, nxt, carriers))
        prev = nyxid_of(rounds.get(max(rounds), []))
        m = re.search(r"(architecture|quality)\s+nyxid", text, re.I)
        if m is None:
            m = re.search(r"nyxid[^,.]*?,?\s*(?:seat\s+)?(?:is\s+)?(architecture|quality)", text, re.I)
        nxt_seat = m.group(1).lower() if m else None
        if prev and nxt_seat and prev == nxt_seat:
            findings.append(
                f"STANDING DRAW-REPEAT round {nxt} keeps nyxid-oracle on {nxt_seat}, the same as round {top}"
            )

    for r in range(1, top):
        a, b = nyxid_of(rounds.get(r, [])), nyxid_of(rounds.get(r + 1, []))
        if a and b and a == b:
            findings.append(f"STANDING DRAW-REPEAT rounds {r} and {r + 1} both put nyxid-oracle on {a}")

    return findings


GOOD = """
| round | head | seat | carrier | decision |
| --- | --- | --- | --- | --- |
| 1 | `aaa` | architecture | codex-cli | reject |
| 1 | `aaa` | quality | nyxid-oracle / ChatGPT Pro | reject |
| 1 | `aaa` | tests | codex-cli | reject |
| 2 | `aaa` | architecture | nyxid-oracle / ChatGPT Pro | approve |
| 2 | `aaa` | quality | codex-cli | reject |
| 2 | `aaa` | tests | codex-cli | reject |

Round tallies: round 1 `approve 0, reject 3, abstain 0`; round 2 `approve 1, reject 2, abstain 0`.

Round 3 seat layout at this head: quality nyxid-oracle / ChatGPT Pro, architecture codex-cli, tests codex-cli.
"""


def selftest():
    cases = []
    cases.append(("clean", GOOD, []))
    cases.append(("gap", GOOD.replace("| 1 | `aaa` | architecture | codex-cli | reject |\n", ""), ["MISSING-SEAT"]))
    cases.append(("placeholder", GOOD.replace("| 2 | `aaa` | tests | codex-cli | reject |", "| 2 | `aaa` | tests | codex-cli | pending |"), ["PLACEHOLDER"]))
    cases.append(("no tally", GOOD.replace("; round 2 `approve 1, reject 2, abstain 0`", ""), ["NO-TALLY"]))
    cases.append(("no layout", GOOD.replace("Round 3 seat layout at this head: quality nyxid-oracle / ChatGPT Pro, architecture codex-cli, tests codex-cli.", ""), ["NO-NEXT-LAYOUT"]))
    cases.append(("stale layout", GOOD.replace("Round 3 seat layout", "Round 2 seat layout"), ["LAYOUT-ROUND"]))
    cases.append(("tests nyxid", GOOD.replace("| 2 | `aaa` | tests | codex-cli | reject |", "| 2 | `aaa` | tests | nyxid-oracle / ChatGPT Pro | reject |"), ["TESTS-NYXID"]))
    cases.append(("draw repeat in table", GOOD.replace("| 2 | `aaa` | architecture | nyxid-oracle / ChatGPT Pro | approve |\n| 2 | `aaa` | quality | codex-cli | reject |", "| 2 | `aaa` | architecture | codex-cli | approve |\n| 2 | `aaa` | quality | nyxid-oracle / ChatGPT Pro | reject |"), ["DRAW-REPEAT"]))
    cases.append(("draw repeat into next", GOOD.replace("Round 3 seat layout at this head: quality nyxid-oracle / ChatGPT Pro, architecture codex-cli", "Round 3 seat layout at this head: architecture nyxid-oracle / ChatGPT Pro, quality codex-cli"), ["DRAW-REPEAT"]))
    never = GOOD.replace(
        "Round 3 seat layout at this head: quality nyxid-oracle / ChatGPT Pro, architecture codex-cli, tests codex-cli.",
        "Round 3 seat layout at this head: quality nyxid-oracle / ChatGPT Pro, architecture codex-cli, tests codex-cli"
        " — the nyxid-oracle seat differs from round 2's, and `tests` is never nyxid-oracle.",
    )
    cases.append(("never-nyxid sentence is not an assignment", never, []))
    cases.append(("tests colon nyxid", GOOD.replace("tests codex-cli.", "tests: nyxid-oracle / ChatGPT Pro."), ["TESTS-NYXID"]))
    cases.append(("missing round", GOOD.replace("| 1 | `aaa` | architecture | codex-cli | reject |\n| 1 | `aaa` | quality | nyxid-oracle / ChatGPT Pro | reject |\n| 1 | `aaa` | tests | codex-cli | reject |\n", ""), ["MISSING-ROUND"]))
    zz22_r3 = """
| round | head | seat | carrier | decision |
| --- | --- | --- | --- | --- |
| 1 | `aaa` | architecture | codex-cli | reject |
| 1 | `aaa` | quality | nyxid-oracle / ChatGPT Pro | reject |
| 1 | `aaa` | tests | codex-cli | reject |

Round 1 tally: `approve 0, reject 3, abstain 0`.

Round 2 seat layout at this head: architecture nyxid-oracle / ChatGPT Pro, quality codex-cli, tests codex-cli.
"""
    cases.append(("#8422 round 3 body, no --round: invisible", zz22_r3, []))
    cases.append(("#8422 round 3 body, --round 3", (zz22_r3, 3), ["ROUND-BEHIND", "LAYOUT-ROUND"]))
    cases.append(("clean body, --round 3", (GOOD, 3), []))
    cases.append(("clean body, --round 4 is behind", (GOOD, 4), ["ROUND-BEHIND"]))
    closed_good = GOOD.replace(
        "| 2 | `aaa` | architecture | nyxid-oracle / ChatGPT Pro | approve |", "| 2 | `aaa` | architecture | nyxid-oracle / ChatGPT Pro | approve |"
    ).replace("| 2 | `aaa` | quality | codex-cli | reject |", "| 2 | `aaa` | quality | codex-cli | comment |"
    ).replace("| 2 | `aaa` | tests | codex-cli | reject |", "| 2 | `aaa` | tests | codex-cli | approve |"
    ).replace("Round 3 seat layout at this head: quality nyxid-oracle / ChatGPT Pro, architecture codex-cli, tests codex-cli.",
              "No round is open.")
    cases.append(("closed standing, no reject", (closed_good, None, True), []))
    cases.append(("closed standing with a reject", (GOOD.replace(
        "Round 3 seat layout at this head: quality nyxid-oracle / ChatGPT Pro, architecture codex-cli, tests codex-cli.",
        "No round is open."), None, True), ["OPEN-REJECT"]))
    cases.append(("closed standing still advertising a round", (closed_good.replace(
        "No round is open.", "Round 3 seat layout at this head: quality nyxid-oracle, architecture codex-cli, tests codex-cli."),
        None, True), ["LAYOUT-WHILE-CLOSED"]))
    bad = 0
    first_pub = """
| round | head | seat | carrier | decision |
| --- | --- | --- | --- | --- |

Round 1 seat layout at `aaa`: quality nyxid-oracle / ChatGPT Pro, architecture codex-cli, tests codex-cli; `tests` is never nyxid-oracle. No round has completed at this head; tally approve 0 / reject 0 / abstain 0. Carried-forward approvals: none. Disagreement adjudication: none.
"""
    cases.append(("first publication: empty table + round-1 layout", first_pub, []))
    cases.append(("first publication, --round 1", (first_pub, 1), []))
    cases.append(("first publication, layout names round 2", first_pub.replace("Round 1 seat layout", "Round 2 seat layout"), ["LAYOUT-ROUND"]))
    cases.append(("first publication, tests nyxid", first_pub.replace("tests codex-cli;", "tests nyxid-oracle / ChatGPT Pro;"), ["TESTS-NYXID"]))
    cases.append(("first publication, no layout line at all", first_pub.replace("Round 1 seat layout at `aaa`: quality nyxid-oracle / ChatGPT Pro, architecture codex-cli, tests codex-cli;", "Seats:"), ["NO-TABLE"]))
    cases.append(("first publication, --closed", (first_pub, None, True), ["NO-TABLE"]))

    # --carriers states what is ABOUT TO BE DISPATCHED. The layout line is the recorded draw; the
    # sshx contract fixes it before the round's first seat launches, so the two must agree. #8698
    # rounds 5 and 6 each burned a full review round on exactly this divergence: the body recorded
    # one seat->carrier assignment and a different one was launched, and nothing compared them.
    cases.append(("dispatch matches the recorded layout",
                  (GOOD, 3, False, {"quality": "nyxid-oracle", "architecture": "codex-cli", "tests": "codex-cli"}), []))
    cases.append(("dispatch swaps two seats against the layout",
                  (GOOD, 3, False, {"quality": "isolated-token-subagent", "architecture": "nyxid-oracle", "tests": "codex-cli"}),
                  ["LAYOUT-MISMATCH"]))
    cases.append(("#8698 round 6: layout said architecture codex, subagent ran it",
                  (GOOD, 3, False, {"architecture": "isolated-token-subagent", "quality": "nyxid-oracle", "tests": "codex-cli"}),
                  ["LAYOUT-MISMATCH"]))
    cases.append(("dispatch names no carrier for a seat the layout assigns",
                  (GOOD, 3, False, {"quality": "nyxid-oracle", "tests": "codex-cli"}), ["LAYOUT-INCOMPLETE"]))
    cases.append(("carrier family compared, not the full display string",
                  (GOOD, 3, False, {"quality": "nyxid-oracle / ChatGPT Pro", "architecture": "codex-cli / OpenAI",
                                    "tests": "codex-cli / OpenAI"}), []))
    cases.append(("no --carriers leaves the layout uncompared", (GOOD, 3, False, None), []))
    # A carrier whose name begins with "is" must not have those two letters eaten by the optional
    # "is" in the assignment pattern. Found by running the live #8698 body, where the layout reads
    # "quality isolated-token-subagent" and the parse returned "olated-token-subagent".
    is_carrier = GOOD.replace("quality nyxid-oracle / ChatGPT Pro, architecture codex-cli",
                              "architecture isolated-token-subagent / Anthropic Claude, quality nyxid-oracle / ChatGPT Pro")
    cases.append(("carrier name starting with 'is' is not truncated",
                  (is_carrier, 3, False, {"architecture": "isolated-token-subagent", "quality": "nyxid-oracle",
                                          "tests": "codex-cli"}), []))
    cases.append(("'tests is nyxid-oracle' still reads as an assignment",
                  GOOD.replace("tests codex-cli.", "tests is nyxid-oracle / ChatGPT Pro."), ["TESTS-NYXID"]))
    for name, body, want in cases:
        nxt, cl, car = None, False, None
        if isinstance(body, tuple):
            if len(body) == 4:
                body, nxt, cl, car = body
            elif len(body) == 3:
                body, nxt, cl = body
            else:
                body, nxt = body
        got = check(body, nxt, cl, car)
        codes = [f.split()[1] for f in got]
        if want:
            ok = all(w in codes for w in want)
        else:
            ok = not got
        print(f"{'ok  ' if ok else 'FAIL'} {name}: {codes}")
        if not ok:
            bad += 1
    print(f"STANDING_SELFTEST cases={len(cases)} failed={bad}")
    return 1 if bad else 0


def main(argv):
    if "--selftest" in argv:
        return selftest()
    if not argv:
        print(__doc__.splitlines()[2].strip(), file=sys.stderr)
        return 2
    if "--body" in argv:
        body = open(argv[argv.index("--body") + 1]).read()
    else:
        if not argv[0].isdigit():
            print(f"standing-check: first argument must be a PR number, got {argv[0]!r}", file=sys.stderr)
            return 2
        try:
            body = subprocess.check_output(
                ["gh", "pr", "view", argv[0], "-R", "the-omega-institute/trureturing",
                 "--json", "body", "--jq", ".body"],
                text=True,
                stderr=subprocess.PIPE,
            )
        except subprocess.CalledProcessError as exc:
            print(f"standing-check: could not read PR {argv[0]}: {exc.stderr.strip()}", file=sys.stderr)
            return 2
    next_round = None
    if "--round" in argv:
        next_round = int(argv[argv.index("--round") + 1])
    carriers = None
    if "--carriers" in argv:
        carriers = {}
        for part in argv[argv.index("--carriers") + 1].split(","):
            if "=" not in part:
                print(f"standing-check: --carriers wants SEAT=CARRIER, got {part!r}", file=sys.stderr)
                return 2
            seat, _, carrier = part.partition("=")
            seat = seat.strip().lower()
            if seat not in SEATS:
                print(f"standing-check: --carriers names {seat!r}, not one of {SEATS}", file=sys.stderr)
                return 2
            carriers[seat] = carrier.strip()
    closed = "--closed" in argv
    if closed and next_round is not None:
        print("standing-check: --round and --closed are mutually exclusive", file=sys.stderr)
        return 2
    findings = check(body, next_round, closed, carriers)
    for f in findings:
        print(f)
    print(f"STANDING_CHECK findings={len(findings)}")
    return 1 if findings else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

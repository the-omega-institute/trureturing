#!/usr/bin/env python3
"""body-chronology-check.py PR [--file PATH] — flag process chronology in a PR body before it is published.

CLAUDE.md 2.10: a PR body carries current results, readings, verification state and open boundaries.
It does not carry implementation/review chronology: what an earlier head said, which round found what,
what was repaired, which attempt a reading came from. History lives in git and in the GitHub timeline.

立条依据: session 6c2e9558, 2026-09-20. Five review rejections across PRs #8698 and #8701 in one session;
four of them were purely this defect and none touched the mathematics. Each cost a full review round
(three seats, ~20 minutes of seat time each). The defect is invisible to the author because narrating
the repair feels like transparency; it is visible to every reviewer because 2.10 names it outright.

This is a WORD-LIST check, deliberately. It cannot be complete: natural language is not lintable
(CLAUDE.md 2.9, 3.5). It is early feedback for the author, not a gate, and it is not wired into any
required check. A clean run does not prove the body is 2.10-compliant; a hit is a prompt to re-read
the sentence and ask the delete test: remove it — is any CURRENT property lost?

MEASURED BLIND SPOT, stated so nobody mistakes a clean run for a clean body: this checker detects
NARRATIVE chronology, not STALE VALUES. On PR #8698 a review seat found four defects in a body this
checker reported clean — a private-declaration count of fourteen where the head had thirteen, a
module SHA-256 measured on superseded bytes, an axiom table anchored at a superseded commit, and a
CI sentence in pending tense. Only the last belongs to a word class, and it is now covered. The
other three are numbers that were true once; no word list can tell a true number from a stale one.
Re-derive every number in a body against the delivered head before publishing it.

Exit 0 when no line matches, 1 when some line matches, 2 on bad input.
"""
import json, re, subprocess, sys

# Each pattern is a phrase that can only be about the past. Patterns that also have a legitimate
# present reading (e.g. "current", "now") are deliberately absent: they would fire on every body.
PATTERNS = [
    (r"\b(an |the )?earlier\b(?!.*\bthan\b)", "narrates an earlier state"),
    (r"\bpreviously\b|\bformerly\b|\buntil (now|recently)\b", "narrates a prior state"),
    (r"\bhas since\b|\bsince then\b|\bafterwards?\b|\bsubsequently\b", "narrates a sequence"),
    (r"\bwas (rewritten|repaired|fixed|corrected|replaced|removed|deleted|added|dispatched|launched)\b", "narrates an action taken"),
    (r"\b(repair|fix|correction)s? (made|landed|applied|below)\b", "narrates a repair"),
    (r"\bround[- ]?\d+ (finding|rejection|review) ", "narrates a review round's content"),
    # The verb slot is deliberately OPEN. A closed list is exactly what failed: the previous
    # pattern enumerated five verbs and the author wrote a sixth. This checker is advisory, so a
    # broad match costs a glance and a narrow one costs a review round.
    (r"\b(is |are )?now \w+\b", "narrates a transition"),
    (r"\balready (carried|contained|stated|had|held|said)\b", "contrasts with an earlier state"),
    (r"\bno longer\b|\bused to\b", "narrates a transition"),
    (r"\battempt[- ]?\d+\b", "names an attempt number"),
    (r"\b(first|second|third) (run|pass|attempt) of\b", "names an attempt ordinal"),
    (r"\bthe (stale|obsolete|superseded|old) \w+ (was|is now)\b", "narrates supersession"),
    (r"\bre-?(run|taken|measured|read) (by|after|following) the\b", "narrates when a reading was retaken"),
    # The three below were added from measured misses: on PR #8701 the first pass of this checker
    # caught 2 of the 5 fragments three review seats actually flagged. Each pattern names its miss.
    (r"\b(in |from |of )?repair \d+\b", "names a numbered repair"),            # 'the misquotation finding in repair 2'
    (r"\bin response to\b", "narrates a reaction to a prior event"),            # 'in response to the round-1 advisory'
    # 'the round-1 architecture advisory'. The two negative lookaheads protect the standing block that
    # CLAUDE.md 5.2 REQUIRES and that standing-check.py parses: 'Round N seat layout' and 'Round N standing'
    # are mandatory current-state disclosures, not chronology; firing on them would train the author to
    # ignore this checker.
    (r"\bround[- ]?\d+\b(?! +(seat layout|standing|tally))(?=.{0,40}\b(advisor|finding|rejection|comment)\w*\b)",
     "narrates a review round's output"),
    (r"\b(reading|search|measurement|count)s?\b(?=.{0,60}\bagreed?\b)", "compares against a superseded reading"),
    # Pending tense: a body that promises a future reading is not stating a current one. Measured
    # miss on PR #8698, whose body still said a CI run was in progress after all three required
    # checks had completed; a review seat caught it and that round cost three seats.
    (r"\b(is|are) (currently )?(in progress|running|pending|under way|underway)\b", "promises a reading instead of stating one"),
    (r"\bwhen (it|they) (complete|completes|finish|finishes)\b", "defers a reading to the future"),
    (r"\b(will be|to be) (recorded|added|dispatched|filled|updated|measured)\b", "defers a reading to the future"),
    # Chinese prose was entirely unguarded: every pattern above is an English regex, while this
    # repository's PR bodies are written in both languages. Measured on PR #9037, where two review
    # seats rejected a Chinese repair-history sentence this checker returned hits=0 on. These match
    # the narration, not the vocabulary a compliant Chinese body needs: 交付 head, 逐字节相同,
    # 预登记, seat layout lines and pool-failure disclosures all stay unmatched (fixtures pin that).
    (r"先前[的之]?\S{0,8}(是错|不对|有误|已删|已改)", "narrates a prior state and its repair"),
    (r"(已删除|已改写|已撤回|已修正|已更正)而非", "narrates how a repair was carried out"),
    (r"(原先|原本|此前|先前|早先)\S{0,12}(与现在|不同|改为|换成|已(删|改|撤))", "contrasts with an earlier state"),
    (r"第\s*[0-9一二三四五六七八九十]+\s*(、|和|与|至|到)?\s*[0-9一二三四五六七八九十]*\s*轮[^。]{0,16}(被拒|拒绝|reject)", "narrates what earlier rounds decided"),
    (r"不为\S{0,10}重跑(冻结|deposit|emit)", "narrates a repair decision rather than a current property"),
    (r"本轮[^。]{0,12}已应用", "narrates that findings were applied"),
    # Two measured misses on PR #8698, each caught by a review seat after this checker returned 0.
    # Both describe an edit made to THIS deliverable, which is what 2.10 excludes; the anchoring and
    # search vocabulary that legitimately uses past tense ('was found in the searched scope', 'no
    # citation index was retrieved', a mutation that 'is deleted and replaced') stays unmatched
    # because these patterns require a round-outcome verb or the word repair/correction itself.
    (r"\brounds?[- ]?\d+(\s*,\s*\d+)*(\s+(and|&)\s+\d+)?\s+(all\s+)?(rejected|approved|objected|flagged)\b",
     "narrates what earlier rounds decided"),                       # 'Rounds 5, 6 and 7 all rejected on one class'
    (r"\b(removed|deleted|dropped|rewritten|corrected|replaced|cut)\s+rather than\b",
     "narrates how a repair was carried out"),                      # 'removed rather than corrected'
    (r"\b(correction|repair|fix)s?\b(?=.{0,45}\b(preserve\w*|kept|keeps|retain\w*|leave\w*|do not|does not)\b)",
     "narrates the effect of an edit made to this delivery"),       # 'display corrections preserve the Lean source'
]
# A body legitimately anchors readings to commits and names disclosed boundaries; those are current
# properties of the evidence, so anchoring vocabulary is not matched above.

def body_of(pr, path):
    if path:
        try:
            return open(path, encoding="utf-8").read()
        except OSError as e:
            print(f"BODY_CHRONOLOGY bad --file: {e}", file=sys.stderr); sys.exit(2)
    try:
        out = subprocess.run(["gh", "pr", "view", str(pr), "--json", "body"],
                             capture_output=True, text=True, check=True).stdout
        return json.loads(out)["body"] or ""
    except (subprocess.CalledProcessError, json.JSONDecodeError, KeyError) as e:
        print(f"BODY_CHRONOLOGY cannot read PR {pr}: {e}", file=sys.stderr); sys.exit(2)

def main(argv):
    if not argv:
        print(__doc__, file=sys.stderr); return 2
    pr, path = argv[0], None
    if "--file" in argv:
        i = argv.index("--file")
        if i + 1 >= len(argv):
            print("BODY_CHRONOLOGY --file needs a path", file=sys.stderr); return 2
        path = argv[i + 1]
    # Inline code spans carry identifiers, not prose: a Lean binder named `earlier`, a commit subject,
    # a shell flag. Matching inside them is a measured false-positive source (PR #8698 body line 32,
    # `IsValley (earlier : List N)`), so blank them out before matching and keep the line numbering.
    CODE = re.compile(r"`[^`]*`")
    hits = []
    for n, line in enumerate(body_of(pr, path).splitlines(), 1):
        probe = CODE.sub(lambda m: " " * len(m.group(0)), line)
        for rx, why in PATTERNS:
            m = re.search(rx, probe, re.I)
            if m:
                hits.append((n, why, m.group(0).strip(), line.strip()[:110]))
                break
    for n, why, frag, line in hits:
        print(f"BODY_CHRONOLOGY line {n}: {why} — {frag!r}\n    {line}")
    print(f"BODY_CHRONOLOGY_CHECK hits={len(hits)}")
    return 1 if hits else 0

if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

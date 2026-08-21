using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History.Consensus;

internal sealed class InlineConsensusOptimalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite fail-closed consensus router is the unique greatest sound rule, and every maximal protocol run consumes a finite shared resource potential.",
        H("Inline Consensus Optimality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("termination-router-is-the-unique-greatest-sound-rule"),
                DeclarationHandle.Create(
                    "D5/S0/History/Consensus/InlineConsensusOptimality."
                    + "termination_router_sound_maximal_unique"),
                H("The termination router is sound, maximal, and unique"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("Sound")), Open, F.Id("r"), Star, Close,
                    Sp, Land, Sp,
                    Forall, Sp, F.Id("p"), Comma, Sp,
                    Operatorname, Grp(F.Id("Sound")), Open, F.Id("p"), Close,
                    Sp, Rightarrow, Sp, F.Id("p"), Sp, Le, Sp, F.Id("r"), Star,
                    Sp, Land, Sp,
                    Operatorname, Grp(F.Id("unique")), Open, F.Id("r"), Star, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The observation contract contains exactly three named termination seats and "
                        + "a three-slot roster; its dependent result function cannot contain a "
                        + "meta-judge verdict. A completed seat result carries the exact peer-free "
                        + "seat view, a non-abstain carrier with matching prior disclosure, and a "
                        + "proof of all five completion conjuncts. Invalid and missing inputs remain "
                        + "fail-closed rows, but cannot masquerade as completed seats. Hazard is "
                        + "stated independently as a fake roster or a named seat that is not a valid "
                        + "satisfied result; it is not the Boolean complement of the router.")),
                    Paragraph(Text(
                        "The proof exhausts the finite router rows to identify hazard-free "
                        + "observations with exact-roster all-satisfied observations. Soundness and "
                        + "pointwise maximality follow from that equivalence. Uniqueness applies "
                        + "Mathlib's IsGreatest.unique rather than reproving greatest-element "
                        + "antisymmetry.")),
                    Paragraph(Text(
                        "Two concrete competitors show that both halves do work. Always-abstain is "
                        + "sound but strictly below the router at the exact all-satisfied fixture. "
                        + "Majority-admit is strictly more permissive, but the two-satisfied and "
                        + "one-unsatisfied fixture proves that it is not sound. Lean checks the three "
                        + "review-router rows as a truth-table fixture; it defines no review hazard, "
                        + "soundness, or maximality theorem. The design table likewise has convergence "
                        + "and bounded-stall exits and supplies no independent binary hazard predicate, "
                        + "so no design maximality claim is made.")),
                    Paragraph(Text(
                        "Snapshot note: the abstract model was compared with the beta.32 sshx "
                        + "SKILL.md whose SHA-256 is "
                        + "ab688e34f2b183291958f78b2d9ff6905d7330f3844668c5103026790d8b4cbf "
                        + "and CODEX_WORKER_SPEC.md whose SHA-256 is "
                        + "700237b1a1389002215272874e8c9cd7b17a130f0d0eaf7bb20cf9b39f49829d. "
                        + "This is prose snapshot correspondence only. A later plugin version may "
                        + "falsify it without falsifying the Lean theorems; no current or future "
                        + "plugin version is claimed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("every-maximal-protocol-run-is-explicitly-bounded"),
                DeclarationHandle.Create(
                    "D5/S0/History/Consensus/InlineConsensusOptimality."
                    + "every_maximal_run_is_bounded"),
                H("Every maximal protocol run is explicitly bounded"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("run"), Comma, Sp,
                    F.Id("length"), Open, F.Id("run"), Close,
                    Sp, Le, Sp,
                    Operatorname, Grp(F.Id("explicitRunBound")), Open, F.Id("config"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "InlineConsensusModel records the stage relation, carrier selector, completion "
                        + "predicate, seat view, role-indexed thinking and review result types, prior "
                        + "disclosure, three routers, roster contract, pass-locus predicate, and guarded "
                        + "transition relation. The internal-wiring theorem checks only those record "
                        + "projections; it does not prove correspondence to external prose. Named "
                        + "semantic fixtures pin executable rows and invariants. Correspondence to the "
                        + "sshx source remains only the digest-pinned snapshot claim stated above.")),
                    Paragraph(Text(
                        "A protocol step either erases one previously available stage-role-carrier "
                        + "key within its fixed retry budget; follows the unique stage successor only "
                        + "with isolation and stage-specific evidence; derives and retains the design "
                        + "or review outcome from fixed role-indexed verdict records; consumes one "
                        + "shared bounded-pass unit at that pass kind's legal locus; or abstains only on "
                        + "carrier exhaustion, isolation unavailability, or a router abstain exit. A "
                        + "rejected review can change only through a bounded fix-and-review step, and "
                        + "finish requires retained review done, available isolation, and termination "
                        + "permission. Every transition and execution also requires the single config "
                        + "budget to satisfy the at-most-five-unless-owner-authorized policy. "
                        + "The potential is the sum of "
                        + "remaining flight keys, remaining stage edges, remaining shared passes, "
                        + "and one live-state credit. Mathlib's card_erase_lt_of_mem proves that a "
                        + "flight failure strictly decreases the first component; the other "
                        + "constructors decrease their named component.")),
                    Paragraph(Text(
                        "Induction over the guarded operational execution proves retry-budget "
                        + "compliance, non-reopening of carrier keys, the shared-pass bound, and the "
                        + "explicit length bound for every maximal run. Universal abstention was "
                        + "removed: without a separate liveness premise a guarded live state may be "
                        + "deadlocked, so no terminal-reachability conclusion is claimed. The named "
                        + "selector fixtures pin codex-first, highest-priority-untried fallback, and "
                        + "exhaustion; the thinking-exhaustion fixture has no dependent-stage event. "
                        + "Additional negative fixtures exercise unavailable isolation, reject an "
                        + "unauthorized budget of six, and prevent an all-reject review from finishing "
                        + "without a fix-and-review step."))),
                DescribeRole.Theorem))));
}

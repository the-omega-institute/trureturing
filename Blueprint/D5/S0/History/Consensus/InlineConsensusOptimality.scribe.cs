using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History.Consensus;

internal sealed class InlineConsensusOptimalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Carrier selection is available and every available priority minimum equals it, while the design router rejects single-perspective consensus.",
        H("Inline Consensus Optimality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("carrier-selection-is-available-and-identifies-every-priority-minimum"),
                DeclarationHandle.Create(
                    "D5/S0/History/Consensus/InlineConsensusOptimality."
                    + "selectCarrier_is_unique_minimum"),
                H("Carrier selection is available and identifies every priority minimum"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("eligible"), Comma, Sp, F.Id("tried"), Comma, Esc,
                    Call("Nonempty", EligibleUntried()), Sp, Rightarrow, Sp,
                    Call("selectCarrier", F.Id("eligible"), F.Id("tried")), Sp,
                    InMacro, Sp, EligibleUntried(),
                    RowBreak, Sp, Land, Sp,
                    Forall, Sp, F.Id("other"), Comma, Esc,
                    F.Id("other"), Sp, InMacro, Sp, EligibleUntried(), Sp,
                    Rightarrow, Sp,
                    Open, Forall, Sp, F.Id("carrier"), Comma, Esc,
                    F.Id("carrier"), Sp, InMacro, Sp, EligibleUntried(), Sp,
                    Rightarrow, Sp,
                    Call("priorityRank", F.Id("other")), Sp, Le, Sp,
                    Call("priorityRank", F.Id("carrier")), Close,
                    Sp, Rightarrow, Sp,
                    F.Id("other"), Sp, Eq, Sp,
                    Call("selectCarrier", F.Id("eligible"), F.Id("tried"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Whenever the eligible carriers not yet tried form a nonempty finite set, "
                        + "selectCarrier belongs to that set. Any other available carrier whose "
                        + "priority rank is no greater than every available carrier's rank must equal "
                        + "the selected carrier.")),
                    Paragraph(Text(
                        "The result is conditional on a nonempty eligible-untried set. It does not say "
                        + "that a worker carrier is always available, and the separate exhaustion row "
                        + "selects abstain when that set is empty."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("single-perspective-consensus-is-rejected"),
                DeclarationHandle.Create(
                    "D5/S0/History/Consensus/InlineConsensusOptimality."
                    + "design_router_rejects_single_perspective"),
                H("Single-perspective consensus is rejected"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("designRouter", F.Id("singlePerspective")), Sp, Eq, Sp,
                    F.Id("rejectFakeConsensus")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The singlePerspective row of designRouter returns rejectFakeConsensus. "
                        + "This equation states one router row; it does not "
                        + "supply an independent design hazard predicate or a design-router maximality "
                        + "theorem."))),
                DescribeRole.Theorem))));

    private static Formula EligibleUntried() =>
        Call("eligibleUntried", F.Id("eligible"), F.Id("tried"));
}

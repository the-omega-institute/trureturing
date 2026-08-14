using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.Searchability;

internal sealed class SearchableWindowDecisionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A searchable input window gives a Boolean decision for every decidable universal test.",
        H("Searchable Window Decision"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("searchable-window-universal-decision"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/Searchability/SearchableWindowDecision"
                    + ".searchable_window_forall_decidable"),
                H("Searchable windows decide universal Boolean tests"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open,
                    Open, Forall, Sp, F.Id("q"), Comma, Sp,
                    F.Id("C"), Open, Operatorname, Grp(F.Id("select")),
                    Open, F.Id("q"), Close, Close, Close,
                    Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("q"), Comma, Sp,
                    Open, Exists, Sp, F.Id("z"), Comma, Sp,
                    F.Id("C"), Open, F.Id("z"), Close,
                    Sp, Land, Sp, F.Id("q"), Open, F.Id("z"), Close,
                    Sp, Eq, Sp, F.Id("true"), Close,
                    Sp, Rightarrow, Sp,
                    F.Id("q"), Open, Operatorname, Grp(F.Id("select")),
                    Open, F.Id("q"), Close, Close,
                    Sp, Eq, Sp, F.Id("true"), Close,
                    Close, Sp, Rightarrow, Sp,
                    F.Id("p"), Open, F.Id("sut"), Open,
                    Operatorname, Grp(F.Id("select")), Open,
                    Open, F.Id("z"), Sp, Mapsto, Sp, Neg, Sp,
                    F.Id("p"), Open, F.Id("sut"), Open, F.Id("z"),
                    Close, Close, Close, Close, Close, Close,
                    Sp, Eq, Sp, F.Id("true"), Sp, Iff, Sp,
                    Open, Forall, Sp, F.Id("z"), Comma, Sp,
                    F.Id("C"), Open, F.Id("z"), Close,
                    Sp, Rightarrow, Sp,
                    F.Id("p"), Open, F.Id("sut"), Open, F.Id("z"),
                    Close, Close, Sp, Eq, Sp, F.Id("true"), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The search premise supplies a selector for every Boolean query. "
                        + "Its selected point lies in C, and whenever an in-domain point "
                        + "satisfies the query, the selected point satisfies it as well. "
                        + "The system function is total and the output test is Boolean.")),
                    Paragraph(Text(
                        "The decision queries the selector for a counterexample to the test. "
                        + "If one exists, selector completeness makes the chosen test false. "
                        + "If none exists, selector membership makes the chosen test true, "
                        + "which is equivalent to universal truth throughout C.")),
                    Paragraph(Text(
                        "Pinned packages and the repository were searched before proving. "
                        + "The finite-type universal-decision instance does not cover infinite "
                        + "searchable windows, and no selection-functional implementation was "
                        + "found, so the selector laws remain explicit theorem premises.")),
                    Paragraph(Text(
                        "This theorem closes only the finite-decision clause of the source atom. "
                        + "The independent claim that an infinite searchable space exists remains "
                        + "residual and is not asserted here."))),
                DescribeRole.Theorem)),
        []));
}

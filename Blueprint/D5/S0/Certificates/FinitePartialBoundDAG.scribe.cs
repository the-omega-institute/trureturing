using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class FinitePartialBoundDAGDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/FinitePartialBoundDAG.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sound finite DAG replay of actual partial-event lower bounds.",
        H("Every value branch and every symmetry edge is checked"),
        Blocks(
            Paragraph(Text("Each row stores a partial assignment, an integer lower bound and either a complete event or a split with one earlier child for every possible value. Every split checks the recorded parent-to-child lower bound and exact assignment transport under its supplied symmetry. No canonicalization edge or external minimum is trusted.")),
            Describe.Lean(DescribeId.Create("structure-terminals"),
                DeclarationHandle.Create(Prefix + "checked_structure_and_terminals"),
                H("Factoring topology from terminal score calculations"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The structural checker validates every split and requires a terminal row to equal its complete event. Separate actual numerical inequalities for all terminal rows then yield full acceptance by the original checker. This allows the large finite topology to be replayed independently of expensive exact score evaluations, while retaining both obligations."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("lower-bound"),
                DeclarationHandle.Create(Prefix + "checked_rows_lower_bound"),
                H("Every accepted row bounds every compatible completion"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Strong induction over earlier-child indices gives the recorded lower bound for every full event compatible with the row's actual partial assignment. A supplied event action must preserve the actual score, and its corresponding partial action must transport compatibility. Full branch coverage and these earned symmetry premises prevent a discarded completion from being silently omitted."))), DescribeRole.Theorem))));
}

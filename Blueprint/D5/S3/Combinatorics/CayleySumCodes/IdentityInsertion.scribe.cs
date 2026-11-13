using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CayleySumCodes;

internal sealed class IdentityInsertionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CayleySumCodes/IdentityInsertion.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create(
        "D5/L/FiniteGroups/manikandishzhang2026sumcodes");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Identity insertion for subgroup total codes, with the exact simple-graph equality boundary.",
        H("Connection sets and loopless graphs"),
        Blocks(
            Describe.Lean(DescribeId.Create("graph-equality-boundary"),
                DeclarationHandle.Create(Prefix + "graph_eq_iff"), H("When the graph changes"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "If 1 is absent from a finite group's normal connection set Y, inserting it "
                    + "preserves the simple sum graph precisely when g*g=1 for every ambient "
                    + "element g. Otherwise the distinct vertices g and g inverse gain an edge. "
                    + "In an exponent-at-most-two group insertion adds only excluded loops. "
                    + "The revised source says another connection set, repairing the original "
                    + "version's unconditional another-graph wording."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("code-preservation"),
                DeclarationHandle.Create(Prefix + "result"), H("Preserving the subgroup code"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "If the squares of H form the singleton {1}, H is a total perfect code for "
                    + "Y union {1} if and only if it is a total perfect code for Y. No restriction "
                    + "on ambient squares outside H is assumed. Any new product g*h=1 with "
                    + "h in H forces g=h, so it contributes only an excluded loop. "
                    + "This preserves all code incidences even if other graph edges change. "
                    + "The square-set-two conversion and general regular classifications "
                    + "remain separate source statements."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/CayleySumCodes/TotalPerfectCriterion"))]));
}

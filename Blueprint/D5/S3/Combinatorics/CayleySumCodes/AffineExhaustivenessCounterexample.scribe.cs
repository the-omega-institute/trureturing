using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CayleySumCodes;

internal sealed class AffineExhaustivenessCounterexampleDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CayleySumCodes/AffineExhaustivenessCounterexample.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create(
        "D5/L/FiniteGroups/manikandishzhang2026sumcodes");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "AffineExhaustivenessCounterexample in the actual loopless sum graphs.",
        H("Retained constructions and exact corrected examples"),
        Blocks(
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"), H("A connected counterexample to the old affine total-code list"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The full affine group over F3, its multiplicative complement, and identity-plus-negations connection give a connected total code excluded from the retained multiplier-transversal list. Every listed connection omits the identity. The general AffineExamples results also supply the distinct full F5 disconnected example by exact application. Neither example refutes the retained sufficient constructions or the perfect-code classification parts. No replacement exhaustive classification is claimed."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/CayleySumCodes/AffineExamples"))]));
}

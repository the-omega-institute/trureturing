using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CayleySumCodes;

internal sealed class DihedralOldNecessityCounterexampleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dihedral necessity counterexample", H("Actual finite-group refutation"),
        Blocks(Describe.Lean(DescribeId.Create("dihedraloldnecessitycounterexample-refutation"),
            DeclarationHandle.Create("D5/S3/Combinatorics/CayleySumCodes/DihedralOldNecessityCounterexample.result"),
            H("The source counterexample"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                "D5/L/FiniteGroups/manikandishzhang2026sumcodes")),
            Blocks(Paragraph(Text("The source Example2.3(2) uses the actual DihedralGroup4 of order8, H=G and the normal connection set {1,a squared}. Center and square set are exactly those two elements; the loopless sum graph is a perfect matching. Both possible normal transversals of G in itself consist of squares. This is the full second source counterexample to the old necessity, with no claim against its surviving sufficient direction."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/CayleySumCodes/TotalPerfectCriterion")),
         DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/CayleySumCodes/QuaternionDihedralCounterexamples"))]));
}

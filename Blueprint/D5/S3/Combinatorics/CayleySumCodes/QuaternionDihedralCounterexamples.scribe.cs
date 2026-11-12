using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CayleySumCodes;

internal sealed class QuaternionDihedralCounterexamplesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quaternion necessity counterexample", H("Actual finite-group refutation"),
        Blocks(Describe.Lean(DescribeId.Create("whole-group-normal-transversal-squares"),
            DeclarationHandle.Create("D5/S3/Combinatorics/CayleySumCodes/QuaternionDihedralCounterexamples.whole_transversal_squares"),
            H("The shared whole-group argument"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                "D5/L/GraphInvariants/Nikandish/manikandishzhang2026sumcodes")),
            Blocks(Paragraph(Text("For any actual group whose center consists of squares, every normal transversal of the whole group consists of squares. This is consumed by both the quaternion and dihedral necessity refutations; it does not impose an order-eight hypothesis."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quaterniondihedralcounterexamples-refutation"),
            DeclarationHandle.Create("D5/S3/Combinatorics/CayleySumCodes/QuaternionDihedralCounterexamples.result"),
            H("The source counterexample"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                "D5/L/GraphInvariants/Nikandish/manikandishzhang2026sumcodes")),
            Blocks(Paragraph(Text("The source Example2.3(1) uses every element of QuaternionGroup2, H=G and the normal connection set {1,-1}. Its exact center and square set are both {1,-1}; every vertex has one distinct neighbor. Every normal transversal of G in itself is a singleton central element, hence a square. The actual matching therefore refutes the old singleton-nonsquare necessity. The surviving sufficiency and the separate dihedral and proper-normal examples remain distinct. No new classification is inferred."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/CayleySumCodes/TotalPerfectCriterion"))]));
}

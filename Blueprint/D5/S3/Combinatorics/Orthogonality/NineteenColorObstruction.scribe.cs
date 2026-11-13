using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Orthogonality;
internal sealed class NineteenColorObstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original seven-dimensional written lower-bound proof.",
        H("NineteenColorObstruction"),
        Blocks(Describe.Lean(DescribeId.Create("law-0"), DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/NineteenColorObstruction.result"), H("result"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuadraticForms/binarysubspace2026complete")), Blocks(Paragraph(Text("The entire original126-line domain, all minimum-vector classes, and the universal quadratic and hole argument. Every finite identity is an ordinary kernel check with full-domain soundness. The written lower bound is distinct from the paused19-color case exclusions, exactn7 remains open, and no upper bound is asserted."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Orthogonality/SevenBitCapacity")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Orthogonality/PartialSpreadHoles")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Orthogonality/SevenBitParity"))]));
}

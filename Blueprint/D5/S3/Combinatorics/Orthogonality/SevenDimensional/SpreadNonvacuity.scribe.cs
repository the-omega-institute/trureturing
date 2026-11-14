using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Orthogonality.SevenDimensional;
internal sealed class SpreadNonvacuityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original trace spread supplies full actual inputs to unique completion.", H("Spread nonvacuity"),
        Blocks(
            Describe.Lean(DescribeId.Create("claim"), DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SevenDimensional/SpreadNonvacuity.claim"), H("The claimed empty input domain"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuadraticForms/binarysubspace2026complete")), Blocks(Paragraph(Text("This is the absence of every actual eight-member family of finrank-three totally isotropic coordinate Submodules with pairwise zero intersection."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SevenDimensional/SpreadNonvacuity.result"), H("The actual input domain is nonempty"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuadraticForms/binarysubspace2026complete")), Blocks(Paragraph(Text("The supplied F8 trace construction gives an explicit original family. All complete finite carriers and incidence data are kernel checked and realized as actual Submodules. This nonvacuity witness does not replace the universal theorem."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Orthogonality/SevenDimensional/ActualSpreadCompletion"))]));
}

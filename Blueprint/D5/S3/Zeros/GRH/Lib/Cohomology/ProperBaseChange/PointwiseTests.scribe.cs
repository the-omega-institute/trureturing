using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Cohomology.ProperBaseChange;

internal sealed class PointwiseTestsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pointwise Tests", H("Pointwise Tests"),
        Blocks(
            Paragraph(Text("Proper base change with supports: classes detected on geometric points, field-extension invariance.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Cohomology/ProperBaseChange/PointwiseTests.isDetectedAtPoints_of_proper"),
                H("isDetectedAtPoints_of_proper"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Proper base change: ℓ invertible in A, X proper over ℤ. On pairs (test over A, point of X), if β from locally constant ℤ/ℓ-valued functions to F is bijective where I vanishes, and this locus is dense for F, then F satisfies IsDetectedAtPoints.")))))));
}

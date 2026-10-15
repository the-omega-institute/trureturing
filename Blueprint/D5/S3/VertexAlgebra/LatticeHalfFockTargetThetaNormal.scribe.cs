using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockTargetThetaNormalDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Labelled normal tuple target reflection",
        H("Labelled normal tuple target reflection"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("latticehalffocktargetthetanormal-sigma-current"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockTargetThetaNormal.sigma_current"),
                H("All half-current modes anticommute"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The original negative creation branch and nonnegative Gram-weighted derivative branch both anticommute with sigma."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticehalffocktargetthetanormal-sigmatensor-jetcurrent"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockTargetThetaNormal.sigmaTensor_jetCurrent"),
                H("Every jet has the same target sign"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The actual jetScalar is unchanged. No additional derivative-order sign is inserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticehalffocktargetthetanormal-sigmatensor-flatcoefficient"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockTargetThetaNormal.sigmaTensor_flatCoefficient"),
                H("Every original labelled tuple"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("Recursion retains the original occurrence list, each signed mode and its original left or right placement. The covariance factor is exactly minus one to the word length, including repeated occurrences."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticehalffocktargetthetanormal-sigmatensor-normalword"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockTargetThetaNormal.sigmaTensor_normalWord"),
                H("Finite original normal-word supports"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The checked flatTerm_finite supplier supports the additive map and scalar finsum operations on both sides. No sampled tuple or replacement finite carrier is used."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticehalffocktargetthetanormal-sigmatensor-normalpolynomial"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockTargetThetaNormal.sigmaTensor_normalPolynomial"),
                H("Every target and source polynomial"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The original monomial basis and complete occurrence words extend the tuple identity to all original polynomials."))),
                DescribeRole.Theorem))));
}

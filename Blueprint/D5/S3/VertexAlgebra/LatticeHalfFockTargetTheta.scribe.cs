using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockTargetThetaDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All original Ytw target conjugation",
        H("All original Ytw target conjugation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("latticehalffocktargettheta-corr-reflection"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockTargetTheta.Corr_reflection"),
                H("The original finite correction reflection"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The explicit checked private Corr_sign consumer retains its auxiliary sigmaHat proof. The none coordinate is fixed, some coordinates are negated, and all singleton, pair and derivation signs remain the original ones."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticehalffocktargettheta-sigmatensor-correctionsum"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockTargetTheta.sigmaTensor_correctionSum"),
                H("Every finite correction shift"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The actual Finsupp.lsum is transported shift by shift. Each exponent is shifted by exactly e plus twice the shift, with no invented shift sign."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticehalffocktargettheta-sigmatensor-correctedpolynomial"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockTargetTheta.sigmaTensor_correctedPolynomial"),
                H("Original corrected charged source"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The unchanged finite Corr coefficients and normalPolynomial conjugation are assembled on arbitrary target states."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticehalffocktargettheta-ytw-target-theta"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockTargetTheta.Ytw_target_theta"),
                H("All-source all-target conjugation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("For every original lattice datum, determinant-unit witness, source, integer coefficient exponent and target, target sigmaTensor intertwines Ytw with the original source theta. No inverse Gram matrix, rank, positivity, cutoff or Jacobi hypothesis is used. Source-coordinate monodromy is not substituted for this target identity."))),
                DescribeRole.Theorem))));
}

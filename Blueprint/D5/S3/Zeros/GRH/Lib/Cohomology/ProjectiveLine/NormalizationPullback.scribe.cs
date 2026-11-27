using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Cohomology.ProjectiveLine;

internal sealed class NormalizationPullbackDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalization Pullback", H("Normalization Pullback"),
        Blocks(
            Paragraph(Text("Projective line formula for tilted O/p coefficients via a left inverse of cup with η. Projective line formula for mod-l cohomology over bases mapping to fields or C_p. Loci keeping coincidences among finitely many maps to a proper functor form a cover. Comparison property for opens of affine space in (P¹)^d and standard étale charts. Pull-back along a finite linear projection to projective space is injective (transfer).")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Cohomology/ProjectiveLine/NormalizationPullback.pullback_injective"),
                H("pullback_injective"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let L embed Y, g be coordinates of a field point, Λ a Noether normalisation of g. If O ⊂ Γ ⊂ Y × P^d contains (x,[Λ(v)]) whenever coordinates v of x satisfy the homogeneous equations of g, pull-back along O → P^d is injective on H^n on p-adic tests with coefficient genericCoeff.")))))));
}

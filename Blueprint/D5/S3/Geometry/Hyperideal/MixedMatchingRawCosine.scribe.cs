using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class MixedMatchingRawCosineDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The symmetric six-variable hyper-ideal cosine reduces to the radial closed form used by mixed matching.",
        H("Mixed matching raw cosine reduction"),
        Blocks(
            Paragraph(Text(
                "For the symmetric six-variable generalized length vector (r,t,t,o,t,t), "
                + "the original six-variable cosine formula reduces to the radial expression "
                + "used in the mixed matching construction.")),
            Describe.Lean(
                DescribeId.Create("mixed-matching-raw-cosine"),
                DeclarationHandle.Create(
                    "D5/S3/Geometry/Hyperideal/MixedMatchingRawCosine.raw_cosine_formula"),
                H("Radial raw cosine formula"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For r>1 and t>0, define Q=2*t^2/(r-1). The six-variable "
                        + "cosine at (r,t,t,o,t,t) equals (Q-o)/(Q+1).")),
                    Paragraph(Text(
                        "The proof factors the numerator and both equal radicands, "
                        + "then cancels the positive common factor and square root.")),
                    Paragraph(Text(
                        "This is an algebraic raw-formula reduction. It does not assert "
                        + "genuine angle-domain membership or construct a face pairing."))),
                DescribeRole.Theorem))));
}

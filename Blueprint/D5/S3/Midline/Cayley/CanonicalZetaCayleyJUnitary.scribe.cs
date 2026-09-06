using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Midline.Cayley;

internal sealed class CanonicalZetaCayleyJUnitaryDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Midline/Cayley/CanonicalZetaCayleyJUnitary.";

    public DocumentDefinition Create()
    {
        return DocumentDefinition.Create(ScribeNode.Create(
            "The diagonal zero Cayley operator preserves the indefinite inner product induced by same-height reflection.",
            H("Canonical zeta Cayley J-unitarity"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("cayley-mirror-coefficient-reciprocity"),
                    DeclarationHandle.Create(Module + "cayleyCoefficient_mirrorIndex"),
                    H("Mirror Cayley coefficients are inverse conjugates"),
                    StatementSource.FromAuthor(Disp(F.Id("c(M rho) = conj(c(rho))^(-1)"))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "This is the coefficient-level consequence of the existing Cayley mirror-coordinate theorem."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("zero-cayley-operator-j-unitary"),
                    DeclarationHandle.Create(Module + "zeroCayleyOperator_j_unitary"),
                    H("The zero Cayley operator is J-unitary"),
                    StatementSource.FromAuthor(Disp(F.Id("U* J U = J"))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Coordinatewise inverse-conjugate coefficients preserve the mirror Krein form, and summation yields the operator identity."))),
                    DescribeRole.Theorem))));
    }
}

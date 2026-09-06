using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Midline.Cayley;

internal sealed class CanonicalZetaCayleyKreinInverseDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Midline/Cayley/CanonicalZetaCayleyKreinInverse.";

    public DocumentDefinition Create()
    {
        return DocumentDefinition.Create(ScribeNode.Create(
            "Mirror symmetry constructs the bounded two-sided inverse of the zero Cayley operator and identifies it with J U-star J.",
            H("Canonical zeta Cayley Krein inverse"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("zero-cayley-invertible-without-rh"),
                    DeclarationHandle.Create(Module + "zeroCayleyOperator_isUnit_unconditional"),
                    H("The zero Cayley operator is unconditionally invertible"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Call("IsUnit", F.Id("U_Z"))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The reciprocal multiplier is bounded by transporting the original bounded coefficients through mirror permutation and conjugation."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("zero-cayley-krein-inverse-formula"),
                    DeclarationHandle.Create(Module + "zeroCayleyKreinInverse_eq_explicit"),
                    H("The explicit inverse equals J U-star J"),
                    StatementSource.FromAuthor(Disp(Seq(
                        F.Id("U_Z^{-1}"), Sp, EqualTo, Sp,
                        F.Id("J_Z U_Z^* J_Z")))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The same proof yields the companion conservation identity U J U-star = J without ordinary unitarity."))),
                    DescribeRole.Theorem))));
    }
}

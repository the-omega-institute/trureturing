using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms.GaussianIntegers;

internal sealed class GaussianIntegerNormDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Gaussian integer times its complex conjugate is its sum-of-two-squares norm.",
        H("Gaussian Integer Norm"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gaussian-integer-conjugate-product-is-its-two-squares-norm"),
                DeclarationHandle.Create(
                    "D5/S3/PrimeForms/GaussianIntegers/GaussianIntegerNorm.gaussian_integer_mul_conj_eq_sq_add_sq"),
                H("The conjugate product is the sum-of-two-squares norm"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("a"), Comma, Sp, F.Id("b"), InMacro,
                    Mathbb, Grp(F.Id("Z")), Comma, Esc,
                    Open, F.Id("a"), Plus, F.Id("b"), F.Id("i"), Close,
                    Open, F.Id("a"), Minus, F.Id("b"), F.Id("i"), Close,
                    Sp, Eq, Sp, F.Id("a"), Caret, D(2), Plus, F.Id("b"), Caret, D(2)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For all integers a and b, embed the Gaussian integer a + bi into the "
                        + "complex numbers. Its product with a - bi, the complex conjugate, is "
                        + "the embedded integer a squared plus b squared.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies Complex.mul_conj and Complex.normSq_apply, so "
                        + "the Lean proof is a thin wrapper around the standard complex norm "
                        + "identity. No claim is made here about constructing the Gaussian integer "
                        + "quotient or the surrounding number-system completion chain."))),
                DescribeRole.Theorem))));
}

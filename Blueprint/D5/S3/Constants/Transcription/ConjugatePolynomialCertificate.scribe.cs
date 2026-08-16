using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.Transcription;

internal sealed class ConjugatePolynomialCertificateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact quartic certificate splits into conjugate golden-radical quadratics.",
        H("A Conjugate Quadratic Certificate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("conjugate-quadratic-product"),
                DeclarationHandle.Create(
                    "D5/S3/Constants/Transcription/ConjugatePolynomialCertificate."
                        + "conjugate_quadratic_product"),
                H("The two conjugate quadratic factors multiply to the exact quartic"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("x"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Esc,
                    F.Id("q"), Underscore, Grp(Plus), Open, F.Id("x"), Close,
                    F.Id("q"), Underscore, Grp(Minus), Open, F.Id("x"), Close, Eq,
                    F.Id("p"), Open, F.Id("x"), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Set q+(x) = x^2 + (-810051203588 + 362265911296 sqrt(5))x "
                            + "+ 55406466168660996 - 24778524949233664 sqrt(5), and let "
                            + "q-(x) be its radical conjugate.")),
                    Paragraph(Text(
                        "Set p(x) = x^4 - 1620102407176 x^3 + 110811693059397656 x^2 "
                            + "+ 84768625708978144 x - 246295300782612464. The Lean theorem "
                            + "certifies q+(x)q-(x) = p(x) for every real x.")),
                    Paragraph(Text(
                        "The proof reuses the pinned Mathlib identity sqrt(5)^2 = 5 and then "
                            + "normalizes the remaining exact ring arithmetic. It asserts only "
                            + "this factorization, not minimality or irreducibility."))),
                DescribeRole.Theorem))));
}

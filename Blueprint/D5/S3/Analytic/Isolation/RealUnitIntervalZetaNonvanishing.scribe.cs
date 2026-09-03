using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Isolation;

internal sealed class RealUnitIntervalZetaNonvanishingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Riemann zeta is nonzero at every positive real point other than one; the open unit interval follows.",
        H("Positive Real-Axis Zeta Nonvanishing"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("riemann-zeta-is-nonzero-on-the-positive-real-axis-away-from-one"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Isolation/RealUnitIntervalZetaNonvanishing."
                        + "riemannZeta_ne_zero_of_real_pos_ne_one"),
                H("Riemann zeta is nonzero at positive real points away from one"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("x"), InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Esc,
                    D(0), Lt, F.Id("x"), Sp, Land, Sp, F.Id("x"), Neq, D(1),
                    Sp, Rightarrow, Sp, F.Zeta, Open, F.Id("x"), Close, Sp, Neq, Sp, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The proof pairs adjacent terms of the alternating Dirichlet series. "
                            + "Uniform convergence on compact subsets of the positive half-plane "
                            + "makes the paired series analytic, and the identity principle "
                            + "identifies it with the eta factor times Riemann zeta.")),
                    Paragraph(Text(
                        "At every positive real argument each adjacent pair is strictly positive. "
                            + "The paired eta series therefore cannot vanish, so its factorization "
                            + "forces the zeta value to be nonzero away from one. This theorem is "
                            + "the public owner of the real-axis family; its eta machinery remains "
                            + "local and introduces no additional named API."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("riemann-zeta-is-nonzero-on-the-open-real-unit-interval"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Isolation/RealUnitIntervalZetaNonvanishing."
                        + "riemannZeta_ne_zero_on_real_unit_interval"),
                H("Riemann zeta is nonzero on the open real unit interval"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("sigma"), InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Esc,
                    D(0), Lt, F.Id("sigma"), Sp, Land, Sp, F.Id("sigma"), Lt, D(1),
                    Sp, Rightarrow, Sp, F.Zeta, Open, F.Id("sigma"), Close, Sp, Neq, Sp, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "This is the direct open-unit-interval corollary of the public positive "
                            + "real-axis theorem: an argument strictly below one is not one."))),
                DescribeRole.Theorem))));
}

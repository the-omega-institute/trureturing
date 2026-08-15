using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Bogoliubov;

internal sealed class BogoliubovNormConservationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Real Bogoliubov coefficients preserve the unit hyperbolic norm.",
        H("Bogoliubov Norm Conservation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("real-bogoliubov-coefficients-preserve-the-unit-norm"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Bogoliubov/BogoliubovNormConservation."
                    + "bogoliubov_norm_conservation"),
                H("Real Bogoliubov coefficients preserve the unit norm"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("r"), InMacro, Mathbb, Grp(F.Id("R")), Comma, Esc,
                    new Formula.Absolute(Seq(
                        Operatorname, Grp(F.Id("cosh")), Open, F.Id("r"), Close)),
                    Caret, Grp(D(2)), Sp, Minus, Sp,
                    new Formula.Absolute(Seq(
                        Operatorname, Grp(F.Id("sinh")), Open, F.Id("r"), Close)),
                    Caret, Grp(D(2)), Sp, Eq, Sp, D(1)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For the standard real squeeze parameter r, alpha = cosh(r) and "
                        + "beta = sinh(r) obey |alpha|^2 - |beta|^2 = 1. Pinned Mathlib "
                        + "provides Real.cosh_sq_sub_sinh_sq, so the Lean proof only rewrites "
                        + "the squared absolute values and applies that identity.")),
                    Paragraph(Text(
                        "This closes only the real Bogoliubov norm-conservation identity in "
                        + "the source atom. It does not formalize its open-channel, Krein, or "
                        + "frustration criteria, nor its adiabatic asymptotic and sudden-quench "
                        + "limit claims."))),
                DescribeRole.Theorem))));
}

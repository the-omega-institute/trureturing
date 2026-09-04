using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.CofinalSupport;

internal sealed class GoldenCofinalKernelCriterionDocument : IScribeDocumentDefinition
{
    private const string Handle =
        "D5/S3/Weil/CofinalSupport/GoldenCofinalKernelCriterion."
            + "golden_cofinal_kernel_criterion";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A cofinal vanishing-scale kernel family is positive semidefinite exactly under RH.",
        H("Golden Cofinal Kernel Criterion"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-cofinal-kernel-criterion"),
            DeclarationHandle.Create(Handle),
            H("Cofinal kernel positivity is equivalent to RH"),
            StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(new Formula.Subscript(F.Id("omega"), F.Id("n")),
                    Sp, Rightarrow, Sp, D(0), Comma),
                Seq(F.Id("RiemannHypothesis"), Sp, Iff, Sp,
                    Forall, Sp, F.Id("n"), Sp, Ge, Sp, D(0), Comma, Sp,
                    Call("PosSemidef", new Formula.Subscript(F.Id("K"),
                        new Formula.Subscript(F.Id("omega"), F.Id("n")))), Dot),
            ]))),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For each scale, positivity means that every finite sampled Gram matrix "
                        + "of the supplied complex kernel is positive semidefinite. The theorem "
                        + "assumes the Hermite-Biehler forward implication and identifies each "
                        + "kernel diagonal with the canonical shifted-xi diagonal value.")),
                Paragraph(Text(
                    "For the reverse implication, a right-half-strip zeta zero determines a "
                        + "positive displacement delta. Since omega_n tends to zero, sampled "
                        + "points approach the zero through a punctured neighborhood. Isolated "
                        + "zeros provide an index where the shifted xi value is nonzero, and the "
                        + "existing one-point formula gives a strictly negative diagonal entry, "
                        + "contradicting positive semidefiniteness.")),
                Paragraph(Text(
                    "The positivity of every omega_n is explicit; it excludes Lean's totalized "
                        + "division at zero in the one-point formula."))),
            DescribeRole.Theorem))));
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Analytic;

internal sealed class NymanOneSidedScalarDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/Analytic/NymanOneSidedScalar";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One-sided Landau continuation for Möbius shells",
        H("One-sided Landau continuation for Möbius shells"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("signal-mellin"),
                DeclarationHandle.Create(Owner + ".signal_mellin"),
                H("Mellin transform of the logarithmic shell signal"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a real kernel W vanishing outside (1, 2), the real logarithmic shell signal uses scale 2 exp(−t). Its Laplace integral over t > 0 multiplied by 2^s equals the Mellin transform of the Möbius dilates of W. The dilates vanish at scales at least 2, so the substitution covers the whole nonzero part of the Mellin integral. The identity uses totalized integrals. For continuous Lipschitz kernels, the Laplace integral converges when Re(s) > 1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-re-le-of-one-sided-signal"),
                DeclarationHandle.Create(Owner + ".zero_re_le_of_one_sided_signal"),
                H("One-sided growth bounds exclude zeta zeros"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let W be a continuous real kernel vanishing outside (1, 2), with Lipschitz constant K ≥ 0. For 0 < β < 1 and c ≠ 0, suppose c times its logarithmic shell signal is eventually at most C exp(βt). Every zeta zero ρ with Re(ρ) < 1 and nonzero Mellin transform of W at ρ then has Re(ρ) ≤ β. After exponential normalization, positive Laplace continuation gives a holomorphic function on Re(s) > β. Multiplying by normalized zeta extends the numerator identity to that half-plane and forces the numerator to vanish at any zero there."))),
                DescribeRole.Theorem))));
}

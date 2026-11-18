using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class OriginalHalfBinomialPfaffNomeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/OriginalHalfBinomialPfaffNome.";

    private static DocumentBlock Result(string id, string declaration, string title, string text,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact Pfaff jumps of the original complementary ratio and its signed charge nome.",
        H("Pfaff Jumps and the Negative Real Nome"),
        Blocks(
            Paragraph(Text(
                "With r = k² the supplier's normalized period is P(r) = 2K(k)/π. "
                + "DLMF 19.7.3b gives the classical reciprocal complementary modulus formula, "
                + "with the upper sign for Im(k²) > 0 and the lower sign for Im(k²) < 0. "
                + "DLMF 22.2.1 fixes the nome convention q = exp(−π K′(k)/K(k)). "
                + "The following proofs use the literal Euler period and its compiled Pfaff "
                + "transformation (DLMF 15.8.1 at a = b = 1/2 and c = 1).")),
            Result("upper-jump", "tau_pfaff_upper", "Exact upper-half-plane jump",
                "For Im r > 0, τ(r) = τ(r/(r − 1)) + 1. The Pfaff period square and "
                + "the chain rule make the difference constant. The map r ↦ 1/(1 − r) "
                + "fixes u = (1 + i√3)/2. Differentiating the reciprocal ratio identity "
                + "there and cancelling the nonzero quotient derivative gives τ(u)² = u². "
                + "The positive imaginary parts give τ(u) = u, and u + 1/u = 1 fixes the addend."),
            Result("lower-jump", "tau_pfaff_lower", "Exact lower-half-plane jump",
                "For Im r < 0, τ(r) = τ(r/(r − 1)) − 1. The Pfaff map interchanges the "
                + "half-planes and is an involution, so the upper identity gives the lower one."),
            Result("signed-nome", "negativeChartNome", "Signed Pfaff nome",
                "At r use minus the exponential of iπτ(r/(r − 1)).",
                DescribeRole.Definition),
            Result("negative-real-extension", "negative_real_nome_extension", "Holomorphic charge factors",
                "Every real x < 0 has an open complex neighborhood on which the signed Pfaff nome "
                + "is holomorphic and has modulus strictly below one. On the overlap with the "
                + "double slit it agrees with exp(iπτ(r)), since both signed unit jumps contribute −1. "
                + "Every natural power extends on the same neighborhood with multiplier (−1)ᵐ "
                + "in the Pfaff chart. This supplies the charge factor at natural charge energy m. "
                + "Full crossing also requires matching the actual source and oscillator factors "
                + "and establishing normal convergence."))));
}

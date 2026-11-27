using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.NullConeGravity;

internal sealed class NullDiamondContour4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondContour4D.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/satishchandransorce2026nulllocal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Horizontal contour translation and exponential Fourier decay of the null-diamond correction.",
        H("Contour shifts of the modular Fourier kernel"),
        Blocks(
            Paragraph(Text("The separately holomorphic modular kernel in the four-dimensional scalar covariance "
                + "problem of Satishchandran and Sorce decays along horizontal lines of a strip. Moving the two "
                + "Fourier contours independently gives enough frequency decay to absorb the inverse quarter-power "
                + "weights of the covariance.")),
            Entry("horizontal-contour-shift", "horizontal_shift", "Horizontal contour shift",
                "Let f be a complex-valued function of a complex variable, B ≥ 0 and d > 0 real, with f "
                + "complex differentiable on the open strip. Suppose for all z in the closed strip that the norm "
                + "of f(z) is at most B exp(−d |Re z|)(1 + |Re z|). For every real y with |y| ≤ b the integral "
                + "of f(r) over the real line equals the integral of f(r + iy) over the real line, with respect "
                + "to Lebesgue measure. Cauchy's rectangle theorem relates the two truncated horizontal integrals "
                + "to the oriented vertical edges. Their norms tend to zero as the rectangle widens, and the "
                + "horizontal integrals converge by the exponentially decaying majorant."),
            Entry("modular-fourier-kernel", "fourierG", "Modular Fourier kernel",
                "For real M, ν, λ and x, the Fourier kernel equals 1/(2π) times the iterated Lebesgue integral "
                + "over r and s in the real line of exp(−iνr + iλs) G_M(r,s,x), integrating over s first.",
                DescribeRole.Definition),
            Entry("fourier-kernel-measurable", "fourierG_measurable", "Joint measurability of the Fourier kernel",
                "For each real M, the Fourier kernel as a function of the real triple (ν,λ,x) is measurable. "
                + "Joint measurability of the integrand and parameterized integration give the conclusion."),
            Entry("fourier-frequency-decay", "fourierG_bound", "Uniform exponential decay in both frequencies",
                "For every real M > 0 there exists a real C > 0 such that for all real ν, λ and x with "
                + "−1 ≤ x < 1, the norm of the Fourier kernel is at most "
                + "C exp(−b(|ν| + |λ|)) (1 + |log(1−x)|). The horizontal shifts use the strip edges with "
                + "imaginary parts opposite in sign to ν and equal in sign to λ, respectively, with either edge "
                + "available at zero frequency. Integrability permits exchange of the "
                + "order of integration. The phase on the translated contours then has norm "
                + "exp(−b(|ν| + |λ|)). The horizontal majorant integrates to a constant times the explicit "
                + "angular factor. Since b = 3/8 exceeds 1/4, the frequency bound permits multiplication by "
                + "exp((|ν| + |λ|)/4) while retaining exponential decay."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), role);
}

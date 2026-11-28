using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence.TraceEntropy;

internal sealed class GibbsCubicTranslationEntropyDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Divergence/TraceEntropy/GibbsCubicTranslationEntropy.";
    private static readonly LibraryNoteRef Wu = LibraryNoteRef.Create("D5/L/SpinModels/wu2026sharp");

    private static DocumentBlock.Describe Result(string id, string declaration, string title, string body) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Wu),
            Blocks(Paragraph(Text(body))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact cubic entropy slopes, their BKM correction, and a scalar Jensen comparison.",
        H("Cubic entropy along Gibbs translations"),
        Blocks(
            Paragraph(Text("Use complex matrices on an arbitrary finite index type, ordinary trace, "
                + "and real spectral functional calculus for the matrix logarithm. Put T = Re Tr(M³). "
                + "The entropy at M with fixed reference cube B³ is Re Tr(M³(log M³ − log B³)) − T log T. "
                + "The translation is M + sB. Write J = Re Tr((BM² − MBM) log B).")),
            new DocumentBlock.Section(H("Derivative of the actual entropy"), Blocks(
                Result("two-sided-derivative", "hasDerivAt_cubicEntropy", "Two-sided derivative",
                    "For positive definite B and M the derivative at s = 0 is "
                    + "9 Re Tr(BM²(log M − log B)) − 3 Re Tr(BM²) log T + 3J. "
                    + "The cube derivative is BM² + MBM + M²B. In the pairing with log M, "
                    + "cyclicity makes the three terms equal. In the pairing with log B the two outer "
                    + "terms agree, and the middle term gives the correction. Differentiating T log T "
                    + "cancels the identity contribution from trace entropy. The formula allows arbitrary "
                    + "trace of B³."),
                Result("right-derivative", "hasDerivWithinAt_cubicEntropy", "Right derivative on the positive boundary",
                    "For positive definite B and positive semidefinite M the same coefficient is the "
                    + "derivative at zero within s ≥ 0. The function x² log x extends continuously at zero "
                    + "with value zero and supplies the boundary limit. The zero matrix has right slope zero "
                    + "by cubic scaling along the Gibbs ray."))),
            new DocumentBlock.Section(H("The noncommuting correction"), Blocks(
                Result("correction-spectral", "correction_spectral", "Correction in a reference eigenbasis",
                    "For Hermitian B and M, write bᵢ for the eigenvalues of B and U for M in the chosen "
                    + "orthonormal eigenbasis of B. Then J is half the sum over i,j of "
                    + "(bᵢ − bⱼ)(log bᵢ − log bⱼ)|Uᵢⱼ|². The expression allows repeated eigenvalues "
                    + "and uses the Lean real logarithm on the whole real line."),
                Result("correction-bkm", "correction_eq_bkm", "BKM pairing of the logarithmic commutator",
                    "For positive definite B and Hermitian M, set C = (log B)M − M(log B). "
                    + "Then J = ½ Re Tr(Cᴴ Ω_B(C)), with Ω_B the actual integral of "
                    + "B^t C B^(1−t) over 0 ≤ t ≤ 1. The logarithmic mean on each reference "
                    + "eigenvalue pair converts the squared log difference to the spectral weight above."),
                Result("correction-nonnegative", "correction_nonneg", "Nonnegative correction",
                    "For positive definite B and Hermitian M, the spectral weights are nonnegative "
                    + "by monotonicity of the logarithm on positive numbers, so J ≥ 0."),
                Result("correction-commutation", "correction_eq_zero_iff_commute", "Equality and commutation",
                    "For positive definite B and Hermitian M, J = 0 exactly when BM = MB. "
                    + "The positive weights between distinct eigenvalues force the corresponding entries "
                    + "to vanish at equality. Entries within a repeated eigenspace are unrestricted."))),
            new DocumentBlock.Section(H("Scalar comparison in the actual spectral pair"), Blocks(
                Paragraph(Text("Let mⱼ be the eigenvalues of M and let wᵢⱼ be the squared overlaps of "
                    + "the respective eigenvectors of B and M. For positive definite B, the "
                    + "Nussbaum–Szkoła reference weights of the cube pair are πᵢⱼ = bᵢ³wᵢⱼ. "
                    + "The ratios xᵢⱼ = mⱼ/bᵢ are the cube roots of the corresponding eigenvalue ratios.")),
                Result("right-spectral-derivative", "hasDerivWithinAt_cubicEntropy_spectral_pair",
                    "Spectral expression for the right derivative",
                    "For positive definite B and positive semidefinite M, the right slope is "
                    + "9 Σ πx² log x − 3 (Σ πx²) log(Σ πx³) + 3J. Entries with zero overlap or "
                    + "zero mⱼ contribute zero to the weighted sums. The reference cube may have any trace."),
                Result("spectral-jensen-comparison", "hasDerivAt_cubicEntropy_spectral_pair",
                    "Exact Jensen deficit of the scalar slope",
                    "For positive definite B and M with Re Tr(B³) = 1, all x are positive. The "
                    + "weights π are nonnegative, sum to one, and vanish exactly on zero overlap. "
                    + "Set S = Re Tr(BM²), T = Re Tr(M³), and ν = πx²/S. Both traces are positive. "
                    + "The nonnegative weights ν sum to one, as do πx³/T. Under ν the mean of x is "
                    + "T/S and the mean of log x is Re Tr(BM²(log M − log B))/S. Put "
                    + "H = Σ πx² log(x²) − S log S and Δ = log(Σ νx) − Σ ν log x. The two-sided "
                    + "derivative is 3(H + J − SΔ), so 3(H + J) bounds the slope above. "
                    + "The Jensen deficit Δ is nonnegative and is strictly positive exactly when "
                    + "two pairs with nonzero π have distinct x."))),
            new DocumentBlock.Section(H("Use in the Wu cubic translation argument"), Blocks(
                Paragraph(Text("In the two-mode CAR specialization of Wu v1, Remark 3.15, equation (3.54), "
                    + "take the Gibbs density D, G = D^(1/6), B = G², and M = GXG. The translation "
                    + "X + sI becomes M + sB, and B³ = D identifies the entropy above with the "
                    + "entropy term of the cubic deficit. The separate WuCubicTranslationEnergy result "
                    + "gives the energy slope in degree-weighted signed thermal coordinates.")),
                Paragraph(Text("In the occupation basis the correction uses the same Gibbs eigenvalue "
                    + "ratios that determine the signed charge blocks of the energy slope. Each weight "
                    + "is the product of a Gibbs eigenvalue difference and its log ratio. It vanishes "
                    + "at the tracial reference and on equal-weight blocks at every temperature. "
                    + "Near the tracial reference the exact weights isolate the part of the entropy "
                    + "slope to be controlled on the noncommuting directions, while the scalar "
                    + "comparison retains the signed contribution −3SΔ.")))))));
}

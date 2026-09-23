using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.Moments;

internal sealed class CatalanSquareHankelLimitsDocument : IScribeDocumentDefinition
{
    private const string Result =
        "D5/S3/Constants/Moments/CatalanSquareHankelLimits.catalan_square_hankel_log_limits";
    private static readonly LibraryNoteRef Kotesovec =
        LibraryNoteRef.Create("D5/L/Recurrence/kotesovec2016a277829a278770");
    private static readonly LibraryNoteRef Lin =
        LibraryNoteRef.Create("D5/L/Recurrence/lin2018catalanpowers");
    private static readonly LibraryNoteRef Simon =
        LibraryNoteRef.Create("D5/L/Recurrence/simon2007equilibrium");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both Kotesovec squared-Catalan Hankel conjectures have logarithmic rate two times log two.",
        H("Squared-Catalan Hankel Limits"),
        Blocks(Describe.Lean(
            DescribeId.Create("a277829-a278770-logarithmic-limits"),
            DeclarationHandle.Create(Result),
            H("The two literal OEIS limits"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Kotesovec, Lin, Simon),
            Blocks(
                Paragraph(Text(
                    "The theorem is one conjunction with no hypotheses. Its first component is "
                        + "the A277829 shift r=1 and its second is the A278770 shift r=2. In "
                        + "both components n ranges over all natural sizes, the size-zero "
                        + "determinant is one, and the limiting value is exactly 2*log(2).")),
                Paragraph(Text(
                    "The upper half of the squeeze comes from the monic Chebyshev-T bounds in "
                        + "the supporting Growth module. Positivity makes every logarithm and "
                        + "monotonicity step legitimate, including the two literal shifts.")),
                Paragraph(Text(
                    "For the lower half, fix 0<delta<8. On a compact central rectangle the two "
                        + "scaled beta densities have one positive lower constant independent of "
                        + "n. Measure domination transfers polynomial energy from the uniform "
                        + "rectangle to the product beta measure while retaining the weight for "
                        + "shift r.")),
                Paragraph(Text(
                    "Chebyshev-U orthogonality is proved and transported to the central "
                        + "interval. The resulting monic polynomials have exact squared norms. "
                        + "After normalizing the changed product functions, the proof bounds the "
                        + "full Gram quadratic form below by a scalar identity matrix. It then "
                        + "uses the positive-semidefinite remainder and all principal minors to "
                        + "obtain the determinant bound; this is not a diagonal-only argument.")),
                Paragraph(Text(
                    "One constant C>0, independent of n, yields for r=1 and r=2 the lower factor "
                        + "(C*delta^r)^n, the factor ((8-delta)*pi/2)^n, and the quadratic factor "
                        + "((8-delta)/2)^(n*(n-1)). Exact logarithmic rate calculations for the "
                        + "lower and upper products, followed by delta tending to zero, squeeze "
                        + "both limits to log(4)=2*log(2).")),
                Paragraph(Text(
                    "Lin's Catalan product density together with Simon's regular-measure and "
                        + "capacity theorems gives a separate ordinary classical corollary. The "
                        + "Lean proof recorded here is the explicit beta, Gram, Chebyshev and "
                        + "quadratic-form derivation, not a formalization of that literature "
                        + "corollary. The bounded prior audit supports only the two named OEIS "
                        + "settlements and makes no worldwide priority or publication claim."))),
            DescribeRole.Theorem,
            new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("oeis-a277829-a278770-catalan-square-hankel-limits"),
                ResolutionKind.Proved)))));
}

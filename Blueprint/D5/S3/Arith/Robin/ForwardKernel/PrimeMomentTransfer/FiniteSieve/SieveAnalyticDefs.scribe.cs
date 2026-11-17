using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve;

internal sealed class SieveAnalyticDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveAnalyticDefs.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Real finite-sieve weights and smoothed interval assumptions",
        H("Real finite-sieve weights and smoothed interval assumptions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sieve-weighted-sum"),
                DeclarationHandle.Create(Prefix + "sieveWeightedSum"),
                H("sieve weighted sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a positive modulus Q, real scale H and real weight f, the weighted sieve sum is the sum over natural shifts d of f(d/H) times the centered coprimality variable at d. The sum uses the finite-support summation convention."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sieve-scale"),
                DeclarationHandle.Create(Prefix + "sieveScale"),
                H("sieve scale"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At a real scale H, the common normalization is the nonnegative square root of H log H."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sieve-norm4"),
                DeclarationHandle.Create(Prefix + "sieveNorm4"),
                H("sieve norm4"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The fourth norm of a real residue function is the fourth root of its fourth absolute moment under the uniform average modulo Q."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sieve-uniform-measure"),
                DeclarationHandle.Create(Prefix + "sieveUniformMeasure"),
                H("sieve uniform measure"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The uniform residue measure is counting measure on ZMod Q multiplied by the reciprocal of the positive modulus Q."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sieve-product-moment"),
                DeclarationHandle.Create(Prefix + "sieveProductMoment"),
                H("sieve product moment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The product moment of a finite family of real residue functions is the uniform expectation of their pointwise product."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sieve-wick-pairing"),
                DeclarationHandle.Create(Prefix + "sieveWickPairing"),
                H("sieve wick pairing"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For four real residue functions, the Wick pairing is the sum of the three products of second moments associated with the three pair partitions."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sieve-wick-defect"),
                DeclarationHandle.Create(Prefix + "sieveWickDefect"),
                H("sieve wick defect"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For four real residue functions, the fourth Wick defect is their product moment minus their Wick pairing."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("normalized-interval-sum"),
                DeclarationHandle.Create(Prefix + "normalizedIntervalSum"),
                H("normalized interval sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The normalized sharp interval sum is the centered sieve sum over the natural shifts in (aH,bH], divided by the square root of H log H."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("normalized-weighted-sum"),
                DeclarationHandle.Create(Prefix + "normalizedWeightedSum"),
                H("normalized weighted sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The normalized weighted sum is the weighted centered sieve sum divided by the square root of H log H."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("msfinite"),
                DeclarationHandle.Create(Prefix + "MSFinite"),
                H("msfinite"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Montgomery–Soundararajan Theorem 1 supplies the assumed scalar second-moment bound and fourth-moment Wick error. In the paper's normalisation, equations (11) and (15) give m_k = Q(φ(Q)/Q)^k V_k and E[(Σ Y_d)^k] = V_k, where the sum runs over 1 ≤ d ≤ n and Y_d is the centered coprimality variable used here; E is the uniform expectation modulo Q. Two nonnegative constants are independent of every positive modulus Q and natural length n at least one. Writing P=Q/φ(Q), the variance estimate in the proof of Theorem 1 (pp. 11–12) gives variance at most C2 n P, and the fourth-moment error is at most C4 n^(2-1/28) P^18."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sieve-smoothing-bump"),
                DeclarationHandle.Create(Prefix + "sieveSmoothingBump"),
                H("sieve smoothing bump"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive delta, the real smooth bump is centered at twice delta, with inner radius delta/2 and outer radius delta."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("smoothing-kernel"),
                DeclarationHandle.Create(Prefix + "smoothingKernel"),
                H("smoothing kernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive delta, the smoothing kernel is the real bump centered at twice delta, divided by its integral with respect to Lebesgue measure."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("smoothed-interval"),
                DeclarationHandle.Create(Prefix + "smoothedInterval"),
                H("smoothed interval"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive delta, the smoothed interval indicator at x is the integral of the smoothing kernel at r times the indicator of (a+r,b+r] at x."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("kuperberg-smoothed"),
                DeclarationHandle.Create(Prefix + "KuperbergSmoothed"),
                H("kuperberg smoothed"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume Kuperberg Theorem 1.3 specialised to the fixed real smoothed interval indicators, in finite-sieve expectation coordinates. The assumed weighted identity is V_k(Q, h; f) = E ∏_i X_{f_i}, where f is the family of smoothed weights, X_{f_i} = sieveWeightedSum Q h f_i and E is the uniform expectation modulo Q; this identifies Kuperberg's weighted moments with the finite-sieve expectation. For each positive delta and each fixed ordered nonnegative endpoint family, nonnegative constants independent of squarefree Q and natural h at least three bound the cubic moment by C h^(3/2-1/21) P^(19/2) and the fourth Wick defect by C h^(2-1/28) P^18, respectively. Here P=Q/φ(Q). Fourier admissibility of the smoothed weights and the Ramanujan coordinate identity are not proved here."))),
                DescribeRole.Definition))));
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class PhysicalPrimeTwoCutoffDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform bounds and complete two-cutoff coefficient tails for the original physical compression and finite symmetric prime action.",
        H("Physical prime two-cutoff estimates"),
        Blocks(
            Paragraph(Text("The coefficients are actual integrals of the original zero-extension compression on Ioc(-a,a]. A complex head has natural modes 0 through N and arbitrary complex coefficients v. The prime cutoff floor(exp(2*a)) is arithmetic and distinct from both mode cutoffs N and M. This module derives coefficient bounds from the actual matrixEntry, rather than taking an entry-decay supplier as a hypothesis. The later L2 and full original AE-even identifications belong to PhysicalCosineTailProjection, OriginalEvenCosineComplete and OriginalEvenExterior.")),
            Describe.Lean(
                DescribeId.Create("actual-offdiagonal"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/PhysicalPrimeTwoCutoff.matrixEntry_offdiagonal"),
                H("Off-diagonal formula for the actual physical pairing"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The assumptions are a>0, natural n<m and real s with abs(s)<=2*a. The formula has sign (-1)^(n+m+1), the original amplitudes, numerator omega_n*sin(omega_n*abs(s))-omega_m*sin(omega_m*abs(s)), and denominator omega_n^2-omega_m^2. Natural separation makes both difference and sum frequencies nonzero. The constant mode n=0, s=0 and the support boundary abs(s)=2*a are included. The original sinc formula, rather than a resonant division, handles the underlying matrix in general."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-uniform-bound"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/PhysicalPrimeTwoCutoff.matrixEntry_uniform_bound"),
                H("Uniform bound for every real shift"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a>0 and natural n<m, the absolute pairing is bounded by 1/(pi*(m-n)) for every real s. Within support, frequency normalization reduces the exact formula to the existing coefficient_bound, and the amplitude factor a*amplitude_n*amplitude_m is at most one, including n=0. Outside support the original physical matrix is zero. Both signed shifts and both touching endpoints are covered without an extra premise on s."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("head-mass"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/PhysicalPrimeTwoCutoff.headMass"),
                H("Mass of the finite complex head"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The sum of norm(v(n))^2 over range(N+1) includes the zero mode and the natural endpoint N. It is nonnegative for every complex v. Under a>0 it becomes the squared norm of the original L2 cosine head in the separate carrier construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("shift-coefficient"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/PhysicalPrimeTwoCutoff.shiftCoefficient"),
                H("Actual compressed-shift coefficient"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This is pairing(a,s,mode_m,profile(a,range(N+1),v)), with the real mode cast into complex values. The inner zero extension precedes translation and the outer compression restricts to the original Ioc window. Integrability follows from continuous factors on bounded overlap. No abstract projection or input matrix is used in this definition."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("shift-row-expansion"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/PhysicalPrimeTwoCutoff.shiftCoefficient_eq"),
                H("Exact complex row expansion"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a>0, natural N and m, arbitrary complex v and arbitrary real s, finite integral linearity and matrix symmetry give the sum of v(n) times the original real matrixEntry(a,n,m,s), cast into complex values. The equality does not require N<m. It keeps the full complex sum; squaring its norm retains mixed terms."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("shift-coefficient-square"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/PhysicalPrimeTwoCutoff.shiftCoefficient_sq"),
                H("Separated-mode coefficient estimate"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume a>0, natural N<m, arbitrary complex v and real s. Finite Cauchy-Schwarz bounds the squared coefficient by headMass(N,v)*(N+1)/pi^2 times ((m-N)^(-1))^2. The actual entry estimate is first applied at n<m for each head index n<=N; only then is m-n replaced by the weaker common gap m-N."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("complete-shift-tail"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/PhysicalPrimeTwoCutoff.shift_complete_tail"),
                H("Summability and the complete infinite shift tail"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a>0 and natural N<M, arbitrary complex v and real s, the squared coefficients at M+j+1 are summable for natural j and their actual infinite sum is at most (N+1)/(pi^2*(M-N))*headMass(N,v). The positive gap M-N feeds the existing inverse-square summability and partial-sum estimate. There is no terminal upper tail cutoff and no unproved L2 identification in this coefficient-space theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-mass"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/PhysicalPrimeTwoCutoff.primeMass"),
                H("Exact arithmetic cutoff mass"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("primeMass(a) sums primeWeight(r)=vonMangoldt(r)/sqrt(r) for r in Icc(1,primeCutoff(a)), with primeCutoff(a)=floor(exp(2*a)). The nonnegative weights include all prime powers and the zero weight at r=1. This finite arithmetic cutoff is not either of the natural mode cutoffs N and M."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("symmetric-prime-entry"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/PhysicalPrimeTwoCutoff.symmetricPrimeEntry"),
                H("Original symmetric finite prime matrix entry"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each arithmetic term retains both actual entries at log(r) and -log(r). Under a>0 and n<m, the triangle inequality bounds its absolute value by 2*primeMass(a)/(pi*(m-n)). The factor two comes from the two signed shifts, with no phase averaging, cancellation premise or change of the underlying compressed action."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("prime-coefficient"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/PhysicalPrimeTwoCutoff.primeCoefficient"),
                H("Whole-line coefficient of the actual finite prime action"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The whole-line integral multiplies the real mode_m, cast into complex values, by primeAction at its original arithmetic cutoff on the finite complex profile. The action already contains both zero extensions and is supported in the physical window. This definition does not presume an orthogonal projection."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("prime-coefficient-shifts"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/PhysicalPrimeTwoCutoff.primeCoefficient_eq_shifts"),
                H("Exact integral bridge to both signed shifts"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary real a, natural N and m and complex v, the coefficient is the finite weighted sum of the two shiftCoefficient values at log(r) and -log(r). No a>0 or mode-separation hypothesis is present in this equality. Bounded overlap and continuity justify moving the finite arithmetic sum and both shifts through the integral."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-row-expansion"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/PhysicalPrimeTwoCutoff.primeCoefficient_eq"),
                H("Exact original prime row expansion"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a>0, arbitrary natural N and m and complex v, the actual integral equals the finite sum of v(n) times symmetricPrimeEntry(a,n,m), cast into complex values. There is no N<m requirement in this identity. Multiplication by conjugated head coefficients and summation would retain all mixed complex terms; the formula does not discard them."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("complete-prime-tail"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/PhysicalPrimeTwoCutoff.prime_complete_tail"),
                H("Complete two-cutoff tail of the actual symmetric prime action"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Assume a>0 and natural N<M, with arbitrary complex v. The squared primeCoefficient values at every natural mode M+j+1 are summable, and their infinite sum is at most 4*primeMass(a)^2*(N+1)/(pi^2*(M-N))*headMass(N,v). The row bound uses the exact symmetric prime entry and finite Cauchy-Schwarz, then the same positive-gap inverse-square tail comparison. Squaring the two-shift allowance gives the factor four. No real-coefficient restriction or positive input moment is imposed.")),
                    Paragraph(Text("These are standard product-to-sum, normalization, triangle, Cauchy-Schwarz and summable-series comparisons applied to the original finite prime action. They supply analytic coefficient estimates, with no literature novelty, canonical full Weil arithmetic/operator identification, signed positivity or Riemann-hypothesis conclusion claimed."))),
                DescribeRole.Theorem))));
}

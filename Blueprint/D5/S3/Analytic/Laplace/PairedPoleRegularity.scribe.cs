using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Laplace;

internal sealed class PairedPoleRegularityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Laplace/PairedPoleRegularity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Removing finitely many paired spectral poles gives a holomorphic regular part with polynomial boundary control.",
        H("Regularity after subtracting paired poles"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pole-bound"),
                DeclarationHandle.Create(Prefix + "pole_bound"),
                H("Paired pole comparison"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If the complex argument has norm at most three quarters of the ordinate, pairing the two opposite poles bounds its term by 32 times the norm times multiplicity divided by ordinate squared."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pole-term-differentiable-at"),
                DeclarationHandle.Create(Prefix + "poleTerm_differentiableAt"),
                H("Differentiability away from the two poles"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A paired pole term is complex differentiable at any point where both denominators are nonzero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pole-sum-split"),
                DeclarationHandle.Create(Prefix + "pole_sum_split"),
                H("Splitting the paired series"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The summable paired series equals its finite cutoff sum plus the complementary tail, with totalized reciprocals at poles."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cut-complement"),
                DeclarationHandle.Create(Prefix + "cutoff_complement"),
                H("Reindexing the complementary spectral tail"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The indices outside the finite spectral cutoff at T are in bijection with the indices whose ordinates are strictly greater than T."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("pole-tsum-summable"),
                DeclarationHandle.Create(Prefix + "poles_summable"),
                H("Absolute summability of paired poles"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a positive spectrum with logarithmic counting asymptotics, away from the poles the paired series is summable. At a pole the Lean expression uses the convention 1/0 = 0."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("regular-part-differentiable-on"),
                DeclarationHandle.Create(Prefix + "regularPart_differentiableOn"),
                H("Holomorphic regular part"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let a locally finite positive spectrum, with positive integral multiplicities, "
                    + "have counting function asymptotic to T log(T)/(2 pi). Suppose a Laplace "
                    + "transform has the prescribed paired pole expansion with holomorphic remainder J "
                    + "on the strip from -eta to 1, where 0<eta<1/5. For M>=1, subtract all poles "
                    + "whose positive ordinate is at most 2M. The resulting regular part is holomorphic "
                    + "on abs(Re(s))<eta and abs(Im(s))<M+1. Pairing opposite poles supplies an "
                    + "inverse-square summable majorant for large cutoffs. For cutoffs between one and four, a finite pole correction to cutoff four remains holomorphic on this rectangle."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("laplace-finite-poles-regular"),
                DeclarationHandle.Create(Prefix + "laplace_eq_finite_poles_add_regular"),
                H("Exact finite pole decomposition"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under the same counting and paired Laplace assumptions, for every M>=1 "
                    + "and every s with 1/2<Re(s)<1, the Laplace transform equals minus one half "
                    + "of the finite sum of paired pole terms with ordinate at most 2M, plus the "
                    + "regular part. Absolute summability of the paired series justifies splitting "
                    + "the full series into the finite cutoff and its complementary tail."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("regularized-boundary-bound"),
                DeclarationHandle.Create(Prefix + "regularized_boundary_bound"),
                H("Polynomial control of boundary values and derivatives"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume additionally that J has polynomial growth of degree k on "
                    + "abs(Re(s))<=eta/2. There is a positive constant A, independent of M and t, "
                    + "such that for M>=1 and abs(t)<=M the sum of the norms of the regular "
                    + "part and its complex derivative at i*t is at most A*M^(max(k,1)). "
                    + "The inverse-square tail estimate bounds the paired tail by a constant "
                    + "times M in a fixed neighborhood of the segment. Cauchy's estimate on "
                    + "circles of radius eta/4 then controls the derivative with the same degree. For cutoffs below four, the finite correction is bounded using the spectral mass at eight."))),
                DescribeRole.Theorem))));
}

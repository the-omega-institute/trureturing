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
                DescribeId.Create("regular-part-differentiable-on"),
                DeclarationHandle.Create(Prefix + "regularPart_differentiableOn"),
                H("Holomorphic regular part"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let a locally finite positive spectrum, with positive integral multiplicities, "
                    + "have counting function asymptotic to T log(T)/(2 pi). Suppose a Laplace "
                    + "transform has the prescribed paired pole expansion with holomorphic remainder J "
                    + "on the strip from -eta to 1, where 0<eta<1/5. For M>=4, subtract all poles "
                    + "whose positive ordinate is at most 2M. The resulting regular part is holomorphic "
                    + "on abs(Re(s))<eta and abs(Im(s))<M+1. Pairing opposite poles supplies an "
                    + "inverse-square summable majorant, uniformly on this rectangle."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("laplace-finite-poles-regular"),
                DeclarationHandle.Create(Prefix + "laplace_eq_finite_poles_add_regular"),
                H("Exact finite pole decomposition"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under the same counting and paired Laplace assumptions, for every M>=4 "
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
                    + "such that for M>=4 and abs(t)<=M the sum of the norms of the regular "
                    + "part and its complex derivative at i*t is at most A*M^(max(k,1)). "
                    + "The inverse-square tail estimate bounds the paired tail by a constant "
                    + "times M in a fixed neighborhood of the segment. Cauchy's estimate on "
                    + "circles of radius eta/4 then controls the derivative with the same degree."))),
                DescribeRole.Theorem))));
}

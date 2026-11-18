using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class OriginalHalfBinomialContinuationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The same original period has a normalized holomorphic correction, continuation and nome.",
        H("The actual original ratio on the full lens"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-continuation"),
                DeclarationHandle.Create("D5/S3/Analytic/OriginalHalfBinomialContinuation.actual_continuation"),
                H("The actual original ratio on the full lens"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                Paragraph(Text("On U=D intersect the principal logarithm slit plane, set t0=(i/pi)(log(16)-log(r))+H(r). The identity rG=R-1 gives the actual derivative t0'=-i/(pi r(1-r)P squared) everywhere on U.")),
                Paragraph(Text("The full lens L={norm r<1 and norm(1-r)<1} is open and convex and lies in U: norm(1-r)<1 implies Re(r)>0. The native tau has exactly the same derivative there, so t0-tau is constant on L. The constant is fixed by the original complementary-period log(16) limit, not by an assumed continuation.")),
                Paragraph(Text("The reciprocal period has a finite derivative at zero, so (1/P(r)-1)/r has a finite real radial limit. Multiplication by r log(r), tending to zero, pays the necessary logarithmic period error. Thus pi P(1-r)/P(r)+log(r)-log(16) tends to zero along positive real r, using reality from the original Euler integral. H(r) tends to zero, which makes the constant difference zero. The resulting equality holds at every complex point of L."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("continued-numerator"),
                DeclarationHandle.Create("D5/S3/Analytic/OriginalHalfBinomialContinuation.continued_numerator"),
                H("The continued native numerator and its equation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                Paragraph(Text("The actual function n0=P t0 is holomorphic on the entire slit disk U and equals iP(1-r) on the full lens. Its actual first and second derivatives satisfy r(1-r)n0''+(1-2r)n0'-n0/4=0 and the oriented Wronskian n0'P-n0P'=-i/(pi r(1-r)) throughout U.")),
                Paragraph(Text("The proof differentiates the neighborhood identity r(1-r)P squared t0'=-i/pi, then combines it with the actual native Picard-Fuchs equation for P. Holomorphy on the open domain supplies the derivative regularity, and a neighborhood product identity supplies the actual second derivative of n0."))), DescribeRole.Theorem))));
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.GoldenResource;

internal sealed class DivisorAssociationFiberDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/GoldenResource/DivisorAssociationFiber.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The four-block association quotient has a unique boundary representative and an exact image count for every finite exponent box.",
        H("Divisor Association Fibers"),
        Blocks(
            Paragraph(Text("A source is a quadruple of natural exponents (a,b,c,k). "
                + "The box bounds them by arbitrary natural numbers A,B,C,D, including zero. "
                + "The observation q(a,b,c,k)=(a+k,b,c+k) joins the first and third coordinates "
                + "through the fourth exponent. This describes an association quotient; "
                + "it does not identify the arithmetic block 7 with the product 2 times 5.")),
            Entry("box", "The complete finite source box",
                "The Cartesian product of ranges of lengths A+1, B+1, C+1, D+1.",
                DescribeRole.Definition),
            Entry("q", "Observed association position",
                "The position retains a+k, b, and c+k, so it can forget the original k.",
                DescribeRole.Definition),
            Entry("labels", "The exact hidden-label interval",
                "For position (u,v,w), the labels are the natural integers from "
                + "max(u-A,w-C) to min(D,u,w), provided v is at most B; otherwise "
                + "the interval is empty. Natural subtraction incorporates the zero lower bound.",
                DescribeRole.Definition),
            Entry("fiberEquiv", "Recovering complete sources",
                "The fiber of (u,v,w) is in bijection with its exact label interval. "
                + "A label k restores (u-k,v,w-k,k). Both inverse identities hold, "
                + "including empty and degenerate fibers.", DescribeRole.Definition),
            Entry("boundary", "Unique boundary sources",
                "The retained sources satisfy k=D or a=0 or c=0. Each observed "
                + "position has exactly one such representative: its hidden exponent "
                + "is min(D,u,w). This gives a canonical representative even when "
                + "the fiber contains three or more sources.", DescribeRole.Definition),
            Entry("image_card", "Exact size of the association quotient",
                "For every natural A,B,C,D, the image has "
                + "(B+1)((A+1)(C+1)+D(A+C+1)) positions. The proof constructs "
                + "the unique boundary representative, then removes the interior "
                + "sources with positive a and c and k below D from the complete box. "
                + "For the 5040 exponent box (4,2,1,1), this yields 48 positions "
                + "from 60 sources; the interpretation requires the existing "
                + "prime-exponent divisor language. Counts and geometric positions "
                + "alone supply no Robin inequality or proof of the Riemann hypothesis.",
                DescribeRole.Theorem),
            Paragraph(Text("The source-bound escape audit for image_card remains "
                + "declared_unresolved: IE-C050 ClosedTruthReadout, unclassified_form, "
                + "source.residual_requires_open. Its faithful equivalence, variation, "
                + "sensitivity and actual-observation dependence proofs compile, but "
                + "source-binding validation is unfinished. The exact gap is tracked "
                + "at https://github.com/the-omega-institute/trureturing/issues/15780. "
                + "This audit status does not replace the Lean proof of the cardinality formula.")))));

    private static DocumentBlock Entry(string selector, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(selector.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + selector), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}

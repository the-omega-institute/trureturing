using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.CosetActions;

internal sealed class TwistedGradedCornerDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/FiniteGroups/CosetActions/TwistedGradedCorner";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Inverse-degree pairings and twisted associativity bound the dimensions of the grades. "
        + "When the total dimension is the group order, every grade is a line.",
        H("Homogeneous lines in a twisted graded corner"),
        Blocks(
            Paragraph(Text("Let B be a complex vector space with components indexed by a group K. "
                + "Its bilinear multiplication respects the grading, has unit e, and satisfies "
                + "twisted associativity on homogeneous triples with a nonzero scalar for each "
                + "triple of degrees. The identity component is the span of e. Each nonzero "
                + "homogeneous vector has a nonzero product with some right factor of inverse degree.")),
            Describe.Lean(
                DescribeId.Create("homogeneous-spanning"),
                DeclarationHandle.Create(Module + ".grade_eq_span_singleton"),
                H("Spanning an occupied grade"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Choose a nonzero vector a in a grade and an inverse-degree "
                    + "vector b with ab a nonzero multiple of e. For any c of the same degree as a, "
                    + "the product bc is a scalar multiple of e. Twisted associativity then "
                    + "identifies a nonzero scalar multiple of c with a scalar multiple of a. "
                    + "This is the spanning argument from Davydov and Simmons, Lemma 2.14. "
                    + "https://arxiv.org/abs/1603.04650"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nonzero-homogeneous-product"),
                DeclarationHandle.Create(Module + ".homogeneous_mul_ne_zero"),
                H("Products of nonzero homogeneous vectors"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For nonzero homogeneous x and y, choose an inverse-degree z "
                    + "so that yz is a nonzero multiple of e. Then x(yz) is a nonzero multiple of x. "
                    + "Twisted associativity forces xy to be nonzero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("saturated-grade-dimension"),
                DeclarationHandle.Create(Module + ".finrank_grade_eq_one"),
                H("Dimension saturation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume K is finite and the components form an internal direct "
                    + "sum equal to B. The total dimension is the sum of the component dimensions. "
                    + "Each is at most one by the spanning result, so equality of the total dimension "
                    + "with the group order forces every component to have dimension one."))),
                DescribeRole.Theorem))));
}

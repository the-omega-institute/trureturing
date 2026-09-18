using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Additive;

internal sealed class RepresentationFunctionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Additive/RepresentationFunction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Counting the ordered pairs of a finite set by their sum distributes the square of the "
            + "cardinality over the reachable sums.",
        H("Representation functions of a finite set"),
        Blocks(
            Paragraph(Text(
                "The representation function records how many ways a number is a sum of two "
                    + "members of a set. Both the ordered and the unordered count are kept, since "
                    + "additive questions are stated in either convention; the total mass identity "
                    + "below is the ordered one, where every pair is counted once.")),
            Describe.Lean(
                DescribeId.Create("ordered-representation-count"),
                DeclarationHandle.Create(Prefix + "repCount"),
                H("The ordered count"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a finite set A of naturals and a natural n, repCount A n is the number of "
                        + "ordered pairs in the product of A with itself whose two entries sum to "
                        + "n. Repeated summands are counted, and the pair with entries exchanged "
                        + "is counted separately."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("unordered-representation-count"),
                DeclarationHandle.Create(Prefix + "repCountUnordered"),
                H("The unordered count"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The same count restricted to pairs whose first entry is at most the second, "
                        + "so each unordered pair contributes once while a repeated summand still "
                        + "contributes. This is the convention in which the Sidon condition reads "
                        + "as the count never exceeding one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("representation-total-mass"),
                DeclarationHandle.Create(Prefix + "repCount_total_mass"),
                H("Total mass"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If A is contained in the naturals below N plus one, then summing repCount A n "
                        + "over n below twice N plus one gives the square of the cardinality of A. "
                        + "Every ordered pair from A has its sum in that range, so the sum counts "
                        + "the fibres of the addition map on the product of A with itself; the "
                        + "fibres partition that product, whose cardinality is the square of the "
                        + "cardinality of A."))),
                DescribeRole.Theorem)),
        []));
}

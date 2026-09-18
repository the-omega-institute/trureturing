using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Additive;

internal sealed class SidonSetDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Additive/SidonSet.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Sidon subset of the integers from one to N obeys the classical difference-counting "
            + "cardinality bound.",
        H("Sidon sets and the difference-counting bound"),
        Blocks(
            Paragraph(Text(
                "A set is Sidon when a sum of two of its elements determines the pair of summands "
                    + "up to their order. Repeated summands are allowed, so the condition is stated "
                    + "on sums rather than on differences; over the naturals this avoids reading a "
                    + "truncated subtraction as a signed difference.")),
            Describe.Lean(
                DescribeId.Create("sidon-set-definition"),
                DeclarationHandle.Create(Prefix + "IsSidon"),
                H("Sidon sets"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "IsSidon A holds when, for members a, b, c and d of A, the equality of a plus b "
                        + "with c plus d forces a to equal c and b to equal d, or a to equal d and b "
                        + "to equal c."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sidon-set-cardinality-bound"),
                DeclarationHandle.Create(Prefix + "card_mul_card_sub_one_le"),
                H("The cardinality bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a finite Sidon set A inside the integers from one to N, the product of the "
                        + "cardinality of A with one less than that cardinality is at most twice N "
                        + "minus one. The proof sends an ordered pair of distinct members of A to a "
                        + "sign together with the magnitude of their difference, which lands in the "
                        + "integers from one to N minus one. The Sidon condition makes that map "
                        + "injective, and counting the target supplies the factor two. The factor is "
                        + "not removable: the pair one and two inside the interval up to two is a "
                        + "Sidon set for which the bound without it fails."))),
                DescribeRole.Theorem)),
        []));
}

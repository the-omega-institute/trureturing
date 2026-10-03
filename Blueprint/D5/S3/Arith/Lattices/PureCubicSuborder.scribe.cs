using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices;

internal sealed class PureCubicSuborderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The integral cubic lattice is a subring with an explicit multiplication table.",
        H("A Pure Cubic Suborder"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pure-cubic-suborder"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Lattices/PureCubicSuborder.pure_cubic_suborder"),
                H("The integer span closes under multiplication"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let K be a characteristic-zero field with a rational power basis "
                            + "(1, theta, theta squared) of dimension three. Let a be an integer "
                            + "and assume theta cubed is 1 + 9a. Set beta to "
                            + "(1 + theta + theta squared)/3.")),
                    Paragraph(Text(
                        "The multiplication table is theta squared = 3 beta - theta - 1, "
                            + "theta beta = beta + 3a, and beta squared = beta + a theta + 2a. "
                            + "Consequently every product of integer linear combinations of "
                            + "1, theta, and beta is another such combination. Their integer "
                            + "span is a subring of K, and every element of it is integral "
                            + "over the integers. The triple (1, theta, beta) is a rational "
                            + "basis of K."))),
                DescribeRole.Theorem))));
}

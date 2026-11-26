using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class WuEndpointFiniteArithmeticDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Semigroups/WuEndpointFiniteArithmetic.";

    private static DocumentBlock Comparison(string id, string name, string title, string statement) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(statement))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A quantitative centered Bernoulli moment gap.",
        H("A finite inequality for the Wu endpoint"),
        Blocks(
            Comparison("centered-bernoulli-gap", "centered_bernoulli_moment_gap", "Quantitative centered Bernoulli gap",
                "For real a and b with −a ≤ b ≤ a, the fourth power of a³ + 3ab² minus the cube of a⁴ + 4a²b² + 4b⁴/9 is at least (14/3)(a²)⁴(b²)²."))));
}

using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Divisors;
internal sealed class ProperDivisorPowerBudgetDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Divisors/ProperDivisorPowerBudget.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A uniform budget for proper-divisor powers", H("A uniform budget for proper-divisor powers"), Blocks(
            Paragraph(Text("The estimate keeps a full additive n margin. Complementary proper divisors lie among the integers from two through n. Mathlib supplies a finite reciprocal-square estimate; no infinite numerical approximation or finite enumeration is used. Multiplication by n^(s-2) extends the result to all natural exponents s at least two.")),
            Node("square_budget", "square budget", "The map d to n/d is injective on proper divisors and gives the exact complementary reciprocal-square sum. The finite telescoping upper bound supplies n squared minus n.", DescribeRole.Theorem),
            Node("power_budget", "power budget", "Each d^s is at most n^(s-2) times d squared. Since n^(s-2) is at least one, the quadratic additive margin remains at least n. The inequality is over integers and holds at n=1 too.", DescribeRole.Theorem))));
    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("properdivisorpowerbudget-" + name.ToLowerInvariant().Replace("_", "-")),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}

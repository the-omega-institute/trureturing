using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic.PermutativeLifts;

internal sealed class FactorialMinimalDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialMinimal.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform recurrence and minimality.",
        H("Uniform recurrence and minimality"),
        Blocks(
            Describe.Lean(DescribeId.Create("construction"), DeclarationHandle.Create(Owner + "factorialWindow"),
                H("Construction"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An actual finite interval meets at most two sufficiently long blocks. Every such adjacent block pair occurs in every block two levels higher. A following high-level boundary therefore supplies the same interval in every point, with a uniform bound of twice the larger high-level block length. Every finite coordinate pattern is reached by every integer shift orbit, proving ordinary topological minimality."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("main-result"), DeclarationHandle.Create(Owner + "factorial_orbit_dense"),
                H("Result"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An actual finite interval meets at most two sufficiently long blocks. Every such adjacent block pair occurs in every block two levels higher. A following high-level boundary therefore supplies the same interval in every point, with a uniform bound of twice the larger high-level block length. Every finite coordinate pattern is reached by every integer shift orbit, proving ordinary topological minimality."))), DescribeRole.Theorem)),
            [ DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialSubshift")) ]));
}

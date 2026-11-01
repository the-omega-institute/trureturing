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
                Blocks(Paragraph(Text("An actual finite interval meets at most two sufficiently long blocks. Every such adjacent block pair occurs in every block two levels higher. A following high-level boundary therefore supplies the same interval in every point, with a uniform bound of twice the larger high-level block length. Every finite coordinate pattern is reached by every integer shift orbit, proving ordinary topological minimality."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("marked-block-occurrence"), DeclarationHandle.Create(Owner + "marked_block_occurs"),
                H("An actual marked block occurs"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any binary word family and actual marked tiling, a marked boundary reads exactly its current word at the same physical integer origin. This existing generic helper is public for reuse by the balanced construction; its proof is unchanged."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("infix-occurrence"), DeclarationHandle.Create(Owner + "occurs_of_infix"),
                H("An infix inherits an actual occurrence"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If a word is an infix of another word that occurs at integer t, it occurs at t+k for a natural prefix length k with k plus its length bounded by the enclosing word length. The publicized existing helper retains the literal coordinate origin and its original proof."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("coordinate-infix"), DeclarationHandle.Create(Owner + "infix_of_coordinates"),
                H("Coordinate equality gives an infix"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A finite word is an infix at natural offset p when it fits in the enclosing list and every indexed letter agrees there. The existing proof identifies it with a take of a drop and is unchanged by publicization. The balanced minimality proof consumes this helper."))), DescribeRole.Theorem)),
            [ DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialSubshift")) ]));
}

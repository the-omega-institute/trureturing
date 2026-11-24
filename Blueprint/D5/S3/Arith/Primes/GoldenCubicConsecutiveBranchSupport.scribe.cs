using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class GoldenCubicConsecutiveBranchSupportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The consecutive cubic-label branch loci are private simple cyclotomic divisors.",
        H("Cyclotomic support of consecutive Fibonacci-compatible cubic labels"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("consecutive-branch-support"),
                DeclarationHandle.Create("D5/S3/Arith/Primes/GoldenCubicConsecutiveBranchSupport.consecutive_branch_support"),
                H("Consecutive marking has exact torsion support, without collisions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("On the Fibonacci conic, the Laurent parameter a projects to x=a minus its inverse. The cubic Lucas recurrence then comes from cubing a. For each depth i the excluded locus x squared equals minus three is precisely where a squared has exact multiplicative order three to the i plus one.")),
                    Paragraph(Text("For a word of length k the union is the nontrivial three-to-the-k torsion of a squared. The product of the level factors, multiplied by a squared minus one, gives the exact division-free torsion equation. In the x coordinate, marked zeros have nonzero linear coefficient; no point is marked at two levels, and no marked point lies above a branch value of the conic projection.")),
                    Paragraph(Text("This is the algebraic support input for a Kummer cover. The cover, its geometric genus, Hasse-Weil bounds, and distribution along one native Lucas orbit are not formalized here."))),
                DescribeRole.Theorem))));
}

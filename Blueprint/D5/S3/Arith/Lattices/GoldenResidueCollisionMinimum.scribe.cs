using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices;

internal sealed class GoldenResidueCollisionMinimumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Balanced residue populations exactly minimize the number of colliding pairs.",
        H("Balanced Residue Collision Minimum"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("balanced-collision-cost-minimum"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Lattices/GoldenResidueCollisionMinimum.balanced_collision_cost_minimum"),
                H("Exact minimum and attaining populations"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let n objects occupy m residue classes, with m positive, "
                    + "and write n = mq + r with 0 <= r < m. "
                    + "For populations c_i summing to n, twice the number of "
                    + "colliding unordered pairs is the sum of c_i(c_i - 1). "
                    + "This sum is at least mq(q - 1) + 2rq. The lower bound "
                    + "is attained by assigning q + 1 objects to r classes "
                    + "and q objects to each remaining class. At one precision "
                    + "in the golden-tower collision calculation, m is 4^s. "
                    + "The theorem gives that precision's exact minimum; "
                    + "compatibility across precisions and field index claims "
                    + "require separate arguments."))),
                DescribeRole.Theorem))));
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class RankThreeOmissionRelationsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/RankThreeOmissionRelations";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Point potentials express relations among oriented triangle rows.",
        H("Reduced Triangle Relations"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rank-three-omission-point-potential"),
                DeclarationHandle.Create(Module + ".IsOmissionPotential"),
                H("Normalized point potentials"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A potential vanishes at the chosen anchor, has zero total sum, and is killed by three at every point. "
                    + "It takes equal values at the ends of every pair in no omitted triple. Its values on each omitted triple sum to zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("rank-three-potential-relations"),
                DeclarationHandle.Create(Module + ".potential_to_relations_bijective"),
                H("Point potentials and relations"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Take a finite indexed family on a finite ground set. Each triple has three distinct points, "
                    + "and triples with distinct indices share at most one point. "
                    + "Suppose multiplication by the ground-set size annihilates the coefficient group. "
                    + "For distinct root and anchor, evaluating a normalized potential by its difference across "
                    + "the first oriented edge of each triple gives a bijection with the reduced row relations."))),
                DescribeRole.Theorem))));
}

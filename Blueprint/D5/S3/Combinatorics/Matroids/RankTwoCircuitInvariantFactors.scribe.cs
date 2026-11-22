using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class RankTwoCircuitInvariantFactorsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/RankTwoCircuitInvariantFactors";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The cyclic factors of the rank-two integral lifting quotient.",
        H("Invariant factors of the rank-two lifting obstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rank-two-lifting-invariant-factors"),
                DeclarationHandle.Create(Module + ".rank_two_lifting_obstruction_invariant_factors"),
                H("The invariant factors for parallel classes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let a loopless rank-two matroid have k + 2 nonempty parallel classes, a ground of "
                    + "size n and class sizes with gcd g. The lifting obstruction is the product of a "
                    + "cyclic group of order g and k cyclic groups of order n. A unimodular change of "
                    + "coordinates reduces the class-size relation to multiplication by the gcd of the "
                    + "weights outside the distinguished class. On the n-torsion subgroup this gcd "
                    + "imposes exactly the g-torsion condition. This also gives the two-class formula "
                    + "and the case of all singleton classes."))),
                DescribeRole.Theorem))));
}

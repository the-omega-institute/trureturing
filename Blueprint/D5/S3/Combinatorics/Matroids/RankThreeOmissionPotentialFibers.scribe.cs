using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class RankThreeOmissionPotentialFibersDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/RankThreeOmissionPotentialFibers";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Consider a finite point set with listed triples of distinct points. Each pair of distinct points lies in at most one indexed triple.",
        H("Fibers of Ternary Point Potentials"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ternary-point-potential-fibers"),
                DeclarationHandle.Create(Module + ".point_potential_evaluations"),
                H("Surjectivity, equal fibers and affine lines in the equality case"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Fix an anchor. Let d be the dimension of the normalized ternary point-potential space. "
                    + "Evaluation in the coordinates of any basis reaches every ternary vector of dimension d. Any two fibers are equivalent, "
                    + "so the point count is three to the power d times the size of the zero fiber. When two evaluation vectors differ, "
                    + "the pair belongs to a unique indexed triple whose third vector is their negative sum. "
                    + "If the point count equals three to the power d, evaluation is injective. The triples then correspond exactly to "
                    + "the triples of distinct vectors with zero sum, which are the affine lines over the ternary field. "
                    + "For two different fibers, fixing a point in the negative-sum fiber gives an involution that exchanges them by taking the third point."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rank-three-obstruction-ternary-divisibility"),
                DeclarationHandle.Create(Module + ".rank_three_lifting_obstruction_divisibility"),
                H("The additional ternary multiplicity divides the ground-set size in powers of three"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Take a rank-three core on a finite ordered set of n greater than three points with singleton parallel classes, "
                    + "and suppose its bases are precisely the triples outside a family of m omitted triples satisfying the pair bound. "
                    + "The integral lifting obstruction is linearly equivalent over the integers to the direct sum of binom(n minus two, two) "
                    + "minus m factors of order n and d factors of order three, with three to the power d dividing n. "
                    + "The equal sizes of the potential fibers give this divisibility when n is divisible by three. "
                    + "When n is coprime to three, the potential count is one and d is zero."))),
                DescribeRole.Theorem))));
}

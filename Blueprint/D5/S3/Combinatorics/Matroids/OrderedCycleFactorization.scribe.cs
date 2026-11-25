using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class OrderedCycleFactorizationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/OrderedCycleFactorization";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalized top integral cycles factor along least-nonloop circuits in finite ordered matroids.",
        H("Signed circuit factorization of normalized matroid cycles"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ordered-join-boundary"),
                DeclarationHandle.Create(Module + ".boundaryOn_signedJoin"),
                H("The augmented boundary of an ordered join"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a finite totally ordered carrier, let C specify a partition into C "
                        + "and its complement. The join of two integral chains at a face F uses "
                        + "the left coefficient at the intersection with C and the right "
                        + "coefficient at the difference with C. Multiply their product by "
                        + "minus one to the number of pairs in which a right vertex precedes a left vertex.")),
                    Paragraph(Text(
                        "The boundary at a ridge sums over vertices outside it, with insertion "
                        + "sign minus one to the number of ridge vertices preceding the insertion. "
                        + "Split this sum at C. The left insertions give the boundary on the left "
                        + "part times the right coefficient. The right insertions give the left "
                        + "coefficient times the boundary on the right part and the parity of the "
                        + "left ridge size. Both terms carry the shuffle sign of the ridge.")),
                    Paragraph(Text(
                        "For a left insertion the count of preceding right vertices occurs in "
                        + "both signs. For a right insertion the counts of left vertices before "
                        + "and after the new vertex add to the full left ridge size."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("normalized-circuit-factorization"),
                DeclarationHandle.Create(Module + ".normalized_factorization"),
                H("The least nonloop gives the signed circuit product"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let M be a matroid on a finite totally ordered carrier and let B be a "
                        + "base whose every vertex can be exchanged for a strictly smaller vertex. "
                        + "There is exactly one integral chain supported on bases, with zero augmented "
                        + "boundary and with coefficients on internally passive bases given by the "
                        + "Kronecker delta at B. If B is empty, this chain has coefficient one at "
                        + "the empty face and zero everywhere else.")),
                    Paragraph(Text(
                        "In positive rank let e be the least nonloop, C its fundamental circuit "
                        + "relative to B, and D the difference of B with C. Then D is an internally "
                        + "passive base in the contraction of C, with the inherited order. Join "
                        + "the oriented augmented boundary of the simplex on C with the normalized "
                        + "cycle at D. The orientation multiplier is the insertion sign of e at "
                        + "the circuit deletion, times the shuffle sign at B. This gives "
                        + "coefficient positive one at B.")),
                    Paragraph(Text(
                        "The simplex boundary is a cycle because the two orders of deleting "
                        + "distinct vertices have opposite signs. Each circuit deletion lifts a "
                        + "contracted base to a base. Only deletion of e can give a passive "
                        + "base, and on that deletion a smaller exchange for an outside vertex "
                        + "is exactly a smaller exchange in the contraction. This gives the "
                        + "prescribed passive coordinates and reduces existence to a smaller base.")),
                    Paragraph(Text(
                        "For uniqueness, choose the latest differing base in the colexicographic "
                        + "order. An internally active vertex gives a ridge whose other cofaces "
                        + "have larger insertion vertices and already agree. Its remaining "
                        + "incidence has sign positive or negative one, forcing agreement there too.")),
                    Paragraph(Text(
                        "A face has nonzero coefficient exactly when its left part omits one "
                        + "vertex of C and its right part has nonzero coefficient in the contracted "
                        + "cycle. The omitted vertex and the right part recover the face uniquely. "
                        + "The support size is the circuit size times the contracted support size."))),
                DescribeRole.Theorem))));
}

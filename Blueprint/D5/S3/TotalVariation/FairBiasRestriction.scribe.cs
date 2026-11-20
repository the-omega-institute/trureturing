using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class FairBiasRestrictionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/TotalVariation/FairBiasRestriction";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The lexicographic shelling partitions the augmented signed fair-bias complex into intervals.",
        H("Restriction faces of the fair-bias link"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("first-at-iff-restriction-subset"),
                DeclarationHandle.Create(Module + ".firstAt_iff_restriction_subset"),
                H("The restriction face identifies the new subfaces"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Fix a finite family of binary columns and a linear order of its signed labels. " +
                    "In a nonempty facet B, mark each vertex whose removal leaves a subset of some earlier facet. " +
                    "For every subset S of B, including the empty face, B is the first containing facet " +
                    "exactly when S contains all the marked vertices. The shelling criterion turns any " +
                    "earlier occurrence of S into a one-vertex omission at B."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("face-enumerator-eq-sum"),
                DeclarationHandle.Create(Module + ".faceEnumerator_eq_sum"),
                H("The face enumerator is the sum of the interval enumerators"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For the same ordered family, assume at least one nonempty facet exists. Let d be the " +
                    "number of labels minus the rank of the columns. For every t in a commutative semiring, " +
                    "weight each face S by t to the power of its size, with the empty face included. The sum " +
                    "over all faces equals the sum over facets B of t to the size of the restriction face " +
                    "times one plus t to the power of d minus that size."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("face-enumerator-eq-one"),
                DeclarationHandle.Create(Module + ".faceEnumerator_eq_one"),
                H("The augmented enumerator is one when no nonempty facet exists"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If the nonempty facet set is empty, no nonempty face can occur, since any such face " +
                    "would extend to a maximal one. The empty face contributes one for every choice of t."))),
                DescribeRole.Theorem))));
}

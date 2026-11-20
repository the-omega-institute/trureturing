using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class FairBiasRestrictionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/TotalVariation/FairBiasRestriction";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "When nonempty facets exist, the lexicographic shelling partitions the augmented signed fair-bias complex into intervals.",
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
                    "For the same ordered family, let d be the " +
                    "number of labels minus the rank of the columns. For every t in a commutative semiring, " +
                    "weight each face S by t to the power of its size, with the empty face included. " +
                    "When nonempty facets exist, sum over them the product of t raised to the size of the " +
                    "restriction face and (1 + t) raised to d minus that size. " +
                    "Otherwise the only face is empty and the sum is one."))),
                DescribeRole.Theorem))));
}

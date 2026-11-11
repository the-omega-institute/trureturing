using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class PartitionCoefficientStructureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCoefficientStructure.";

    private static DocumentBlock Entry(string id, string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Structural restrictions on nonzero quadratic collision configurations.",
        H("Quadratic partition coefficients"),
        Blocks(
            Entry("partition-coefficient", "partitionCoefficient", "Reduction coefficient of a configuration",
                "For a partition sigma of Fin k, retained subset S of its blocks, and real a and b, partitionCoefficient is the product of u(size(B)) "
                + "over retained blocks B times the product of v(size(B)) over the other blocks, where u and v are the quadratic power coefficients.", DescribeRole.Definition),
            Entry("partition-main-residual", "partitionMainResidual", "Residual after removing free-block collisions",
                "For a finite index type, commutative real algebra A, linear functional ell, algebra-valued family Y, and original scalar weight family f, "
                + "partitionMainResidual is the product of the scalar sums of the free block weights times the ordered distinct-index moment of the retained block weights. "
                + "The retained blocks are enumerated by the inverse of equivFin on S.", DescribeRole.Definition),
            Entry("partition-coefficient-zero-free-singleton", "partitionCoefficient_zero_of_free_singleton", "Free singletons vanish",
                "If a block outside the retained set S has multiplicity one, partitionCoefficient is zero, since the constant coordinate v(1) is zero.", DescribeRole.Theorem),
            Entry("partition-coefficient-nonzero-free-multiplicity", "partitionCoefficient_nonzero_free_mult", "Every nonzero free block has size at least two",
                "If partitionCoefficient is nonzero, every unretained block has multiplicity at least two. "
                + "Every quotient block is nonempty, and multiplicity one would force the coefficient to vanish.", DescribeRole.Theorem),
            Entry("kernel-moment-main-without-free-blocks", "kernelDistinctMoment_eq_main_of_compl_card_zero", "No error when every block is retained",
                "If the complement of S has cardinality zero, kernelDistinctMoment equals partitionMainResidual exactly. "
                + "There are then no collision edges involving an unretained block, so only the empty edge set occurs in the collision expansion. "
                + "The statement includes the top-order distinct-index moment and requires no size estimate for it.", DescribeRole.Theorem),
            Entry("kernel-moment-zero-single-retained-block", "kernelDistinctMoment_zero_of_retained_card_one", "A single retained block is centered",
                "If ell(Y(d))=0 for every index d and the retained set S has cardinality one, kernelDistinctMoment is zero. "
                + "Every summand contains exactly one centered algebra factor inside ell.", DescribeRole.Theorem),
            Entry("partition-main-zero-single-retained-block", "partitionMainResidual_zero_of_retained_card_one", "The corresponding main residual is centered",
                "Under the same centering and cardinality-one condition on S, partitionMainResidual is zero. "
                + "Its empty-edge assignment representation again contains one centered algebra factor in each summand.", DescribeRole.Theorem))));
}

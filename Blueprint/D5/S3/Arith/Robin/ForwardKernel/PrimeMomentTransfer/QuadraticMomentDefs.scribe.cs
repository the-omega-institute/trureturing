using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class QuadraticMomentDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticMomentDefs.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite quadratic moment sums and pairing expressions.",
        H("Quadratic moment definitions"),
        Blocks(
            Describe.Lean(DescribeId.Create("index-sum"), DeclarationHandle.Create(Prefix + "indexSum"), H("Coefficient sum"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Sum a real coefficient function over the finite index type."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("quadratic-family-moment"), DeclarationHandle.Create(Prefix + "quadraticFamilyMoment"), H("Moment of weighted sums"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Apply a real linear functional to a product of finite sums of indexed algebra elements weighted by real coefficient functions."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("distinct-index-moment"), DeclarationHandle.Create(Prefix + "distinctIndexMoment"), H("Distinct-index moment"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Sum coefficient products times the linear functional of the corresponding algebra products over ordered injective tuples of indices."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("perfect-pairing-sum"), DeclarationHandle.Create(Prefix + "perfectPairingSum"), H("Perfect pairing sum"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For a function of two coefficient functions, sum its three products associated with the perfect pairings of four inputs."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("repeated-pair-sum"), DeclarationHandle.Create(Prefix + "repeatedPairSum"), H("Repeated pair sum"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Sum the six terms obtained by multiplying one pair of the four coefficient functions and leaving the two other inputs separate."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("pair-pair-sum"), DeclarationHandle.Create(Prefix + "pairPairSum"), H("Two pairs sum"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Sum the three terms obtained by splitting four coefficient functions into two pairs and multiplying within each pair."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("triple-singleton-sum"), DeclarationHandle.Create(Prefix + "tripleSingletonSum"), H("Triple and singleton sum"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Sum the four terms obtained by choosing a singleton input and multiplying the other three coefficient functions."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("quadratic-family-moment-eq-tuple-sum"), DeclarationHandle.Create(Prefix + "quadraticFamilyMoment_eq_tuple_sum"), H("Expansion over ordered tuples"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("A moment of weighted finite sums equals the sum over all ordered index tuples of the coefficient product times the linear functional of the corresponding algebra product."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sum-perm"), DeclarationHandle.Create(Prefix + "sum_perm"), H("Permutation of injective tuples"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Precomposing every ordered injective tuple with a permutation of its positions leaves the sum of any real-valued function of the tuple unchanged."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("distinct-index-moment-pair-comm"), DeclarationHandle.Create(Prefix + "distinctIndexMoment_pair_comm"), H("Symmetry of the distinct second moment"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Interchanging the two coefficient functions leaves the ordered distinct-index second moment unchanged, because swapping the two indices preserves injectivity and multiplication is commutative."))), DescribeRole.Theorem))));
}

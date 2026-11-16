using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class SingleLengthSamplingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthSampling.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cumulative scalar moments admit floor sampling with explicit terminal corrections.",
        H("Single-length cumulative sampling"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sampling-cumulative-pointwise"),
                DeclarationHandle.Create(Prefix + "sampling_cumulative_pointwise"),
                H("Endpoint discrepancy on the full prefix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For Y at least two, lengths between one and Y, and base points between one and Y, "
                    + "the continuous increment differs from the increment with both length and base point rounded down "
                    + "by at most 2 log(4Y)+2. Beyond the length scale this uses the dyadic sampling estimate; "
                    + "the remaining prefix is controlled by the endpoint lattice crossings."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("step-mem-lp"),
                DeclarationHandle.Create(Prefix + "step_memLp"),
                H("Fourth integrability of sampled increments"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every real cutoff and length, the floor-sampled lattice increment belongs to L4 "
                    + "on the closed interval from one to the cutoff. Only finitely many lattice values occur there."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("floor-integral-identity"),
                DeclarationHandle.Create(Prefix + "floor_integral_identity"),
                H("Exact terminal-cell correction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any real sequence F and Y at least one, set N=floor(Y). The integral of F(floor(x)) "
                    + "from one to Y minus the sum of F(n) over 1 through N equals (Y-N-1)F(N). "
                    + "In particular, an integral cutoff contributes minus its final sample."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("step-fourth-le-sum"),
                DeclarationHandle.Create(Prefix + "step_fourth_le_sum"),
                H("Discrete control of the sampled fourth integral"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For Y at least one, the fourth integral of the increment with floored length and base point "
                    + "is at most its discrete fourth-moment prefix through floor(Y). "
                    + "The exact terminal-cell correction is nonpositive."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("scalar-stability"),
                DeclarationHandle.Create(Prefix + "scalar_stability"),
                H("Stability of scalar moments under fourth-moment perturbations"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On a probability space, suppose f and g have fourth moments at most C and their difference "
                    + "has fourth moment at most e^4, with C and e nonnegative. For k equal to two or four, "
                    + "their kth moments differ by at most k e C^((k-1)/4). "
                    + "This is the finite-product replacement bound applied to identical factors."))),
                DescribeRole.Theorem))));
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class JointCircuitLiftingObstructionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/JointCircuitLiftingObstruction";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Smith coordinates and the cyclic obstruction for two rank-one factors.",
        H("Integral joint circuit lifting"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rank-one-transpose-cokernel"),
                DeclarationHandle.Create(Module + ".rank_one_transpose_cokernel"),
                H("The rank-one transpose cokernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a nonempty ground of size n whose bases are precisely the ground "
                    + "singletons, the transpose cokernel is the cyclic integer module of "
                    + "order n. A circuit is a pair and its contraction has the empty basis. "
                    + "The corresponding readout is a signed difference of singleton "
                    + "coefficients. Hence all singleton evaluations represent the same "
                    + "generator in the cokernel, and the augmented boundary makes n times "
                    + "that generator vanish. A cycle with coefficients one except at a "
                    + "chosen vertex, where the coefficient is one minus n, gives a character "
                    + "sending the generator to one modulo n."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("joint-lifting-obstruction-equiv"),
                DeclarationHandle.Create(Module + ".joint_lifting_obstruction_equiv"),
                H("Torsion of the integral lifting quotient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On a nonempty ground, the signed pivot pairings give injectivity of "
                    + "joint restriction. The torsion submodule of the integral target modulo "
                    + "the joint image is the saturation of that image modulo the image. "
                    + "Smith coordinates identify this torsion submodule with the transpose "
                    + "cokernel. The identification uses a choice of Smith bases."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rank-one-sum-joint-lifting-obstruction"),
                DeclarationHandle.Create(Module + ".rank_one_sum_joint_lifting_obstruction"),
                H("The cyclic obstruction for two rank-one factors"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For an ordered direct sum of two nonempty rank-one loopless matroids "
                    + "with ground sizes m and n, the obstruction to an integral joint lift "
                    + "of a rationally compatible integral tuple is cyclic of order gcd(m,n). "
                    + "The tensor of the two cyclic generators generates the tensor of the "
                    + "transpose cokernels. Bezout's identity gives its annihilator and the "
                    + "tensor of the reductions modulo gcd(m,n) detects its exact order. "
                    + "In particular, coprime ground sizes give a saturated joint image."))),
                DescribeRole.Theorem))));
}

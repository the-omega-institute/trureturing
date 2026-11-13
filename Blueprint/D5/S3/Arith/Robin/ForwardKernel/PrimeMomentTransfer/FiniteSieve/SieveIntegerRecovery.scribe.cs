using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve;

internal sealed class SieveIntegerRecoveryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveIntegerRecovery.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform integer-scale interval recovery",
        H("Uniform integer-scale interval recovery"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("uniform-integer-small"),
                DeclarationHandle.Create(Prefix + "UniformIntegerSmall"),
                H("uniform integer small"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an order k and interval functional F, uniform integer smallness means that, for every window M and density constant B at least one and every positive epsilon, all sufficiently large natural h satisfy the bound |F(Q,h,a,b)| at most epsilon times (h log h)^(k/2), simultaneously for squarefree Q with Q/phi(Q) at most B log h and ordered endpoints in [0,M]."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sieve-integer-third"),
                DeclarationHandle.Create(Prefix + "sieve_integer_third"),
                H("Uniform cubic recovery at integer scales"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume MSFinite and KuperbergSmoothed. For each fixed endpoint window M and density constant B, the sharp interval third moments divided by (h log h) to the power three halves tend to zero uniformly over admissible interval triples and all squarefree moduli Q satisfying P(Q) at most B log h. Choose a positive mesh from the desired error before choosing the integer threshold. Endpoint rounding and positive shift smoothing give a common fourth-norm bound K and difference at most C times the sum of the square root of the mesh and h to the power minus one quarter. The cubic replacement bound is three times that difference times K squared. The fixed grid cubic moment and the remaining negative power of h become small at a common threshold. Multiplication by the positive cubic scale recovers the sharp moment statement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sieve-integer-fourth"),
                DeclarationHandle.Create(Prefix + "sieve_integer_fourth"),
                H("Uniform fourth Wick recovery at integer scales"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume MSFinite and KuperbergSmoothed. For fixed M and B, the sharp interval fourth Wick defects divided by h squared times log h squared tend to zero uniformly over all admissible interval quadruples and all squarefree Q with P(Q) at most B log h. Choose the mesh first, then a common integer threshold. If D bounds the fourth norm of each replacement error and K bounds all individual fourth norms, the four-variable moment changes by at most 4 D K cubed and the sum of the three covariance products changes by at most 12 D K cubed. Their sum controls the sharp Wick defect together with the fixed grid smooth Wick defect. The identity separating these three contributions, followed by the positive fourth-power scale identity, gives the asserted uniform limit."))),
                DescribeRole.Theorem))));
}

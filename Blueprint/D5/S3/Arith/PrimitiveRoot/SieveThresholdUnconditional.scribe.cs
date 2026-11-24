using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.PrimitiveRoot;

internal sealed class PrimitiveRootSieveThresholdUnconditionalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/PrimitiveRoot/SieveThresholdUnconditional.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A linear principal term for the primitive-root sieve",
        H("A linear principal term for the primitive-root sieve"), Blocks(
            Describe.Lean(DescribeId.Create("covering-linear"),
                DeclarationHandle.Create(Prefix + "covering_linear"),
                H("Uniform signed margins above five million"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every integer x≥5000000 there are covering parameters with positive " +
                    "delta for which the signed error coefficient times " +
                    "(165458/111375)sqrt(x)log(x) is strictly less than delta times 23x/50. " +
                    "SieveThreshold.covering_parameters supplies the existing support " +
                    "construction. At most seven factors use K/delta≤4417/100. Exactly " +
                    "eight use the sharper K/delta≤7+20/(610847/1616615). " +
                    "At x=9699690 the certified logarithm bound is 160903/10000 and the " +
                    "square-root lower bound is 15572/5. Further factors use geometric " +
                    "radical growth and monotonicity of log(x)/sqrt(x)."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("root-from-linear-main"),
                DeclarationHandle.Create(Prefix + "exists_prime_primitiveRoot"),
                H("A prime primitive root from a principal sum at least 23p/50"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a prime p≥5000000, suppose the actual principal triangular sum " +
                    "is at least 23p/50 and each nonprincipal character of squarefree " +
                    "order dividing rad(p−1) has absolute real part at most " +
                    "(165458/111375)sqrt(p)log(p). Then some prime q<p has order p−1 " +
                    "modulo p. No Riemann hypothesis occurs in this numeric reduction; " +
                    "the principal estimate and the character estimate are explicit inputs."))),
                DescribeRole.Theorem))));
}

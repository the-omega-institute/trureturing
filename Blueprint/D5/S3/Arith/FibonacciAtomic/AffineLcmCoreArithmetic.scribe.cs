using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class AffineLcmCoreArithmeticDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Arith/FibonacciAtomic/AffineLcmCoreArithmetic.arithmetic";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual affine lcm core supplies valuation, fiber, saturation, Euler-product, and prime-block arithmetic.",
        H("Affine Lcm Core Arithmetic"),
        Blocks(Describe.Lean(
            DescribeId.Create("affine-lcm-core-arithmetic"),
            DeclarationHandle.Create(Declaration),
            H("Actual affine lcm arithmetic core"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For every L>=2, the theorem proves the actual affine seed prime-power criterion, "
                        + "the saturated 3-adic core, the positive short-signature fiber, and visible-core "
                        + "identities.")),
                Paragraph(Text(
                    "It also proves the residue-theta size error, the additive Euler-product factorization, "
                        + "the valuation defect and square estimates, and the prime-block multiplicativity and "
                        + "Chebyshev logarithm identities used by the public asymptotic result."))),
            DescribeRole.Theorem))));
}

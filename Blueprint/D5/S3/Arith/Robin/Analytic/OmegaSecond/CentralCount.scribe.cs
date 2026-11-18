using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic.OmegaSecond;

internal sealed class CentralCountDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A uniform prime-counting error on an interval centered at a moving endpoint.",
        H("Prime density on a moving central interval"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("central-prime-counting-bound"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/CentralCount.central_prime_counting_bound"),
                H("Uniform central prime-counting error"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every sufficiently large real P and every real t in the closed interval [P/2,2P], the absolute difference between primeCount(t) and t/log(P) is at most 28P/log(P)^2. The prime count includes primes at the floored real endpoint.")),
                    Paragraph(Text("The constant density uses the same central endpoint P throughout the interval. The bound combines the uniform eventual error at t with the change from log(t) to log(P). It supports the moving prime-weight upper estimate; no matching lower bound for the second distinct-prime threshold is asserted."))),
                DescribeRole.Theorem))));
}

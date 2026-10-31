using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class FiniteDeficitComparisonDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual full-record Euler tail differs from its literal finite prime-square sum by a controlled finite error.",
        H("Finite Euler Deficit on Actual Price Records"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-prime-square-sum"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Robin/PriceRecord/FiniteDeficitComparison.finitePrimeSquareSum"),
                H("Literal prime-square sum on the actual second-layer window"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a natural m, this is exactly the finite sum of 1/p^2 over prime p "
                        + "with layerPrime(m,2)<p<=largestPrime(m). It uses the same actual integer "
                        + "and retains the empty-window, Q=1 and Q=P cases."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-finite-euler-deficit"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Robin/PriceRecord/FiniteDeficitComparison.actual_finite_euler_deficit"),
                H("Finite actual-record Euler deficit bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every m>=2, lambda>0 and literal full predecessor record, put "
                            + "P=largestPrime(m), Q=layerPrime(m,2), D=tail(m), and let J be "
                            + "the finite prime-square sum above Q through P. Then "
                            + "0<=D-J<=6/P^(2/3)+2/Q^3, with real powers and casts.")),
                    Paragraph(Text(
                        "The same-record prime structure identifies the valuation-one support with "
                            + "the primes in the literal interval (Q,P]. The complete tail splits "
                            + "into the repeated-layer mass H and the valuation-one layers. "
                            + "For each latter prime, the logarithmic excess above 1/p^2 is "
                            + "nonnegative and at most p^-4. Since p>Q>=1, this is at most "
                            + "Q^-1 p^-3; the finite cubic-tail estimate sums these terms to "
                            + "2/Q^3. The existing same-integer repeated-layer estimate gives "
                            + "H<=6/P^(2/3).")),
                    Paragraph(Text(
                        "The proof keeps all small and empty cutoffs: layerPrime uses its max-one "
                            + "convention, and no Q>1 or Q<P premise is added. It uses the literal "
                            + "record integer throughout and makes no claim about the remaining "
                            + "signed prime-error term, the sqrt(2) asymptotic, Robin's inequality, "
                            + "or RH."))),
                DescribeRole.Theorem))));
}

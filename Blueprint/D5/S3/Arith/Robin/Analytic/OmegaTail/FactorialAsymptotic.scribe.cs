using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic.OmegaTail;

internal sealed class FactorialAsymptoticDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Proposition 7.9 gives the logarithmic rate of the strict factorial tail at each fixed order.",
        H("Exact asymptotic for the strict factorial tail"),
        Blocks(
            Describe.Lean(DescribeId.Create("factorial-tail-asymptotic"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaTail/FactorialAsymptotic.factorial_tail_asymptotic"),
                H("Eventual nonemptiness and the exact logarithmic rate"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix a natural number r ≥ 2. Write L = log x and ℓ = log L. "
                        + "The threshold is L times the sum of j! divided by ℓ to the power j+1 for 0 ≤ j < r. "
                        + "The count N_r(x) filters the natural interval from 1 through floor(x) by the strict inequality that the number of distinct prime factors exceeds this threshold. "
                        + "This interval represents the positive integers at most x.")),
                    Paragraph(Text(
                        "Eventually N_r(x) is positive. The logarithm of N_r(x) divided by L/ℓ^((r+1)/2) tends to π√(2r!/3) as x tends to infinity.")),
                    Paragraph(Text(
                        "At P = log x, factorial_far_deletion supplies a prime base with cardinality floor of the threshold plus one and retains every donor prime in (3P/4, P]. "
                        + "The safe reserve limit and factorial_tail_lower give eventual positivity and the lower logarithmic bound. "
                        + "The continuous reserve limit and factorial_sharp_upper_bound give the upper bound on the same count. "
                        + "After taking logarithms and dividing by the positive scale, the two bounds squeeze the normalized logarithm. "
                        + "Composition with log x and the identity exp(log x) = x for positive x give the stated limit."))),
                DescribeRole.Theorem))));
}

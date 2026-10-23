using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class MertensExplicitEnvelopeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An elementary prime-product envelope with an explicit error constant is valid at every real cutoff at least 286.",
        H("An Explicit Elementary Mertens Envelope"),
        Blocks(
            Paragraph(Text("The classical Mertens identities are reused from the attributed PrimeNumberTheoremAnd port. The numerical constants below are derived in this repository. The module has instance classification because fixed rational certificates from RobinRationalBasis bear the proof; its estimate is uniform for every real cutoff at least 286. Rosser and Schoenfeld, Approximate formulas for some functions of prime numbers, Theorem 8, gives a stronger classical bound; its finite tables and zero information are not premises of this elementary proof. The result is an unconditional analytic estimate and makes no claim to resolve the Riemann hypothesis.")),
            Describe.Lean(
                DescribeId.Create("explicit-prime-power-constant"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/MertensExplicitEnvelope.explicit_mertens_E1_le_four_fifths"),
                H("The convergent prime-power error is at most four fifths"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The Mertens constant E1 is the sum over prime natural numbers of log(p)/(p*(p-1)). A dyadic logarithm upper estimate uses log(2) at most 347/500. The rational weighted sum over the whole range 0 through 512, with the prime predicate in each summand, is checked directly by the Lean kernel and is at most 39/50. The remaining summands are bounded by 513/512 times the integral of log(t+512)/(t+512)^2 over the positive half-line. That integral equals (log(512)+1)/512. These bounds imply E1 at most 4/5; no native decision oracle or unproved numerical input is used."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("explicit-prime-log-sum-lower"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/MertensExplicitEnvelope.effective_E1p_lower"),
                H("A lower endpoint uniform beyond 286"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real x at least 286, the sum of log(p)/p over prime p at most x, minus log(x), is at least -91/50. The factorial integral lower estimate retains its negative linear term. Combining the von Mangoldt version with E1 at most 4/5 and log(x)/x at most 1/50 gives the stated endpoint."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("explicit-prime-log-sum-upper"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/MertensExplicitEnvelope.effective_E1p_upper"),
                H("An upper endpoint uniform beyond 286"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the same real domain, the prime logarithmic sum error is at most 2/25. The full Chebyshev prime-power decomposition separates squares, cubes and powers of exponent at least four; monotonicity makes their joint contribution at most 7*x/25. Fourteen explicitly selected prime powers provide a lower bound 319/500 for the difference between the von Mangoldt and prime logarithmic sums. The refined factorial upper estimate and (log(x)+1)/x at most 3/125 then give this endpoint."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("explicit-reciprocal-prime-product"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/MertensExplicitEnvelope.prime_product_upper_effective"),
                H("A reciprocal prime-product bound for every cutoff"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every real x at least 286, the reciprocal of the product of 1-1/p over all primes p at most x is at most exp(gamma)*log(x)*exp((19/10)/log(x)), where gamma is the Euler-Mascheroni constant. Both logarithmic sum endpoints hold on the entire tail, so their difference is exactly the required error width 19/10.")),
                    Paragraph(Text("The correction log(1-1/p)+1/p is nonpositive. Consequently the third Mertens error is at least the negative of its second error; partial summation bounds the second error by the endpoint width divided by log(x). Exponentiating the exact finite product identity gives the conclusion. The estimate can be consumed with local sigma factors and excluded-prime factors in a Robin argument, but those arithmetic assumptions and their connection to a particular integer are separate proof obligations."))),
                DescribeRole.Theorem))));
}

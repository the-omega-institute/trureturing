using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class PrimeSquareTailDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The prime reciprocal-square tail has uniform leading and finite-endpoint logarithmic estimates.",
        H("Uniform Prime Reciprocal-Square Tail"),
        Blocks(Describe.Lean(
            DescribeId.Create("prime-square-tail-uniform-real-cutoffs"),
            DeclarationHandle.Create(
                "D5/S3/Arith/Robin/PriceRecord/PrimeSquareTail.prime_square_tail_uniform"),
            H("Uniform finite-tail asymptotic"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For every real epsilon>0 there are real C>1 and Y>1 such that "
                    + "for every pair of real cutoffs y,z with Y<=y and C*y<=z, "
                    + "the absolute difference between y*log(y)*sum over primes y<p<=z "
                    + "of 1/p^2 and one is strictly less than epsilon. The sum is "
                    + "literally over the prime filter of Finset.Ioc(floorNat(y),floorNat(z)); "
                    + "the lower endpoint is strict even when y is an integer prime. "
                    + "Both thresholds precede both cutoff quantifiers. There is no "
                    + "theta-error hypothesis, RH hypothesis, record-integer restriction, "
                    + "or price parameter.")),
                Paragraph(Text(
                    "The PNT supplier EulerLayerRootCorrection.prime_number_limits gives "
                    + "theta(t)/t tending to one. The original finite_theta_abel_upper "
                    + "in ActualPriceRecordPrimeStructure supplies the upper estimate "
                    + "(1+3*rho)/(y*log(y)) uniformly for every upper cutoff. For the "
                    + "new lower estimate, Mathlib's exact real-endpoint Abel identity "
                    + "with coefficients log(p) at primes and zero elsewhere yields "
                    + "sum log(p)/p^2 >= (1-3*rho)/y-(1-rho)/z. "
                    + "The negative derivative reverses the lower theta comparison in "
                    + "the integral, and both endpoint corrections are retained.")),
                Paragraph(Text(
                    "Choose eta=min(epsilon/16,1/16) and C=1/eta. On (y,C*y], "
                    + "log(p)<=log(C*y), so the weighted lower bound implies a "
                    + "normalized unweighted bound at least "
                    + "(1-4*eta)*log(y)/log(C*y). Requiring "
                    + "Y>=exp(log(C)/eta) and Y>=2 makes log(y)/log(C*y) at least 1-eta; "
                    + "hence the normalized sum is at least 1-5*eta. Nonnegative "
                    + "summands and floor monotonicity extend it to every z>=C*y. "
                    + "The upper bound is 1+3*eta, giving the stated strict tolerance.")),
                Paragraph(Text(
                    "This is a repository derivation from the classical PNT and Abel "
                    + "summation. No literature novelty is claimed. It supplies a generic "
                    + "analytic input for the actual-record Euler-deficit leading constant; "
                    + "that further arithmetic application and RH are not conclusions "
                    + "of this theorem."))),
            DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("prime-square-tail-logarithmic-finite-endpoints"),
            DeclarationHandle.Create(
                "D5/S3/Arith/Robin/PriceRecord/PrimeSquareTail.prime_square_tail_logarithmic_refinements"),
            H("Second and third logarithmic terms at finite endpoints"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let S(y,z) be the sum of 1/p^2 over natural primes with y<p<=z. "
                    + "Put A2(t)=1/(t log(t))-1/(t log(t)^2) and "
                    + "A3(t)=A2(t)+2/(t log(t)^3). There is one real Y>exp(1) such "
                    + "that for all real z>=y>=Y, simultaneously "
                    + "abs(S(y,z)-A2(y)+A2(z))<=2/(y log(y)^3)+5/(y log(y)^9) "
                    + "and abs(S(y,z)-A3(y)+A3(z))<=6/(y log(y)^4)+5/(y log(y)^9). "
                    + "The lower endpoint is strict and the upper endpoint inclusive, "
                    + "including prime endpoints and z=y.")),
                Paragraph(Text(
                    "The existing theta_error_eight gives theta(t)-t=o(t/log(t)^8), "
                    + "hence a fixed threshold above which its absolute value is at most "
                    + "t/log(t)^8. Exact finite Abel summation with coefficients log(p) "
                    + "at primes and zero elsewhere and f(t)=1/(t^2 log(t)) compares "
                    + "S(y,z) with I1, where Ik is the integral from y to z of "
                    + "1/(t^2 log(t)^k). Both boundary errors together are at most "
                    + "2/(y log(y)^9), and the integral error is at most 3/(y log(y)^9). "
                    + "Finite integration by parts gives "
                    + "I1=A2(y)-A2(z)+2 I3=A3(y)-A3(z)-6 I4. Positivity and "
                    + "Ik<=1/(y log(y)^k) finish both estimates.")),
                Paragraph(Text(
                    "These are repository derivations from the classical prime number "
                    + "theorem and Abel summation, without a claim of literature novelty. "
                    + "They retain both endpoints for higher order prime-prefix and "
                    + "Robin correction estimates. Mere divergence of z/y is not asserted "
                    + "to remove the upper endpoint at second order. The complete "
                    + "predecessor-record correction and RH require further estimates."))),
            DescribeRole.Theorem))));
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class ActualLeastCrossingPriceRecordDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ActualLeastCrossingPriceRecord.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual least Robin-height crossings confine every occupied prime layer at a uniform positive price.",
        H("Uniform Positive-Price Predecessor Records"),
        Blocks(Describe.Lean(
            DescribeId.Create("uniform-actual-least-crossing-price-record"),
            DeclarationHandle.Create(Prefix + "uniform_actual_least_crossing_price_record"),
            H("One threshold through eta equal to one half"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let W(n)=log(sigma(1,n)/n), F(n)=W(n)-log(log(log(n))), and "
                    + "H(eta,n)=(log(n))^eta*(F(n)-gamma), with the existing total real "
                    + "definitions. There is T0>0, chosen before eta, such that for every "
                    + "0<eta<=1/2, every T>=T0, and every actual m>=3 with H(eta,m)>=T "
                    + "and H(eta,n)<T for all 3<=n<m, put X=log(m), L=log(X), c=39/20, "
                    + "lambda=(1-c*eta)/(X*L) and lambda0=1/(40*X*L). Both prices are "
                    + "positive. At each price m strictly beats every positive predecessor "
                    + "n<m for the literal goldenResourceObjective. Every prime p and "
                    + "1<=j<=v_p(m) satisfies p^j*log(p)<40*X*L. Moreover m divides "
                    + "ActualTwoPriceDefect.strictInteger(lambda0), and 5040 divides m.")),
                Paragraph(Text(
                    "The arbitrary-error envelope in ActualIntegerLogEnvelope is used "
                    + "with epsilon=1/20, giving F(n)-gamma<=(39/20)/log(log(n)) for all "
                    + "sufficiently large actual n. No support condition is imposed on n. "
                    + "With R=max(A,exp(2),log(30)), the shared uniform_actual_height_escape "
                    + "at R+1 chooses T0 independently of eta and ensures W(m)>R+1 "
                    + "and X>=exp(2). Put a=1-c*eta. Then 1/40<=a<=1 and lambda*X<=1. "
                    + "A hypothetical price rival has W(n)>=W(m)-1>R. The elementary "
                    + "divisor_log_le_log bound puts log(n)>R before the improved envelope "
                    + "is used. This proves n>=3 and log(log(n))>=2; the statement still "
                    + "compares all positive predecessors, including one and two.")),
                Paragraph(Text(
                    "For l>=2, beta>0 and 0<eta<=1/2, the strict scalar remainder is "
                    + "log(1+beta/l)-(c/l)*(1-exp(-eta*beta))>(1-c*eta)*beta/(l+beta). "
                    + "Differentiate the difference of these two sides. Writing b=c*eta "
                    + "and t=beta/l, its derivative numerator is "
                    + "exp(eta*beta)*(b+t)-b*(1+t)^2. The exponential tangent gives "
                    + "exp(eta*beta)>1+b*t, while "
                    + "(b+t)*(1+b*t)-b*(1+t)^2=t*(1-b)^2>=0. Thus the derivative "
                    + "is strictly positive away from zero, where the difference vanishes.")),
                Paragraph(Text(
                    "For the rival put Y=log(n), l=log(Y), beta=log(X)-log(Y), "
                    + "E=F(n)-gamma and delta=W(m)-W(n). The rival bounds delta by "
                    + "a*(1-exp(-beta))/L<a*beta/L. The scalar remainder and E<=c/l "
                    + "then make delta+E*(1-(Y/X)^eta)-log(L/l) strictly negative, even "
                    + "when E is negative. The exact literal height cancellation gives "
                    + "H(eta,m)<H(eta,n), contradicting leastness. Lowering lambda to "
                    + "lambda0 preserves strictness because log(n)<X.")),
                Paragraph(Text(
                    "The positive lambda0 record satisfies the hypotheses of "
                    + "ActualPriceRecordPrimeStructure.price_record_divides_strictInteger, "
                    + "so m divides the canonical strictInteger(lambda0). The existing "
                    + "factorization comparison places every occupied layer of m in this "
                    + "strict inventory. Applying strict_layer_iff gives "
                    + "lambda0<goldenLayerMarginal(p,j). The reciprocal-power "
                    + "marginal bound gives the literal strict cutoff. Positive-price records "
                    + "also give strict abundancy records; W(m)>log(30) permits the existing "
                    + "5040 theorem to apply.")),
                Paragraph(Text(
                    "This combines the repository's arithmetic and analytic results with "
                    + "a quantitative scalar estimate; no literature priority is claimed. "
                    + "No crossing existence, height unboundedness, signed upper bound, "
                    + "Robin inequality or RH follows here. The conclusion compares "
                    + "predecessors only. It supplies neither global optimality of m, "
                    + "conditions on absent layers nor equality with the strict inventory. "
                    + "The full RH goal and its signed-upper and unboundedness gaps remain open."))),
            DescribeRole.Theorem))));
}

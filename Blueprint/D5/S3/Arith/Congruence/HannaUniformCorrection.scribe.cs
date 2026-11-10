using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;
internal sealed class HannaUniformCorrectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Congruence/HannaUniformCorrection.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete uniform corrected-Euler power family", H("The complete uniform corrected-Euler power family"), Blocks(
            Paragraph(Text("The parameter s is an integer. The contract uses all s>=2 and every positive natural index. The internal integer weight uses s.toNat; weight_cast proves equality with the requested rational integer power for every s>=0, including zero. All appearances of s.toNat-1 and s.toNat*(r-1)-r represent the corresponding nonnegative integer exponents on their stated domains. The actual F is exp(sum over n>=1 of (n^s-a_s(n))*X^n/n). Its integer coefficients f are extracted independently from the canonical Euler series and then identified with the actual rational coefficients. Su, Theorems 7.1-7.2, owns the known square-weight conclusions; the supplied note attributed to Haobo Ma and Wenlin Zhang motivates the uniform extension. The note's authorship and literature novelty of the all-s extension are unverified. Bala owns the cited universal-shift theorem for A082579, which is outside this module.")),
            Node("weight", "weight", "The integer recursion uses the natural representative of the nonnegative integer weight. Negative parameters are not asserted to model negative-power integrality.", DescribeRole.Definition),
            Node("a", "a", "The correction is the generic bounded residue for the integer power weight.", DescribeRole.Definition),
            Node("c", "c", "The positive-index Euler exponents are the generic recursively constructed integer ledger.", DescribeRole.Definition),
            Node("F", "F", "This is the literal rational formal exponential with integer power parameter s. Its logarithmic input has constant coefficient zero.", DescribeRole.Definition),
            Node("IsPowerCorrection", "IsPowerCorrection", "The predicate states exactly the positive-index bounds and integrality of that literal exponential, with no prescribed value at zero.", DescribeRole.Definition),
            Node("weight_cast", "weight cast", "For every nonnegative integer s and every natural n, the cast integer weight is exactly the rational integer power n^s. This discharges the domain correspondence.", DescribeRole.Theorem),
            Node("correction_spec", "correction spec", "The generic integer-weight construction supplies boundedness and actual exponential integrality.", DescribeRole.Theorem),
            Node("correction_exists_unique", "correction exists unique", "Existence and uniqueness hold on every positive index for every integer s>=0. Whole-function uniqueness is deliberately absent because the entry at zero is unused.", DescribeRole.Theorem),
            Node("euler_representation", "euler representation", "The integer Euler series, indexed by part size i+1, maps to the actual rational exponential. The separate HasProd theorem in the canonical owner proves it is an actual infinite Euler product.", DescribeRole.Theorem),
            Node("exponent_bounds", "exponent bounds", "Strong induction bounds the proper-divisor ghost between zero and the proper-divisor power sum. The additive-n divisor budget and the correction interval force the new exponent to be a positive integer, at most n^(s-1).", DescribeRole.Theorem),
            Node("correction_prime_power", "correction prime power", "The generalized original owner induction treats every prime including two and every positive power. At the first prime power the representative is p-1; at higher powers both weights vanish modulo p^r because s>=2.", DescribeRole.Theorem),
            Node("exponent_prime", "exponent prime", "Subtracting actual divisor ghosts at p and one gives p*c_s(p)=p^s-p. Integer cancellation yields p^(s-1)-1.", DescribeRole.Theorem),
            Node("exponent_prime_power", "exponent prime power", "At r>=2, the equal corrections cancel. The exponent s*(r-1)-r is nonnegative on the complete stated domain; exact power algebra and cancellation yield the displayed formula.", DescribeRole.Theorem),
            Node("f", "f", "These are ordinary integer coefficients of the canonical Euler series. They are not defined by a recurrence or a requested partition count.", DescribeRole.Definition),
            Node("coefficient_eq", "coefficient eq", "Mapping the actual integer Euler series into rationals identifies f_s(n) with coefficient n of F_s.", DescribeRole.Theorem),
            Node("ColouredPartition", "ColouredPartition", "The independent finite generic coloured carrier is specialized to (c_s(d)).toNat. Positive-index exponent bounds prove this natural colour count faithfully equals the integer exponent at every occurring part.", DescribeRole.Definition),
            Node("coefficient_cardinality", "coefficient cardinality", "The independent carrier counts the actual coefficients. The proof transports nonnegative Euler exponents to natural colours and consumes the generic cardinality correspondence.", DescribeRole.Theorem),
            Paragraph(Text("For every integer s, including negative parameters, f_s(0)=1 follows directly from the definitions. Set b(i)=c_s(i+1). By "),
                Ref("D5/S1/Recurrence/Witt/HannaDiagonalGhostPowerIntegrality.eulerSeries"),
                Text(", f_s(0) is coefficient zero of ledgerProduct b 0. The definition "),
                Ref("D5/S1/Recurrence/Witt/PrimitiveEulerLedger.ledgerProduct"),
                Text(" makes this the product over the empty range, hence the constant series one, whose coefficient zero is one. This argument concerns the integer Euler series and requires neither nonnegative s nor an assertion about negative-power integrality.")),
            Paragraph(Text("For every integer s>=0 and every natural n, the same actual coefficients satisfy the integer identity n*f_s(n)=sum over 1<=j<=n of (j^(s.toNat)-a_s(j))*f_s(n-j). Apply "),
                Ref("D5/S1/Recurrence/Witt/EulerExponentialCoefficients.coefficient_recurrence"),
                Text(" with g(m)=((weight(s,m)-a_s(m)):Q). Its exponentialSum g is F_s because weight_cast identifies the integer weight with the rational integer power. The equality "),
                Ref("D5/S3/Arith/Congruence/HannaUniformCorrection.coefficient_eq"),
                Text(" identifies every rational coefficient with the cast of f_s. Injectivity of the integer-to-rational cast gives the displayed integer identity; replacing j by k+1 gives exactly the sum over k in range n. At n=0 both sides are zero. The reusable recurrence itself extracts coefficients from "),
                Ref("D5/S1/Recurrence/Witt/HannaDiagonalGhostPowerIntegrality.exponential_sum_equation"),
                Text(": the positive-degree ghost series has coefficient g(j), the derivative contributes n times coefficient n, and multiplication gives the finite convolution. This is a consequence of the generic supplier and the coefficient correspondence, without defining f_s recursively.")),
            Node("coefficient_positive", "coefficient positive", "The corrected ghost n^s-a_s(n) is strictly positive for s>=2 and n>0. The general exponential positivity theorem therefore applies to the actual f_s.", DescribeRole.Theorem),
            Node("coefficient_monotone", "coefficient monotone", "The difference (n+1)^s-n^s is at least n+1 for s>=2 and n>=1. The correction bounds make corrected ghosts increasing, with first ghost one. The general convolution comparison proves nondecreasing f_s.", DescribeRole.Theorem),
            Node("correction_boundary", "correction boundary", "At weights zero and one, the bounded positive-index corrections are respectively zero and n-1. Their literal corrected ghosts equal one. Uniqueness comes from the same generic construction.", DescribeRole.Theorem),
            Node("F_boundary", "F boundary", "Both actual boundary exponentials equal the inverse of one minus X. Coefficient induction proves exp(sum X^n/n) has every coefficient one; the formal geometric-series identity identifies its inverse. At weight one and prime-square index p^2, the correction is p^2-1, so the constant prime-power formula starts at weight two. For J_s(n)=sum over d dividing n of mu(n/d)*d^s, the generic Mobius identity at weight(s) gives n*c_s(n)=J_s(n)-sum over d dividing n of mu(n/d)*a_s(d). The generic logarithmic estimate at the same weight gives |c_s(n)-J_s(n)/n|<=1+log(n) for every positive n.", DescribeRole.Theorem))));
    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("hannauniformcorrection-" + (name == "F" ? "formal-exponential" : name.ToLowerInvariant().Replace("_", "-"))),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}

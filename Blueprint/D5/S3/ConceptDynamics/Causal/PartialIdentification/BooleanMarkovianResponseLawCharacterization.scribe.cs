using Mathlib.Meta.NormNum;

namespace Blueprint.D5.S3.ConceptDynamics.Causal.PartialIdentification
{
    public static class BooleanMarkovianResponseLawCharacterization
    {
        public static readonly TheoremDeclaration BooleanMarkovianIffDeterminantZero = new()
        {
            Name = "boolean_markovian_iff_determinant_zero",
            Statement = "A normalized nonnegative law on Bool × Bool is a product of two normalized coordinate laws if and only if its two-by-two determinant vanishes.",
            Proof = "Necessity is the product determinant identity. For sufficiency, take the two coordinate marginals. Normalization and the determinant equation show cell by cell that their product reconstructs the original law."
        };

        public static readonly TheoremDeclaration BenefitResponseVectorDeterminantGap = new()
        {
            Name = "benefitResponseVector_determinant_gap",
            Statement = "For the explicit Boolean benefit response vector with intervention marginals p0 and p1 and benefit target q, the signed determinant equals (1 - p0) * p1 - q.",
            Proof = "Expand the four response cells and normalize the resulting polynomial identity by exact ring arithmetic."
        };

        public static readonly TheoremDeclaration DeterminantZeroPointIdentifiesBenefit = new()
        {
            Name = "determinant_zero_point_identifies_benefit",
            Statement = "A normalized Boolean outcome-response law with vanishing determinant and fixed control and treatment success marginals has benefit mass (1 - p0) * p1.",
            Proof = "Convert determinant zero to response-coordinate factorization using the complete Boolean characterization, then invoke the coordinate-factorization identification theorem."
        };

        public static readonly TheoremDeclaration BenefitResponseLawFactorizedIff = new()
        {
            Name = "benefitResponseLaw_factorized_iff",
            Statement = "Within the explicit sharp Frechet witness family, the response law factorizes exactly when q = (1 - p0) * p1.",
            Proof = "Use the determinant characterization and the exact determinant-gap identity in both directions."
        };

        public static void Register()
        {
            _ = BooleanMarkovianIffDeterminantZero;
            _ = BenefitResponseVectorDeterminantGap;
            _ = DeterminantZeroPointIdentifiesBenefit;
            _ = BenefitResponseLawFactorizedIff;
        }
    }
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Parking;

internal sealed class PeakTieDescentRecurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/PermutationPatterns/alexandersson2026parking");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An insertion operator on trivariate polynomials gives the recurrence and recovers Alexandersson’s bivariate operator at descent marker one.",
        H("A descent refinement for bounded parking words"),
        Blocks(
            Node("literalParking", "The finite set of bounded parking words", DescribeRole.Definition,
                "Filter the length-n words on 1 through m by the sorted rank test."),
            Node("mem_literalParking", "Finite-set membership", DescribeRole.Theorem,
                "Membership in the finite set is equivalent to the literal bounded parking predicate."),
            Node("G", "The weighted enumerator", DescribeRole.Definition,
                "Sum the literal trivariate weight over the bounded parking words in a commutative semiring."),
            Node("topFiber", "The finite maximum-letter fiber", DescribeRole.Definition,
                "Keep exactly the words in which the upper-bound letter occurs r times."),
            Node("coefficient_fiber", "Exactly r copies of the maximum", DescribeRole.Theorem,
                "For 2 ≤ m ≤ n and 1 ≤ r ≤ n − m + 1, the weight sum on the maximum-letter fiber equals the sum of the degree-r kernel coefficient over shorter words of length n − r and bound m − 1."),
            Node("parking_base", "The bound-one initial condition", DescribeRole.Theorem,
                "There is just the word of n ones at bound one. Its weight is u^(n−1), which also gives equation (3) at v = 1."),
            Node("parkingPolynomial", "The trivariate polynomial", DescribeRole.Definition,
                "The variables at indices zero, one and two mark strict interior peaks, adjacent ties and strict adjacent descents, respectively."),
            Node("ParkingPolynomial", "The polynomial type", DescribeRole.Definition,
                "The natural-coefficient polynomial ring in three variable positions."),
            Node("insertionOperator", "Linear insertion on trivariate polynomials", DescribeRole.Definition,
                "For retained length ℓ and insertion size r, replace each input monomial by its degree-r kernel coefficient and extend additively with natural multiplicities."),
            Node("insertionOperator_monomial", "The operator on a monomial", DescribeRole.Theorem,
                "The operator on t^p u^k v^d takes the coefficient of z^r in the six-factor kernel with statistics ℓ, p, k and d."),
            Node("parkingPolynomial_operator_recurrence", "The trivariate insertion recurrence", DescribeRole.Theorem,
                "For 2 ≤ m ≤ n, the terms with no m give the same-length enumerator at bound m − 1. For each r from 1 through n − m + 1, apply the insertion operator to the enumerator at length n − r and bound m − 1."),
            Node("bivariateInsertionOperator", "The bivariate operator of equation (11)", DescribeRole.Definition,
                "For a bivariate polynomial F, substitute the actual power series B/A² and C/A, multiply by E² A^(ℓ−1), and extract the coefficient of z^r."),
            Node("bivariateParkingPolynomial", "The bivariate polynomial", DescribeRole.Definition,
                "The variables at indices zero and one mark peaks and ties. Each descent contributes the unit weight."),
            Node("specialize_descent", "Substitute one for the descent marker", DescribeRole.Theorem,
                "The polynomial homomorphism mapping the third variable to one and keeping the first two variables yields the bivariate parking polynomial."),
            Node("insertEq11", "Equation (11) on the enumerator", DescribeRole.Definition,
                "Apply the bivariate insertion operator to the peak-and-tie enumerator of the retained length and bound."),
            Node("insertEq11_coeff", "The specialized coefficient sum", DescribeRole.Theorem,
                "For a positive retained length the bivariate operator is the sum of the specialized degree-r kernel coefficients over the literal retained words."),
            Node("parking_recurrence_eq11", "Recover equation (2)", DescribeRole.Theorem,
                "Apply the specialized operator in each positive maximum-letter fiber. The insertion range and the zero-multiplicity term are precisely those of equation (2)."),
            Node("result", "Problem 10.3", DescribeRole.Theorem,
                "The bound-one initial values, arbitrary-length trivariate recurrence, descent-marker substitution, equation (10) factors and equation (2) with its equation (11) operator hold on the bounded parking-word enumerators.")),
        []));

    private static DocumentBlock Node(
        string declaration, string title, DescribeRole role, string prose,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("peaktiedescentrecurrence-" +
                (declaration == "ParkingPolynomial" ? "polynomial-type" :
                    declaration.ToLowerInvariant().Replace('_', '-'))),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))),
            role, resolution);
}

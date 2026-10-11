using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Probability;

internal sealed class FiniteCommonMarginalSupermodularDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Probability/FiniteCommonMarginalSupermodular.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A diagonal law maximizes real supermodular expectations with four equal finite marginals.",
        H("Four-coordinate finite common-marginal comparison"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("common-marginal-supermodular-diagonal"),
                DeclarationHandle.Create(Prefix + "common_marginal_supermodular_le_diagonal"),
                H("Diagonal maximization"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Estimation/puccettiwang2015dependence")),
                Blocks(
                    Paragraph(Text(
                        "Let C be any nonempty finite linearly ordered set. A joint law p on " +
                        "the functions from Fin 4 to C has arbitrary nonnegative real weights " +
                        "whose sum is one. Let m be a real function on C. For every coordinate " +
                        "i and every t in C, the sum of p(x) over all x with x(i)=t is exactly " +
                        "m(t). These identities imply both nonnegativity and normalization of m.")),
                    Paragraph(Text(
                        "Let f be any real function on the four-coordinate product. Suppose " +
                        "that f(x)+f(y) is at most f(x meet y)+f(x join y) for every x and y, " +
                        "where meet and join take the minimum and maximum in each coordinate. " +
                        "Then the sum of p(x)f(x) over the whole product is at most the sum " +
                        "of m(t)f(t,t,t,t) over C.")),
                    Paragraph(Text(
                        "The test may take negative values and need not be increasing. " +
                        "The law may have zero cells, irrational masses and arbitrary dependence. " +
                        "Repeated coordinates, a singleton support, and atoms with zero " +
                        "marginal mass are included.")),
                    Paragraph(Text(
                        "Order the scalar support and follow the diagonal through adjacent " +
                        "levels. Within each level raise coordinates in the order 0,1,2,3. " +
                        "The difference in f at each such step defines a coordinate increment. " +
                        "For an arbitrary product point, clip each coordinate at the current " +
                        "level. Supermodularity compares each clipped increment with the " +
                        "corresponding diagonal increment. Summing the increments gives a " +
                        "separable upper bound, with equality at every diagonal point. " +
                        "Taking its expectation uses only the exact one-coordinate marginals.")),
                    Paragraph(Text(
                        "This is the finite common-support form of the classical comonotonic " +
                        "supermodular comparison in Theorem 2.1(d) of the cited source. " +
                        "In the four-rate argument, " +
                        "equations 16.25 and 16.26 use this comparison for H=F minus x(0)x(1). " +
                        "The present result supplies that expectation comparison when the " +
                        "common scalar support is finite. A continuum passage, the proof of " +
                        "supermodularity of that particular H, and the second-moment identity " +
                        "must be established separately."))),
                DescribeRole.Theorem)),
        []));
}

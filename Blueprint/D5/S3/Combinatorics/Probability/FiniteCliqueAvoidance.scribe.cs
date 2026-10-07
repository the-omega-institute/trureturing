using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Probability;

internal sealed class FiniteCliqueAvoidanceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Probability/FiniteCliqueAvoidance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive coordinate-deletion comparison controls the actual probability of avoiding "
        + "a finite family of dependent events and bounds queries under one conditioned law.",
        H("Finite coordinate-clique avoidance"),
        Blocks(
            Paragraph(Text(
                "Fix a finite probability space with rational weights mu and a finite coordinate "
                + "set P. The coordinate type itself need not be finite. For each nonempty finite "
                + "support S, let A(S) be a bad event. Avoids(A,R) means that every event whose "
                + "nonempty support is contained in R fails; Z(R) is its probability under mu. "
                + "All these probabilities refer to this same original law.")),
            Describe.Lean(
                DescribeId.Create("relative-avoidance-and-query"),
                DeclarationHandle.Create(Prefix + "finite_clique_avoidance"),
                H("Relative avoidance and conditional queries"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/GraphInvariants/houghnielsen2017restricted")),
                Blocks(
                    Paragraph(Text(
                        "Let t(S) bound the probability of each nonempty event A(S). Assume that "
                        + "A(S) is independent of the entire avoidance event on R whenever S and R "
                        + "are disjoint subsets of P. Pairwise independence of individual bad "
                        + "events does not supply this premise. No independence requirement is "
                        + "imposed on an empty event support.")),
                    Paragraph(Text(
                        "Let rho be a rational function on coordinate sets, equal to one at the "
                        + "empty set and strictly positive on every subset of P. For p outside R "
                        + "with insert(p,R) contained in P, its deletion recurrence is exact: "
                        + "adjoining p to R subtracts from rho(R) the sum, "
                        + "over U contained in R, of t(insert(p,U)) times rho(R minus U). "
                        + "Then rho(T) is at most Z(T), Z(T) is positive, and for every S contained "
                        + "in T contained in P the ratio Z(T)/Z(S) is at least rho(T)/rho(S).")),
                    Paragraph(Text(
                        "Condition mu on avoiding every bad event in P. For any query event E "
                        + "and Q contained in P, suppose E is independent of the entire avoidance "
                        + "event on P minus Q. The probability of E under this one conditioned law "
                        + "is at most mu(E) times rho(P minus Q)/rho(P). The law is constructed "
                        + "before the query is chosen; it is not separately selected for each query.")),
                    Paragraph(Text(
                        "The proof first bounds the mass lost when a coordinate is adjoined by "
                        + "an actual union of new bad events. Strong induction compares the "
                        + "smaller avoidance ratios. These comparisons upper-bound each "
                        + "subtracted loss, and the exact recurrence supplies the next positive "
                        + "ratio. Multiplication along nested subsets gives the relative result. "
                        + "For a query, discard bad events touching Q and use independence on "
                        + "the complementary coordinate set.")),
                    Paragraph(Text(
                        "This is the finite rational coordinate-deletion argument of Hough and "
                        + "Nielsen's clique-Shearer theorem with upper activities. Identifying "
                        + "rho with a specific independent-set polynomial, proving its positivity, "
                        + "and constructing coordinate independence for a particular arithmetic "
                        + "source remain separate application obligations. The statement neither "
                        + "asserts an infinite-coordinate extension nor settles unrestricted "
                        + "odd covering systems."))),
                DescribeRole.Theorem)),
        []));
}

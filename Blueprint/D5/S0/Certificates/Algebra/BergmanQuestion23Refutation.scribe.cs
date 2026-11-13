using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates.Algebra;

internal sealed class BergmanQuestion23RefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/bergman2014eggert");

    private static readonly LibraryNoteRef Stanley =
        LibraryNoteRef.Create("D5/L/Certificates/stanley1978hilbert");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A coefficient model for the positive ideal of a truncated monomial idealization.",
        H("Bergman's Question 23: the monomial model"),
        Blocks(
            Node("mixed-products", "Mixed product spaces", "mixedPower",
                "Index k means exactly k+1 factors from V. The recursion uses the span of "
                    + "the actual bilinear multiplication image of two subspaces, rather than "
                    + "the set of pure powers of individual vectors."),
            Node("relative-annihilator", "The relative annihilator", "relativeAnnihilator",
                "This is a submodule of V whose elements annihilate every vector of W. "
                    + "The quotient in the question is the quotient of V by this submodule."),
            Node("original-question", "The complete universal question", "claim",
                "For every field and every vector space with an associative commutative "
                    + "bilinear multiplication, every finite dimensional subspace V and every "
                    + "positive exponent, the question asks whether the dimension of the "
                    + "annihilator quotient is at most the dimension of the mixed product "
                    + "space. No identity, finite ambient dimension, nilpotence or "
                    + "characteristic hypothesis is imposed. Ordinary small carriers include "
                    + "all the proposed finite counterexamples."),
            Node("monomials", "Monomial labels", "Monomial",
                "A monomial is a multiset on m variables. Its cardinality is its total degree. "
                    + "Multiset addition adds exponents and uses no factorials."),
            Node("positive-labels", "Positive monomials", "PositiveIndex",
                "The e labels have degrees from one through t, inclusive."),
            Node("dual-labels", "Dual monomials", "DualIndex",
                "The f labels have underlying monomial degrees from zero through t."),
            Node("basis-labels", "The finite carrier", "Model",
                "The absorbing zero is separate from the e and f families. The contracted "
                    + "algebra has precisely the nonzero labels as its vector space basis."),
            Node("multiplication", "The truncated multiplication", "modelMul",
                "Two e labels multiply by multiset addition when their sum has degree at "
                    + "most t, and give zero otherwise. An e label a times an f label b gives "
                    + "f(b-a) when a is contained in b with multiplicity, and zero otherwise. "
                    + "Two f labels multiply to zero. The symmetric rule is extended "
                    + "bilinearly through the existing contracted algebra construction."),
            Node("ambient-space", "The positive ideal", "Ambient",
                "Over any field, this is the contracted algebra of the finite carrier. "
                    + "It models the positive ideal, rather than the entire unital "
                    + "Stanley idealization."),
            Node("grading", "The reversed dual grading", "labelDegree",
                "An e label has its monomial degree. The degree of an f label b is "
                    + "t+1 minus the degree of b, so every nonzero label has positive degree."),
            Node("layers", "The actual homogeneous subspaces", "layer",
                "The degree d subspace consists of the finitely supported coefficient "
                    + "vectors supported on labels of degree d."),
            Node("dimension-ratio", "The actual quotient-to-product dimension ratio", "dimensionRatio",
                "Use the real quotient of the actual annihilator quotient dimension by the "
                    + "dimension of the actual n-fold mixed product span of the designated "
                    + "degree-one subspace, in the model with truncation t=n+1."),
            Node("family-properties", "The full family specification", "familyProperties",
                "Let R be the positive ideal with t=n+1, V its degree-one subspace, W its "
                    + "n-fold mixed product space and A the annihilator of W in V. The "
                    + "specification includes finite dimensional R and W, W equal to the "
                    + "degree-n subspace, A equal to zero, all four dimension formulas, the "
                    + "exact positive dimension deficit, annihilation of every product of "
                    + "n+3 ambient elements and the stated lower bound for the real ratio."),
            Describe.Lean(DescribeId.Create("full-family"),
                DeclarationHandle.Create(Prefix + "family"), H("The complete parameter family"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source, Stanley),
                Blocks(Paragraph(Text(
                    "For every field F and every integer n at least two, every integer m at "
                    + "least three satisfies the full family specification. The actual n-fold "
                    + "mixed product space is exactly the degree-n subspace, with e labels of "
                    + "monomial degree n and f labels of monomial degree two; its relative "
                    + "annihilator in V is zero. R and the product space are finite dimensional.")),
                    Paragraph(Text(
                    "The dimensions of R, V, W and V/A are respectively two times binomial "
                    + "(m+n+1,n+1) minus one; m plus binomial (m+n,n+1); binomial "
                    + "(m+n-1,n) plus binomial (m+1,2); and the dimension of V. The exact "
                    + "quotient-minus-product deficit is binomial (m+n-1,n+1) minus "
                    + "binomial (m,2), at least binomial (m,3), and the quotient dimension "
                    + "is strictly larger than the product dimension.")),
                    Paragraph(Text(
                    "Every product of n+3 elements of R is zero. The real dimension ratio "
                    + "is at least (m+n)/(2(n+1)). For each fixed F and n, every real C "
                    + "is exceeded by the actual ratio for some m at least three. The "
                    + "construction is a coefficient presentation of the classical Stanley "
                    + "idealization; see Library/Certificates/stanley1978hilbert.md. "
                    + "The entire unital idealization has one more dimension than R."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("question-twenty-three-refuted"),
                DeclarationHandle.Create(Prefix + "result"), H("Question 23 has a negative answer"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source, Stanley),
                Blocks(Paragraph(Text(
                    "The complete universal assertion is false. Its literal negation follows "
                    + "by taking F rational, n equal to two and m equal to three in the "
                    + "full family. The actual positive ideal has dimension 39, V and its "
                    + "annihilator quotient have dimension 13, and V squared has dimension "
                    + "12. No extra assumption is added to the original universal claim."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("bergman-question23"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string id, string title, string declaration, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source, Stanley),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}

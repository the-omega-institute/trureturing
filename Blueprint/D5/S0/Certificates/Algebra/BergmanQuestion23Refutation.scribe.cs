using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates.Algebra;

internal sealed class BergmanQuestion23RefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/bergman2014eggert");

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
                    + "vectors supported on labels of degree d."))));

    private static DocumentBlock Node(string id, string title, string declaration, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}

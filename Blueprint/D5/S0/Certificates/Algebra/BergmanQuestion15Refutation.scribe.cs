using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates.Algebra;

internal sealed class BergmanQuestion15RefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S0/Certificates/Algebra/BergmanQuestion15Refutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/bergman2014eggert");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Distinct nonzero sixth powers of three semigroup elements do not prevent "
            + "a nonzero complex vector in their contracted span from having zero sixth power.",
        H("Bergman's Question 15 on Contracted Semigroup Algebras"),
        Blocks(
            Node("contracted-space", "The contracted vector space", "Contracted",
                "The vector space has the nonzero semigroup elements as a free basis.",
                DescribeRole.Definition),
            Node("contracted-basis", "Contracted basis images", "delta",
                "The absorbing semigroup zero maps to the zero vector. Every other element "
                    + "maps to its basis vector with coefficient one.", DescribeRole.Definition),
            Node("contracted-product", "Bilinear multiplication", "product",
                "Extend the semigroup product bilinearly, sending products equal to the "
                    + "absorbing element to the zero vector. Associativity, commutativity, "
                    + "and distributivity follow from these basis products.", DescribeRole.Definition),
            Node("positive-power", "Positive powers without an identity", "positivePower",
                "Index zero means exponent one. Increasing the index multiplies once more "
                    + "by the same element, so index n means exponent n+1.", DescribeRole.Definition),
            Node("original-question", "The universal assertion in Question 15", "claim",
                "For an arbitrary commutative semigroup with absorbing zero, a finite subset, "
                    + "a positive exponent, and a field of characteristic zero, assume the power "
                    + "map is injective on the subset and preserves nonzero elements. The question "
                    + "asks whether the same nonannihilation holds on the contracted linear span. "
                    + "The closed assertion uses ordinary small carriers, including infinite carriers; "
                    + "the finite counterexample already belongs to those universes.",
                DescribeRole.Definition),
            Node("finite-carrier", "The 59 semigroup elements", "Model",
                "There are 55 singleton monomials of degrees one through five, three terminal "
                    + "classes of degree six, and the absorbing zero.", DescribeRole.Definition),
            Node("monomial-labels", "The retained terminal classes", "label",
                "Retain exactly the three classes A, B and C listed in the Route section of "
                    + "Problems/bergman-question15.md from the degree-six monomials; "
                    + "every remaining monomial becomes zero.", DescribeRole.Definition),
            Node("finite-product", "The finite multiplication", "modelMul",
                "Add the exponent triples of singleton classes and take their retained label. "
                    + "Multiplication involving zero or a terminal class gives zero.",
                DescribeRole.Definition),
            Node("numeric-product", "The numeric multiplication table", "tableMul",
                "The numeric table represents the same exponent addition and contraction. "
                    + "Its equality with the monomial rule is checked in the proof.",
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("question-fifteen-refuted"),
                DeclarationHandle.Create(Prefix + "result"), H("Question 15 has a negative answer"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Over the complex numbers take the three degree-one generators and exponent six. "
                    + "Their powers are the distinct nonzero terminal classes A, B and C. With ζ a "
                    + "primitive cube root, the vector delta_x + ζ delta_y + ζ² delta_z has x "
                    + "coefficient one. Its sixth power has coefficient 21(1+ζ+ζ²) in each terminal "
                    + "class and vanishes. Mixed monomials cause cancellation despite the pure powers "
                    + "remaining distinct."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("bergman-question15"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}

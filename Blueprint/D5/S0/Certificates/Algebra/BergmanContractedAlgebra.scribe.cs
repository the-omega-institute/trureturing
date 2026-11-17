using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates.Algebra;

internal sealed class BergmanContractedAlgebraDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S0/Certificates/Algebra/BergmanContractedAlgebra.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/bergman2014eggert");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The contracted algebra construction also applies to noncommutative semigroups with zero.",
        H("Contracted semigroup algebras without an identity"),
        Blocks(
            Node("basis-product", "Products of scalar basis vectors", "single_mul",
                "Let F be any field and S have a multiplication and a distinguished zero. "
                    + "Use exactly the contracted vector space and bilinear product of the "
                    + "Question 15 construction. The product of the scalar basis vectors "
                    + "r delta_a and t delta_b is (rt) delta_(ab). If ab is zero, its image "
                    + "is the zero vector, rather than a new basis vector.", DescribeRole.Theorem),
            Node("left-scalars", "Scalars and left multiplication", "contractedSMulCommClass",
                "The field action commutes with multiplication by an algebra element. "
                    + "This is the scalar law a(r b)=r(ab).", DescribeRole.Definition),
            Node("scalar-tower", "Scalars in the first factor", "contractedScalarTower",
                "The other scalar law is (r a)b=r(ab). Together these laws express the "
                    + "bilinearity of the original product.", DescribeRole.Definition),
            Node("basis-multiplication", "Multiplicative basis images", "delta_mul",
                "For every semigroup with absorbing zero, delta_a delta_b=delta_(ab), "
                    + "including when a, b or their product is zero. No commutativity "
                    + "hypothesis is used.", DescribeRole.Theorem),
            Node("associative-algebra", "The nonunital associative ring", "contractedRing",
                "If S is a semigroup with absorbing zero, its original contracted vector "
                    + "space over any field is a nonunital associative ring, with the same "
                    + "multiplication. Associativity reduces by linear induction to the "
                    + "semigroup associativity law. Neither an identity nor commutativity "
                    + "is required. For a commutative S the existing commutative structure "
                    + "uses this identical product.", DescribeRole.Definition),
            Node("linear-extension", "The induced linear map", "map",
                "Given a function f from S to T, send each nonzero basis element s to "
                    + "delta_(f(s)) and extend linearly over the same field. This construction uses "
                    + "the original nonzero-element basis on each carrier.", DescribeRole.Definition),
            Node("map-basis", "The image of every semigroup element", "map_delta",
                "When f sends zero to zero, the induced map sends every delta_s to "
                    + "delta_(f(s)), including s=0. A nonzero element may be sent to zero, "
                    + "as is necessary for a contracted quotient map.", DescribeRole.Theorem),
            Node("map-product", "Multiplication under the linear extension", "map_mul",
                "Suppose S and T are semigroups with absorbing zero, and f preserves "
                    + "zero and multiplication. For arbitrary contracted vectors a and b, "
                    + "the induced linear map sends ab to the product of their images. "
                    + "The assertion applies to all vectors, rather than only basis vectors "
                    + "or individual powers, and imposes no commutativity hypothesis.",
                DescribeRole.Theorem),
            Node("algebra-homomorphism", "A nonunital algebra homomorphism", "mapHom",
                "The same linear extension is a nonunital algebra homomorphism whenever "
                    + "f preserves zero and multiplication. Its addition and scalar laws "
                    + "come from the linear map, and its product law is the preceding "
                    + "identity. The field needs no characteristic-zero assumption for "
                    + "these structural statements.", DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}

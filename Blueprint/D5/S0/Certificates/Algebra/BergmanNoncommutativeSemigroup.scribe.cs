using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates.Algebra;

internal sealed class BergmanNoncommutativeSemigroupDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/Algebra/BergmanNoncommutativeSemigroup.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/bergman2014eggert");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two actual noncommutative nilpotent constructions preserve contracted span cancellation.",
        H("Noncommutative semigroups and contracted witnesses"),
        Blocks(
            Node("four", "The four-element auxiliary semigroup", "FourElement",
                "The carrier consists of the four distinct elements zero,p,q,r. Its "
                + "only nonzero product is pq=r. Every triple product is zero in "
                + "either bracketing, so the multiplication is associative. In "
                + "particular pq differs from qp=zero.", DescribeRole.Definition),
            Node("product", "The full Cartesian product", "ProductModel",
                "Take the full direct product of the actual cyclic xyz-zero quotient "
                + "Model 6 true with the four-element auxiliary semigroup. Every pair "
                + "occurs, including pairs with exactly one zero component. "
                + "Multiplication is componentwise and only the pair (zero,zero) is "
                + "the absorbing zero. The size is therefore 49 times 4, or 196; "
                + "this construction is distinct from a smash product.", DescribeRole.Definition),
            Node("include", "The original quotient inside the product", "includeZero",
                "The map s to (s,zero) is injective, preserves zero and preserves "
                + "multiplication on the actual quotient49. No quotient elements "
                + "are identified by this inclusion.", DescribeRole.Definition),
            Node("embedding", "The contracted algebra embedding", "embedding",
                "Apply the existing BergmanContractedAlgebra.mapHom to the literal "
                + "inclusion s to (s,zero). This is an F-linear multiplicative map "
                + "between the original contracted Finsupp algebras, with no "
                + "commutativity assumption on the target. The induced linear map "
                + "of the first projection is a left inverse, as checked on every "
                + "scalar basis vector and extended linearly. It therefore gives "
                + "an injective homomorphism of nonunital algebras.", DescribeRole.Definition),
            Node("product-family", "The product preserves the sixth-power witness", "product_family",
                "Over every field, the full product has 196 elements and is strictly "
                + "noncommutative: (zero,p)(zero,q)=(zero,r), whereas the reversed "
                + "product is zero. The contracted embedding sends the basis image "
                + "of s to the basis image of (s,zero). The three included generators "
                + "have pairwise distinct nonzero sixth powers. Every seven-fold "
                + "product of arbitrary semigroup elements is zero. The entire "
                + "subspace spanned by seven-fold products of arbitrary algebra "
                + "vectors is zero as well, and the sixth power of the first "
                + "included generator basis vector survives. Thus both exact "
                + "nilpotency indices are seven. For each primitive cube root omega "
                + "in the field, take the existing cyclic quotient's actual nonzero "
                + "sixth-power-zero witness u. Its image is a nonzero vector in the "
                + "span of the three included generator images and still has sixth "
                + "power zero. The source construction of u is x+omega*y+omega^2*z; "
                + "its coefficient at x is one. Multiplicativity preserves that "
                + "very witness, rather than introducing an unrelated algebra. "
                + "This includes every characteristic-zero field containing a "
                + "primitive cube root, with its original field hypothesis intact.", DescribeRole.Theorem),
            Node("right-zero", "The actual right-zero truncation", "RightZero",
                "For a natural n, the carrier has a separate zero and a pair (i,a) "
                + "for every degree 1 through n and every label a in {e,f}. The Lean "
                + "index in Fin n is one less than the written degree. Multiply "
                + "(i,a) by (j,b) to obtain (i+j,b) when i+j is at most n, and "
                + "zero otherwise. Both bracketings of a triple keep the rightmost "
                + "label and total degree when that degree is at most n; otherwise "
                + "both are zero. This is a literal carrier with associative "
                + "multiplication and a two-sided absorbing zero.", DescribeRole.Definition),
            Node("generators", "The two degree-one generators", "generator",
                "Choose x=(1,e) and y=(1,f). These are distinct nonzero elements. "
                + "For each k below n their (k+1)st powers are (k+1,e) and (k+1,f). "
                + "In particular their nth powers are distinct and nonzero. "
                + "When n is at least two, xy=(2,f) differs from yx=(2,e).", DescribeRole.Definition),
            Node("difference", "The contracted square-zero vector", "difference",
                "In the original contracted algebra take the basis image of x "
                + "minus that of y. This is nonzero because its coefficient at x "
                + "is one. Its square is (2,e)-(2,f)-(2,e)+(2,f)=zero. "
                + "The semigroup zero maps to the zero vector and is never "
                + "included as an extra basis vector.", DescribeRole.Definition),
            Node("right-zero-family", "The full quantified right-zero family", "right_zero_family",
                "For every n at least two, the actual carrier has exactly 2n+1 "
                + "elements and is strictly noncommutative. Its two generators "
                + "have distinct nonzero nth powers. Over every field, their "
                + "contracted difference is a nonzero member of their span, has "
                + "square zero and hence nth power zero. Every product of n+1 "
                + "arbitrary semigroup elements vanishes. The whole subspace "
                + "spanned by n+1-fold products of arbitrary contracted algebra "
                + "vectors vanishes, so every such vector product vanishes. "
                + "The nth power of the first generator's basis image is nonzero, "
                + "which makes both exact nilpotency indices n+1. No cube-root "
                + "hypothesis is required here; in particular the claim holds "
                + "over every characteristic-zero field. The application n=6 "
                + "has 13 elements and exact common index seven. These numerical "
                + "applications require no additional retained theorem wrappers.", DescribeRole.Theorem),
            Paragraph(Text("The arbitrary-vector bounds follow from the actual "
                + "object correspondence: the span of basis images of all "
                + "(k+1)-fold semigroup products equals the (k+1)-fold contracted "
                + "product subspace. Bilinearity and a split of each actual "
                + "positive word prove this equality by induction. Semigroup "
                + "nilpotence therefore controls all algebra products, rather "
                + "than only the power of the displayed witness.")),
            Paragraph(Text("The square-zero identity for differences of "
                + "idempotents in a common Green L- or R-class is prior work of "
                + "Almeida, Margolis, Steinberg and Volkov (2007), Proposition 3.4 "
                + "proof, page 11. The right-zero truncation is the source "
                + "manuscript's separate semigroup consequence, using degree "
                + "truncation as in Bergman's Example 12. The 196-element direct "
                + "product is a different source construction and retains its "
                + "cube-root witness hypothesis. These are the Question-15 "
                + "branch of Question 19 only; the independent quadratic field "
                + "countermodel is not this family.")),
            Paragraph(Text("The original formal59 Question-15 settlement and "
                + "the distinct cyclic59 and quotient49 carriers remain separate. "
                + "All positive-six-divisible-n cyclic results and arbitrary-n "
                + "terminal-partition results retain their original domains. "
                + "The n35 set {0,...,13,20,21} is one of four derived unfoldings "
                + "of von zur Gathen and Roche's first n35 Table 2 row, not a "
                + "printed I-set; their Theorem 4.4 proofs are omitted. Benjamin "
                + "and Scott's binomial identities remain prior. No novelty, "
                + "priority, minimality, additional paper or solved-credit claim "
                + "is made. Universal Question 11, Questions 16-18 and the "
                + "characteristic-p Eggert conjecture are outside this result. "
                + "Wenlin Zhang is affiliated with National University of Singapore "
                + "and ChronoAI Pte Ltd, Singapore; Haobo Ma with ChronoAI Pte Ltd, "
                + "Singapore only.")))));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Divisors;

internal sealed class NumberFieldDivisorSubpowerDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Divisors/NumberFieldDivisorSubpower.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform divisor counts in number fields of degree at most three",
        H("Uniform number-field divisor subpower bounds"),
        Blocks(
            Paragraph(Text("These estimates choose their positive constant before the number field. The constant depends only on the requested positive exponent and works for every number field K of degree at most three. There is no fixed-field, discriminant, class-number or regulator parameter. The statements count finite sets of actual ideals or actual algebraic integers, rather than a class of formal labels. The proof combines classical ideal factorization, bounded-coefficient minimal-polynomial finiteness and elementary real-power estimates; no claim of literature novelty is made.")),
            Node("ideal_divisors_subpower", "Uniform ideal-divisor count",
                "For every real delta greater than zero, one positive real C works simultaneously for all number fields K of degree at most three, all nonzero integral ideals I of the ring of integers, and all finite sets s of integral ideals dividing I: the cardinality of s is at most C times the absolute ideal norm of I to the power delta.",
                "Unique factorization injects ideal divisors into the box of prime-ideal exponents, whose cardinality is the product of a+1. Choose a norm cutoff T depending only on delta. For a large-norm prime ideal P, a+1 is at most Norm(P)^(delta*a). A small-norm factor needs a fixed extra constant, but the number of possible small-norm ideals is bounded uniformly in K: an ideal of positive norm at most T contains T!, and is determined by its image in the finite quotient modulo T!. That quotient has (T!)^[K:Q] elements, so its subsets number at most 2^((T!)^3). Multiplying the factor estimates and using multiplicativity of ideal norm proves the result without a field-dependent count of small prime ideals."),
            Node("bounded_divisors_subpower", "Actual bounded-conjugate algebraic divisors",
                "For every real epsilon greater than zero, there is a positive real C such that the following holds for every number field K of degree at most three and every real p at least two. Let D be a nonzero algebraic integer with the natural absolute value of its integral norm at most p^108. If s is a finite set of algebraic integers dividing D, and every complex embedding of every member of s has norm at most p^18, then the cardinality of s is at most C*p^epsilon. Primality of p is not assumed.",
                "A nonzero integral norm has absolute value at least one. With at most three embeddings, the logarithm of each conjugate of an allowed divisor lies between -36*log(p) and 18*log(p). Partition actual divisors by their principal ideal and by the natural floors of these logarithms shifted by 36*log(p). There are at most (floor(54*log(p))+1)^3 logarithmic boxes. In any nonempty fiber, choose an actual reference divisor. Equal principal ideals make every ratio an algebraic-integer unit, and equal logarithmic boxes bound every conjugate of the ratio by exp(1). Before choosing K, take the finite set in the complex numbers of roots of all degree-at-most-three integer polynomials with the resulting uniform coefficient bound. A fixed embedding injects each fiber into this one finite set. The ideal estimate with exponent epsilon/216 and the cubic logarithmic factor with exponent epsilon/6 together give the stated epsilon bound."),
            Node("fixed_product_pairs_subpower", "Actual pairs with a fixed nonzero product",
                "The same choice of an epsilon-dependent positive C bounds a finite set of ordered pairs of algebraic integers by C*p^epsilon, uniformly over K of degree at most three and real p at least two, provided all pair products equal the same nonzero D, its absolute integral norm is at most p^108, and every complex embedding of every first component has norm at most p^18. The second component needs no separate size hypothesis.",
                "The nonzero product makes the first projection injective: the first component determines the second by cancellation. Each first component divides D, so the preceding bounded-divisor estimate applies to the finite set of actual first values."),
            Paragraph(Text("Application boundary: these theorems supply the uniform number-field value-counting step proposed for the Pascadi singular-partner argument. This module does not construct the algebraic integers from the original lattice points, prove their integrality and nonzero fixed product from the original polynomial identities, establish the p^18 and p^108 bounds for those constructed values, or control the fibers from actual points to algebraic values. Those connections remain separate obligations. In particular, the generic pair-counting theorem alone is not a proof of the original Pascadi conjectural endpoint.")))));

    private static DocumentBlock Node(string name, string title, string statement, string proof) =>
        Describe.Lean(
            DescribeId.Create("number-field-divisor-subpower-" + name.Replace("_", "-")),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(statement)), Paragraph(Text(proof))),
            DescribeRole.Theorem);
}

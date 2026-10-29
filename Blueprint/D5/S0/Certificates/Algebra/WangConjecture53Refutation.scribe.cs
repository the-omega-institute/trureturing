using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates.Algebra;

internal sealed class WangConjecture53RefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/Algebra/WangConjecture53Refutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/wang2025semigrouprings");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Wang's Conjecture 5.3 fails for a six-element finite commutative monoid over Q: "
            + "the ordinary algebraic constant is one and the proposed right side is at least two.",
        H("Wang Conjecture 5.3: an Ordinary Semigroup Algebra Counterexample"),
        Blocks(
            Node("positive-multiples", "Positive multiples without adjoining zero", "positiveMultiple",
                "Index n denotes the positive multiple (n+1)a. The universal assertion requires "
                    + "only a finite commutative semigroup, with no identity assumption."),
            Node("positive-cyclic", "The positive cyclic subsemigroup", "cyclic",
                "The carrier consists of positive multiples only. It excludes an artificial "
                    + "zeroth multiple in a nonunital semigroup."),
            Node("idempotent-specification", "Cyclic idempotent specification", "IsCyclicIdempotent",
                "The element belongs to the positive cyclic subsemigroup and satisfies e+e=e."),
            Node("cyclic-idempotent", "The actual cyclic idempotent", "cyclicIdempotent",
                "A finite positive cyclic subsemigroup has a unique idempotent. Existence reuses "
                    + "Mathlib's compact-semigroup theorem with the discrete topology; uniqueness "
                    + "uses common positive multiples. The selector's fallback is unreachable "
                    + "for every element of a finite commutative semigroup."),
            Node("cyclic-group", "A cyclic group with its own identity", "CyclicIsGroup",
                "An identity and inverses must lie inside the positive cyclic subsemigroup. "
                    + "This property, rather than idempotence alone, controls epsilon."),
            Node("cyclic-period", "The cyclic period", "period",
                "Take the least positive eventual shift of positive multiples. This is the "
                    + "source period, not the index where periodicity begins."),
            Node("semigroup-exponent", "LCM of the periods", "semigroupExponent",
                "The exponent is the least common multiple of all cyclic periods. The six-label "
                    + "witness has period one at each element and exponent one."),
            Node("splitting-field", "The source splitting condition", "Splitting",
                "The root set zeta^exp(S)=1 has cardinality exp(S). Extended cardinality retains "
                    + "the distinction between a finite root count and an infinite set."),
            Node("field-admission", "Both admissibility branches", "Admissible",
                "Either the splitting condition holds, or K has prime characteristic p and the "
                    + "exponent is a power of p. Branch (i) requires neither algebraic closure "
                    + "nor characteristic zero. Q is used only for the counterexample."),
            Node("ordinary-factor", "A factor in the ordinary semigroup algebra", "factor",
                "Reuse AddMonoidAlgebra K S: coefficients are finitely supported on all of S, "
                    + "and multiplication is the upstream convolution. The factor is the basis "
                    + "vector at s minus a times the basis vector at its cyclic idempotent. "
                    + "Even an absorbing semigroup label remains an independent basis vector."),
            Node("positive-product", "Positive products in a possibly nonunital algebra", "factorProduct",
                "Multiply the ordered factors associatively for every positive length. The "
                    + "empty branch is zero and supplies no positive admissible length; no unit "
                    + "is asserted for an arbitrary nonunital semigroup algebra."),
            Node("all-coefficients", "Every tuple of individually nonzero coefficients", "GoodSequence",
                "Quantify over a separate coefficient at each position, requiring it to be "
                    + "nonzero at every position of the finite sequence. Coefficients outside "
                    + "that prefix do not enter the product. Repeated semigroup labels still "
                    + "have independently chosen coefficients."),
            Node("algebraic-constant", "The algebraic Davenport constant", "algebraicD",
                "Take the ENat supremum of all admissible finite lengths. Infinity means "
                    + "unboundedness of finite lengths, without defining an infinite product. "
                    + "Length zero contributes only the bottom of this supremum. In particular, "
                    + "an empty semigroup has constant zero as stipulated by the paper."),
            Node("principal-ideals", "Actual principal ideals", "Below",
                "Membership means x=a or x=a+c for a genuine semigroup element c. Including "
                    + "a itself does not require an adjoined identity."),
            Node("green-equivalence", "Green H-equivalence", "Green",
                "Two elements are equivalent exactly when their principal ideals are equal."),
            Node("green-congruence", "The Green congruence", "greenCon",
                "Equality of principal ideals is an additive congruence in a commutative "
                    + "semigroup; the proof establishes compatibility with addition."),
            Node("green-quotient", "The canonical quotient S/H", "GreenQuotient",
                "Use the upstream AddCon quotient and its canonical quotient map. For this "
                    + "witness, an exact finite check of principal ideals proves that the "
                    + "canonical quotient map is injective."),
            Node("sequence-sums", "Sequence sums and existing identities", "SequenceSum",
                "A nonempty list sums by the semigroup operation. The empty list sums to a "
                    + "only when a is already a two-sided identity in that semigroup."),
            Node("relative-irreducibility", "Irreducibility at a specified sum", "IrreducibleAt",
                "The sequence sums to a and no proper sublist has the same sum. Empty sublists "
                    + "are included. In a commutative semigroup, lists enumerate the unordered "
                    + "sequences and their submultisets without changing sums."),
            Node("relative-davenport", "The relative Davenport constant", "relativeD",
                "Take the ENat supremum of irreducible lengths at the given sum, retaining "
                    + "the source's relative constant rather than a global reducibility threshold."),
            Node("green-class", "The actual H-class", "HClass",
                "The class is a subtype of S consisting of elements with the same principal ideal."),
            Node("translations", "Actual stabilizer translations", "Gamma",
                "The carrier consists of maps H_a to itself realized by c+x for a genuine "
                    + "c in S. Equal maps are identified. Addition is composition, corresponding "
                    + "to addition of realizing elements. No identity is adjoined; the carrier "
                    + "is allowed to be empty."),
            Node("epsilon", "The source epsilon", "epsilon",
                "Epsilon is zero exactly for a positive cyclic group, and one otherwise."),
            Node("right-side", "The complete proposed right side", "rightSide",
                "Take the supremum over a in S of epsilon(a) times the relative Davenport "
                    + "constant at the canonical quotient image, plus the algebraic constant "
                    + "of the actual translation semigroup. For finite S this is the finite "
                    + "maximum appearing in the conjecture."),
            Node("published-claim", "The complete universal assertion", "claim",
                "Quantify over all finite commutative semigroups and fields satisfying either "
                    + "source branch. Assert equality of the two source constants. The finite "
                    + "monoid counterexample is substituted into this full semigroup assertion; "
                    + "the claim imposes no global monoid or sequence-length restriction."),
            Node("six-labels", "The six semigroup labels", "Model",
                "The carrier is {0,1} times {0,1,2}. All six labels remain in the ordinary algebra."),
            Node("witness-addition", "Union and truncated addition", "modelAdd",
                "Add by maximum in the first coordinate and min(2,n+m) in the second. The "
                    + "finite commutative monoid laws are checked by Lean's kernel."),
            Node("witness-idempotent", "Cyclic idempotents of the witness", "modelE",
                "Level zero remains zero; levels one and two have cyclic idempotent level two, "
                    + "with the first coordinate retained."),
            Node("transient-term", "The transient term", "transient",
                "The label (0,1) gives an always-nonzero singleton factor, detected by its "
                    + "coefficient one at this independent basis label."),
            Node("marker-term", "The marker term", "marker",
                "The label (1,0), together with the transient term, forms an irreducible "
                    + "two-term sequence at the target in the canonical quotient."),
            Node("target-term", "The target quotient class", "target",
                "The target is (1,1). Its positive cyclic semigroup is not a group, so its "
                    + "epsilon equals one."),
            Describe.Lean(DescribeId.Create("conjecture-five-three-refuted"),
                DeclarationHandle.Create(Prefix + "result"), H("Conjecture 5.3 has a negative answer"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Over Q, every nonzero coefficient assignment leaves the singleton at (0,1) "
                    + "nonzero. The all-ones assignment kills every sequence of length at least "
                    + "two: an idempotent yields a zero factor, while two transient factors have "
                    + "four equal basis products and cancel. Thus d(S,Q)=1. Principal ideals "
                    + "distinguish all six labels. At (1,1), the quotient sequence [(0,1),(1,0)] "
                    + "is irreducible and epsilon is one, so the proposed right side is at least "
                    + "two. Q meets splitting branch (i), since exp(S)=1. This single admissible "
                    + "instance refutes the full universal equality. The exact right-side maximum, "
                    + "minimality, independent novelty, and separate Conjecture 3.26 are not claimed."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("wang-conjecture53"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string id, string title, string declaration, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}

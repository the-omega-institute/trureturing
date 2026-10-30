using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Codes;

internal sealed class MajoranaFourteenModeDistanceFourDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Codes/MajoranaFourteenModeDistanceFour.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Hamming/hastings2017smallmajorana");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A self-orthogonal binary stabilizer space containing parity on at most fourteen modes has a logical operator of weight below four whenever twice its dimension is less than the number of modes.",
        H("The fourteen-mode obstruction for parity Majorana codes"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("majorana-fourteen-self-orthogonal"),
                DeclarationHandle.Create(Module + "IsSelfOrthogonal"),
                H("Self-orthogonal binary stabilizer spaces"),
                StatementSource.FromAuthor(Disp(SelfOrthogonalFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a finite coordinate type ι, c is a binary linear subspace. "
                    + "It is self-orthogonal when the dot product of every x and y in c is zero in ZMod 2, including x equal to y. "
                    + "The dot product is the sum of the coordinate products. Thus every vector of c has even Hamming weight, "
                    + "and every two supports overlap in an even number of coordinates. "
                    + "These are the evenness and commutation conditions for Majorana stabilizers in Hastings, c.tex, lines 86–97."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("majorana-fourteen-claim"),
                DeclarationHandle.Create(Module + "claim"),
                H("A logical operator of weight below four"),
                StatementSource.FromAuthor(Disp(Equivalence(Local("claim"), ClaimBody()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every natural n at most fourteen, take any self-orthogonal binary subspace c on Fin n containing the constant-one vector. "
                    + "If twice its dimension is strictly less than n, there is a vector v in its character orthogonal complement, outside c, with Hamming weight below four. "
                    + "The character orthogonal complement here is precisely the dot-product orthogonal complement over ZMod 2. "
                    + "Hastings identifies the dimension of c with the number of independent stabilizers and gives the logical-qubit count as n/2 minus that dimension "
                    + "in c.tex, lines 91 and 99–105. Logical operators and distance are defined in lines 108–113; "
                    + "the requirement that the constant-one parity vector belong to c is in lines 115–117. "
                    + "This statement expresses the exclusion suggested for fourteen modes in lines 271–273, together with all smaller lengths. "
                    + "It asserts the obstruction below sixteen modes; it does not assert existence at sixteen modes."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("majorana-fourteen-result"),
                DeclarationHandle.Create(Module + "result"),
                H("Proof of the obstruction"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Work first with an arbitrary finite coordinate type ι. Membership in the character orthogonal complement is equivalent to having zero dot product with every vector of c; "
                        + "symmetry of the dot product permits either order. Applying self-orthogonality to the constant-one vector twice shows that the number of coordinates is even. "
                        + "For distinct i and j, the vector eᵢ + eⱼ, where eᵢ = Pi.single i 1, has Hamming weight two. "
                        + "If this vector belongs to c, orthogonality against it forces x i = x j for every x in c.")),
                    Paragraph(Text(
                        "Suppose such a pair belongs to c. Let ev be evaluation at i on c, and let res restrict the kernel of ev to the coordinates other than i and j. "
                        + "Vectors in this kernel vanish at both removed coordinates, so res is injective. Its range d is self-orthogonal. "
                        + "The sum of the constant-one vector and eᵢ + eⱼ lies in the kernel and restricts to the constant-one vector of d. "
                        + "Evaluation is surjective because the constant-one vector evaluates to one, so rank-nullity gives dim d + 1 = dim c. "
                        + "The coordinate count decreases by two. A vector v orthogonal to d but outside d extends by zero at i and j to a vector w of the same Hamming weight. "
                        + "For x in c, adding x i times eᵢ + eⱼ puts x in the evaluation kernel without changing its other coordinates; hence w is orthogonal to x. "
                        + "If w belonged to c it would lie in that kernel and restrict into d, contradicting v outside d. "
                        + "This is the linear-space form of the pair-removal construction in Hastings, c.tex, lines 131–139.")),
                    Paragraph(Text(
                        "Next suppose that no vector eᵢ + eⱼ with i distinct from j lies in the orthogonal complement. "
                        + "The dimension inequality ensures that ι is nonempty. Choose i₀, evaluate c at i₀, and take a basis b of this evaluation kernel. "
                        + "Write k for its dimension and r a for the underlying vector of b a, with a in Fin k; then k + 1 = dim c. "
                        + "Associate to coordinate i the column whose a-th entry is (r a).val i. "
                        + "If the columns of i and j agree, their evaluations agree on the entire kernel because they agree on b. "
                        + "Every x in c can be moved into the kernel by adding x i₀ times the constant-one vector. "
                        + "Thus x i = x j for all x in c, putting eᵢ + eⱼ in the orthogonal complement. The assumption therefore makes the column map injective.")),
                    Paragraph(Text(
                        "Let s be the image of this column map in the binary k-dimensional cube. Its cardinality is the number of coordinates. "
                        + "For any subset a of Fin k with cardinality at most two, the sum over s of the monomial consisting of the product of x i for i in a is zero in ZMod 2. "
                        + "Indeed, injectivity transfers that sum to a sum over coordinates. "
                        + "For empty a this is orthogonality of the parity vector with itself; for a singleton it is orthogonality of r b with parity; "
                        + "for a two-element set it is orthogonality of the two corresponding vectors r b and r d.")),
                    Paragraph(Text(
                        "To use these moment equations, let f be any binary-valued function on the binary k-dimensional cube. "
                        + "For each subset a of Fin k, define q a to be the sum over y of f y times the product of y i over coordinates outside a. "
                        + "Then f x is the sum over all a of q a times the product of x i + 1 over i in a. "
                        + "To prove this expansion, the product over all coordinates of x i + 1 + y i equals one when y = x and zero otherwise. "
                        + "Multiplying by f y, summing over y, expanding the product, and exchanging the finite sums gives the asserted coefficients. "
                        + "If k is at least three and all moments of degrees at most two vanish, q a vanishes whenever the cardinality of a exceeds k − 3: "
                        + "its complementary product then has degree at most two.")),
                    Paragraph(Text(
                        "If all coefficients of degree greater than one vanish, this expansion makes f affine. "
                        + "Expanding its constant and singleton terms gives f(x + u) + f x = f u + f 0. "
                        + "A constant f has Hamming weight zero or 2ᵏ. Otherwise choose u with f u different from f 0. "
                        + "The displayed identity gives f(x + u) = f x + 1. Translation by u is a bijection exchanging the zero and nonzero values, "
                        + "so twice the Hamming weight of f is 2ᵏ.")),
                    Paragraph(Text(
                        "If instead all coefficients of degree greater than two vanish, expand the constant, singleton and pair terms to obtain additivity in x of "
                        + "b u x = f(x + u) + f x + f u + f 0. "
                        + "Use the integer-valued additive character χ on ZMod 2 with χ(0) = 1 and χ(1) = −1. "
                        + "For each u the character sum of χ(b u x) over x is zero or 2ᵏ, according as this character is nontrivial or trivial. "
                        + "Squaring the sum of χ(f x) and changing variables from the pair (x,y) to (x,x + u) expresses the square as the sum over u of "
                        + "χ(f u + f 0) times the sum over x of χ(b u x). Consequently 2ᵏ divides this integer square.")),
                    Paragraph(Text(
                        "At k = 5, write w for the integer sum with summand one when f x = 0 and minus one otherwise. "
                        + "The preceding divisibility is 32 dividing w squared. Passing to the natural absolute value and using prime factorization yields 8 dividing w. "
                        + "Counting the nonzero values gives w = 32 − 2 times the integer cast of the Hamming weight of f. "
                        + "It follows that 4 divides that integer cast, and hence that 4 divides the natural Hamming weight.")),
                    Paragraph(Text(
                        "Apply these facts to f equal to one on s and zero elsewhere; its Hamming weight is the cardinality of s. "
                        + "The inequalities k ≤ 5, 2(k + 1) < |s| ≤ 14 and |s| ≤ 2ᵏ exclude k at most three, leaving k = 4 or k = 5. "
                        + "The moment expansion has degree at most k − 3. At k = 4 the affine weight alternatives are 0, 8 and 16, "
                        + "all incompatible with 10 < |s| ≤ 14. At k = 5, evenness and 12 < |s| ≤ 14 force |s| = 14, "
                        + "contradicting divisibility by four.")),
                    Paragraph(Text(
                        "If c contains no weight-two vector but every vector of the orthogonal complement outside c has weight at least four, "
                        + "the orthogonal complement contains no eᵢ + eⱼ with distinct i and j. "
                        + "The injective column construction then gives s with all the preceding properties: k + 1 = dim c and |s| = |ι| "
                        + "supply the dimension and size bounds, while self-orthogonality and parity supply the moments and evenness. "
                        + "The contradiction proves the desired short vector whenever c contains no weight-two vector.")),
                    Paragraph(Text(
                        "Finally use strong induction on the number of coordinates. If c contains eᵢ + eⱼ for distinct i and j, "
                        + "the space d obtained by removing that pair has two fewer coordinates, one less dimension, and the same strict inequality "
                        + "between twice its dimension and its coordinate count. It remains self-orthogonal and contains parity, so induction gives a short vector "
                        + "orthogonal to d but outside d. Extension by zero gives the required vector for c. If there is no such pair in c, the preceding contradiction applies. "
                        + "Specializing the coordinate type to Fin n, whose cardinality is n, proves the stated assertion for every n at most fourteen."))),
                DescribeRole.Theorem)
        )));

    private static Formula SelfOrthogonalFormula() =>
        All(Iota, Seq(Qualified("Type"), Star),
            Seq(OpenBracket, At(Qualified("Fintype"), Iota), CloseBracket, Comma, Sp,
                All(X("c"), Code(Iota), Equivalence(LocalCall("IsSelfOrthogonal", X("c")),
                    All(X("x"), Vectors(Iota), Imp(Member(X("x"), X("c")),
                        All(X("y"), Vectors(Iota), Imp(Member(X("y"), X("c")),
                            Equal(At(Qualified("dotProduct"), X("x"), X("y")),
                                Typed(D(0), Binary()))))))))));

    private static Formula ClaimBody()
    {
        var coordinates = At(Qualified("Fin"), X("n"));
        var parity = At(Qualified("Function", "const"), coordinates, Typed(D(1), Binary()));
        var dimension = At(Qualified("Module", "finrank"), Binary(),
            Typed(X("c"), Qualified("Type")));
        var complement = At(Qualified("D5", "S3", "Fourier", "CharacterSelection",
            "BinaryCharacterCodeDuality", "characterOrthogonalComplement"), Binary(), X("c"));
        var conclusion = Some(X("v"), Vectors(coordinates), And(Member(X("v"), complement),
            And(new Formula.Not(Parenthesized(Member(X("v"), X("c")))),
                Less(At(Qualified("hammingNorm"), X("v")), Typed(D(4), Naturals())))));
        return All(X("n"), Naturals(), Imp(LessOrEqual(X("n"), Typed(D(1, 4), Naturals())),
            All(X("c"), Code(coordinates), Imp(LocalCall("IsSelfOrthogonal", X("c")),
                Imp(Member(parity, X("c")),
                    Imp(Less(Multiply(Typed(D(2), Naturals()), dimension), X("n")), conclusion))))));
    }

    private static Formula X(string name) => F.Id(name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(X(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Local(string name) =>
        Qualified("D5", "S3", "Quantum", "Codes", "MajoranaFourteenModeDistanceFour", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => new Formula.LatexSequence([Open, value, Close]);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula Binary() => At(Qualified("ZMod"), Typed(D(2), Naturals()));
    private static Formula Vectors(Formula coordinates) => new Formula.TypeArrow(coordinates, Binary());
    private static Formula Code(Formula coordinates) => At(Qualified("Submodule"), Binary(), Vectors(coordinates));
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula Some(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LessOrEqual(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula value, Formula set) => new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}

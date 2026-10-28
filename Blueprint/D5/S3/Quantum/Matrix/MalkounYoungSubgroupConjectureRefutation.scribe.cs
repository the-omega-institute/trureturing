using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class MalkounYoungSubgroupConjectureRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/MalkounYoungSubgroupConjectureRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/malkoun2025finitegraphs");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fifteen copies of a three-column Gram matrix violate the proposed lower bound for two class-preserving permutation groups.",
        H("A counterexample to the Young-subgroup cross-sum inequality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("class-preserving"),
                DeclarationHandle.Create(Prefix + "classPreserving"),
                H("Permutations preserving every equivalence class"),
                StatementSource.FromAuthor(Disp(ClassPreservingFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For an equivalence relation r on Fin n, classPreserving r is the subgroup of permutations "
                        + "that send each index to an equivalent index. Its displayed carrier determines the subgroup: "
                        + "reflexivity gives the identity, transitivity gives closure under composition, and symmetry "
                        + "gives closure under inversion. This is the group defined in the source's TeX line 405. "
                        + "The index i in Fin n corresponds to the source's label i+1."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The conjectured lower bound in every dimension"),
                StatementSource.FromAuthor(Disp(Equal(
                    Typed(Qualified("claim"), Qualified("Prop")), Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every natural n, every pair of equivalence relations r₁,r₂ on Fin n, and every complex "
                        + "Hermitian positive semidefinite matrix h, the proposed lower bound is the cardinality "
                        + "of the intersection of their class-preserving groups times the product of the real diagonal entries. "
                        + "Here SemilatticeInf.inf is subgroup intersection, Subtype of its carrier is the type of its elements, and Nat.card "
                        + "is its natural-valued cardinality; the displayed Nat.cast includes this cardinality in the reals. "
                        + "The function crossSum is the sum over both full subgroups of the products of h(σ(i),τ(i)), "
                        + "as in TeX lines 407–408. Conjecture D is the inequality at lines 410–412. "
                        + "Hermitian diagonal entries are real: diagonal_product_eq_real identifies their complex product "
                        + "with Complex.ofReal of the product of their real parts. Thus this real inequality expresses "
                        + "the source's diagonal-product inequality without any additional restriction on n or on the relations."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Fifteen Gram blocks contradict the bound"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Qualified("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Use coordinates (j,s) in Fin m × Fin 3, identified with Fin (m·3) by (j,s) ↦ 3j+s. "
                            + "On each three-point block, the first relation has classes {0,1} and {2}, and the second "
                            + "has classes {0} and {1,2}; indices in different blocks are never equivalent. "
                            + "Let V have columns (1,0), (1,1), (1,Complex.I). Its Gram matrix A = VᴴV has rows "
                            + "(1,1,1), (1,2,1+Complex.I), and (1,1−Complex.I,2). "
                            + "Let H be the direct sum of m copies of A, reindexed by the stated coordinates. "
                            + "Each Gram block is positive semidefinite; block-diagonal assembly and reindexing preserve "
                            + "this property. In particular H is Hermitian.")),
                    Paragraph(Text(
                        "A family of class-preserving permutations of Fin 3, one for each j, acts on (j,s) by "
                            + "fixing j and applying its jth permutation to s. Conversely, a permutation preserving "
                            + "either block relation fixes the first coordinate, and its restriction to each fiber "
                            + "is a bijection of Fin 3 preserving the corresponding seed relation. These two constructions "
                            + "identify the full class-preserving subgroup with the product of the seed subgroups. "
                            + "Reindexing the product of matrix entries by (j,s) separates it into a product over blocks. "
                            + "Reindexing both subgroup sums by these families, then distributing each finite sum over "
                            + "the product, gives crossSum(H) = crossSum(A)^m for the two corresponding pairs of groups.")),
                    Paragraph(Text(
                        "For the first seed relation the only permutations are the identity and the swap of 0 and 1; "
                            + "for the second they are the identity and the swap of 1 and 2. Enumerating each group by "
                            + "the two Boolean values reduces the seed cross-sum to four products. They are respectively "
                            + "4, 2, 2, and 1−Complex.I, so their sum is 9−Complex.I.")),
                    Paragraph(Text(
                        "If two seed indices are equivalent for both relations, they are equal. A permutation "
                            + "belonging to both block subgroups therefore fixes both coordinates of every index. "
                            + "Their intersection is the identity subgroup and has cardinality one. "
                            + "For the diagonal product, Hermitian symmetry first identifies the real product with its "
                            + "complex embedding. Reindexing the complex product by (j,s) gives the mth power of the "
                            + "seed diagonal product, and the seed diagonal is (1,2,2). Injectivity of Complex.ofReal "
                            + "therefore gives the real diagonal product 4^m.")),
                    Paragraph(Text(
                        "Exact complex multiplication gives (9−Complex.I)^15 = "
                            + "−20078071648128−224842906547072·Complex.I. Now suppose claim holds and apply it with "
                            + "n = 45, m = 15, the two block relations, and H. The established positivity supplies "
                            + "both matrix hypotheses. Substituting the intersection, diagonal product, block factorization, "
                            + "seed value, and fifteenth power into the asserted inequality gives "
                            + "1073741824 ≤ −20078071648128, a contradiction."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("malkoun-2025-young-subgroup-conjecture-d"),
                    ResolutionKind.Refuted)))));

    private static Formula ClassPreservingFormula()
    {
        Formula n = F.Id("n"), r = F.Id("r"), i = F.Id("i");
        Formula permutations = At(Qualified("Equiv", "Perm"), FinOf(n));
        Formula subgroup = At(Qualified("Subgroup"), permutations);
        Formula carrier = At(Qualified("SetLike", "coe"), Typed(ClassOf(r), subgroup));
        Formula condition = All(i, FinOf(n),
            At(Seq(r, Dot, F.Id("r")), At(Qualified("Equiv", "toFun"), SigmaLower, i), i));
        Formula elements = Seq(OpenBrace, Typed(SigmaLower, permutations), Sp, Mid, Sp, condition, CloseBrace);
        return All(n, Naturals(), All(r, At(Qualified("Setoid"), FinOf(n)), Equal(carrier, elements)));
    }

    private static Formula ClaimBody()
    {
        Formula n = F.Id("n"), h = F.Id("h"), i = F.Id("i");
        Formula r1 = new Formula.Subscript(F.Id("r"), D(1));
        Formula r2 = new Formula.Subscript(F.Id("r"), D(2));
        Formula intersection = At(Qualified("SemilatticeInf", "inf"), ClassOf(r1), ClassOf(r2));
        Formula cardinality = At(Qualified("Nat", "card"),
            At(Qualified("Subtype"), At(Qualified("SetLike", "coe"), intersection)));
        Formula realCardinality = Typed(At(Qualified("Nat", "cast"), cardinality), Reals());
        Formula diagonal = Seq(new Formula.Subscript(Prod, Seq(i, Colon, Sp, FinOf(n))), Sp,
            Parenthesized(At(Qualified("Complex", "re"), At(h, i, i))));
        Formula crossSum = At(Qualified("D5", "S3", "Quantum", "Matrix",
            "MalkounSubgroupLowerBoundRefutation", "crossSum"), ClassOf(r1), ClassOf(r2), h);
        Formula bound = new Formula.Relation(Multiply(realCardinality, diagonal),
            FormulaRelationOperator.LessThanOrEqual, At(Qualified("Complex", "re"), crossSum));
        Formula matrices = All(h, At(Qualified("Matrix"), FinOf(n), FinOf(n), Complexes()),
            Implies(At(Qualified("Matrix", "IsHermitian"), h),
                Implies(At(Qualified("Matrix", "PosSemidef"), h), bound)));
        Formula relations = At(Qualified("Setoid"), FinOf(n));
        return All(n, Naturals(), All(r1, relations, All(r2, relations, matrices)));
    }

    private static Formula ClassOf(Formula r) => At(Qualified("classPreserving"), r);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula Qualified(params string[] parts) => Seq(Operatorname, Grp(Seq(
        parts.Select((part, index) => index == 0 ? F.Id(part) : Seq(Dot, F.Id(part))).ToArray())));
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula Implies(Formula premise, Formula conclusion) =>
        new Formula.Logic(Parenthesized(premise), FormulaLogicOperator.Implies, Parenthesized(conclusion));
}

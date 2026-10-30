using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permutation;

internal sealed class StronglyComplementaryPermutationMaximumDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Permutation/StronglyComplementaryPermutationMaximum";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGroups/rajchelgasiorowskizyczkowski2018robust");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The maximum size of a strongly complementary permutation family is the largest power of two dividing its positive dimension.",
        H("The maximum number of strongly complementary permutation matrices"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("is-complementary"),
                DeclarationHandle.Create(Module + ".IsComplementary"),
                H("Complementarity of matrix entries"),
                StatementSource.FromAuthor(Disp(ComplementaryFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Complementarity is the four-index condition of Definition 4.1 "
                    + "in arXiv:1804.10715v2, unisto9.tex, lines 606–611. "
                    + "If p has ones at (i,j) and (h,k), and q has a one at (i,k), "
                    + "then q must have a one at (h,j). The predicate is defined for "
                    + "all natural-valued square matrices on an arbitrary index type α; "
                    + "being a permutation matrix is a separate condition."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("is-strongly-complementary"),
                DeclarationHandle.Create(Module + ".IsStronglyComplementary"),
                H("Complementarity with disjoint support"),
                StatementSource.FromAuthor(Disp(StronglyComplementaryFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Strong complementarity adds the requirement that every entry equal "
                    + "to one in p is zero in q. This is Definition 4.3 "
                    + "in unisto9.tex, lines 623–626; for permutation matrices it says "
                    + "that their supports are disjoint. As with complementarity, "
                    + "the predicate itself does not assume that its matrices are permutations."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("is-permutation-matrix"),
                DeclarationHandle.Create(Module + ".IsPermutationMatrix"),
                H("Matrices of permutations"),
                StatementSource.FromAuthor(Disp(PermutationMatrixFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A permutation matrix is the matrix of a bijection σ of its index type. "
                    + "The convention is σ.permMatrix ℕ i j = 1 exactly when σ i = j. "
                    + "This makes explicit the permutation matrices used in Definition 4.1 "
                    + "at unisto9.tex, lines 606–611. The definition allows an arbitrary "
                    + "index type with decidable equality, including an infinite one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("max-strongly-complementary"),
                DeclarationHandle.Create(Module + ".maxStronglyComplementary"),
                H("The supremum of the attained family sizes"),
                StatementSource.FromAuthor(Disp(MaximumFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For each natural n, take the supremum in ℕ of the cardinalities "
                    + "of finite sets of n by n permutation matrices whose distinct "
                    + "members are pairwise strongly complementary. SetLike.coe explicitly "
                    + "includes the finite set s into the set of matrices before Pairwise "
                    + "is applied. All matrix entries, cardinalities, and supremum values "
                    + "are natural numbers. This is the maximal number in unisto9.tex, "
                    + "lines 678–690, expressed as a supremum; the function also extends to n = 0."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("The maximum-cardinality identity in every positive dimension"),
                StatementSource.FromAuthor(Disp(Equal(Local("claim"), Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every natural n at least one, the maximum is 2 raised to "
                    + "padicValNat 2 n, the exponent of two in n. This answers the "
                    + "cardinality part of the question at unisto9.tex, lines 678–690. "
                    + "The question there about unistochasticity of the interior of the "
                    + "polytope is separate from this identity."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("The sharp bound and a family attaining it"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For a permutation σ, the (i,j) entry of its matrix is one "
                        + "exactly when σ i = j and is zero exactly when σ i ≠ j. "
                        + "The map taking σ to its matrix is injective. Complementarity "
                        + "of the matrices of σ and τ is equivalent to the relative "
                        + "permutation σ⁻¹τ being an involution: in the forward direction "
                        + "apply the four-index condition with i = x, j = σ x, "
                        + "h = σ⁻¹(τ x), and k = τ x; in the reverse direction the three "
                        + "entries equal to one give σ⁻¹(τ i) = h, and applying the "
                        + "involution at i gives τ h = σ i = j. Disjoint support is "
                        + "equivalent to the absence of fixed points of σ⁻¹τ. Thus "
                        + "strong complementarity means precisely a fixed-point-free involution.")),
                    Paragraph(Text(
                        "Replacing every σ by σρ⁻¹ conjugates each relative permutation "
                        + "by ρ, preserving this condition. A finite matrix family s lifts "
                        + "to the finite set of all permutations whose matrices belong to s; "
                        + "the matrix map takes that set onto s and preserves cardinality. "
                        + "For a nonempty permutation family choose a member ρ. The "
                        + "replacement σ ↦ σρ⁻¹ is injective, preserves cardinality and "
                        + "strong complementarity, and produces a family t containing the identity.")),
                    Paragraph(Text(
                        "Every member of t squares to the identity, by comparison with "
                        + "the identity. For distinct σ and τ in t, their relative product "
                        + "is also an involution. Since σ and τ are their own inverses, "
                        + "inverting that product gives στ = τσ. Hence the generators "
                        + "commute. Every element of the subgroup they generate squares "
                        + "to the identity: this property holds for the generators and "
                        + "the identity, is preserved under inverses, and is preserved "
                        + "under products of commuting elements.")),
                    Paragraph(Text(
                        "For any point x, evaluation σ ↦ σ x embeds a pairwise strongly "
                        + "complementary family into its generated subgroup's orbit of x. "
                        + "Indeed σ x = τ x for distinct members would make σ⁻¹τ fix x. "
                        + "For a 2-group acting on Fin n with n at least one, every orbit "
                        + "has size 2 raised to a natural exponent. Choose the smallest "
                        + "such exponent a. Its orbit size 2^a divides every other orbit "
                        + "size, so it divides their sum n.")),
                    Paragraph(Text(
                        "The subgroup generated by t is a 2-group because each element "
                        + "squares to the identity. Evaluating t in an orbit of least size "
                        + "therefore gives |t| ≤ 2^a, with 2^a dividing n. Thus a ≤ "
                        + "padicValNat 2 n and |t| ≤ 2^(padicValNat 2 n). Cardinality "
                        + "preservation gives the bound for the original permutation family; "
                        + "the empty family satisfies it as well. Lifting matrix families "
                        + "to permutations then gives the same upper bound for matrices.")),
                    Paragraph(Text(
                        "For the matching family, write n = 2^a m with "
                        + "a = padicValNat 2 n and m = n.divMaxPow 2. Here m is positive "
                        + "because n is positive, and m is odd because no further factor "
                        + "of two divides it. Choose a bijection e from Fin n to "
                        + "(Fin a → ZMod 2) × Fin m. For each vector v in Fin a → ZMod 2, "
                        + "transport the translation (w,z) ↦ (v+w,z) back along e to a "
                        + "permutation of Fin n.")),
                    Paragraph(Text(
                        "These permutations are distinct: evaluating at the point "
                        + "corresponding to (0,0) recovers v, using m > 0. The relative "
                        + "permutation for vectors u and v translates by v−u. It is an "
                        + "involution since every coordinate has characteristic two. A "
                        + "fixed point forces v−u = 0, hence u = v. Distinct vectors "
                        + "therefore give strongly complementary matrices. There are "
                        + "2^a vectors, and injectivity of the matrix map preserves that "
                        + "cardinality when passing to the matrix family.")),
                    Paragraph(Text(
                        "The set of attained cardinalities thus contains "
                        + "2^(padicValNat 2 n), and every attained cardinality is at most "
                        + "this number. Its supremum is at most this bound and at least "
                        + "the attained value, proving the identity for every n ≥ 1."))),
                DescribeRole.Theorem))));

    private static Formula ComplementaryFormula() => MatrixBinders(Equivalence(
        Call("IsComplementary", X("p"), X("q")),
        All("i", Alpha, All("j", Alpha, All("h", Alpha, All("k", Alpha,
            Implication(Equal(At(X("p"), X("i"), X("j")), D(1)),
                Implication(Equal(At(X("p"), X("h"), X("k")), D(1)),
                    Implication(Equal(At(X("q"), X("i"), X("k")), D(1)),
                        Equal(At(X("q"), X("h"), X("j")), D(1)))))))))));

    private static Formula StronglyComplementaryFormula() => MatrixBinders(Equivalence(
        Call("IsStronglyComplementary", X("p"), X("q")),
        Conjunction(Call("IsComplementary", X("p"), X("q")),
            All("i", Alpha, All("j", Alpha,
                Implication(Equal(At(X("p"), X("i"), X("j")), D(1)),
                    Equal(At(X("q"), X("i"), X("j")), D(0))))))));

    private static Formula PermutationMatrixFormula() => All("α", Qualified("Type"),
        InstanceBinder(At(Qualified("DecidableEq"), Alpha), All("p", Matrices(Alpha),
            Equivalence(Call("IsPermutationMatrix", X("p")),
                Some("σ", At(Qualified("Equiv", "Perm"), Alpha),
                    Equal(X("p"), At(Qualified("Equiv", "Perm", "permMatrix"), Naturals, X("σ"))))))));

    private static Formula MaximumFormula()
    {
        Formula matrices = Matrices(At(Qualified("Fin"), X("n")));
        Formula family = All("p", matrices, Implication(
            Member(X("p"), X("s")), Call("IsPermutationMatrix", X("p"))));
        Formula pairwise = At(Qualified("Set", "Pairwise"),
            Typed(At(Qualified("SetLike", "coe"), X("s")), At(Qualified("Set"), matrices)),
            Local("IsStronglyComplementary"));
        Formula attained = Seq(OpenBrace, Typed(X("k"), Naturals), Sp, Mid, Sp,
            Some("s", At(Qualified("Finset"), matrices),
                Conjunction(family, Conjunction(pairwise,
                    Equal(At(Qualified("Finset", "card"), X("s")), X("k"))))), CloseBrace);
        return All("n", Naturals, Equal(Call("maxStronglyComplementary", X("n")),
            At(Qualified("sSup"), attained)));
    }

    private static Formula ClaimBody() => All("n", Naturals,
        Implication(LE(D(1), X("n")), Equal(Call("maxStronglyComplementary", X("n")),
            new Formula.Power(D(2), At(Qualified("padicValNat"), D(2), X("n"))))));

    private static Formula MatrixBinders(Formula body) => All("α", Qualified("Type"),
        All("p", Matrices(Alpha), All("q", Matrices(Alpha), body)));
    private static Formula Matrices(Formula index) => At(Qualified("Matrix"), index, index, Naturals);
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula X(string name) => name switch
    {
        "α" => Alpha,
        "σ" => SigmaLower,
        _ => F.Id(name),
    };
    private static Formula Local(string name) => Qualified("StronglyComplementaryPermutationMaximum", name);
    private static Formula Call(string name, params Formula[] args) => At(Local(name), args);
    private static Formula Qualified(params string[] names) => Seq(Operatorname,
        Grp(Seq([.. names.SelectMany((name, index) => index == 0
            ? new Formula[] { F.Id(name) } : new Formula[] { Dot, F.Id(name) })])));
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula InstanceBinder(Formula instance, Formula body) =>
        Seq(OpenBracket, instance, CloseBracket, Comma, Sp, Parenthesized(body));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Conjunction(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implication(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
}

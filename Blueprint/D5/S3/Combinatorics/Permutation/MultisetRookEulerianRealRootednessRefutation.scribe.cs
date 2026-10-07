using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permutation;

internal sealed class MultisetRookEulerianRealRootednessRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Permutation/MultisetRookEulerianRealRootednessRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/alexanderssonjalquemener2025rook");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full multiset rook-Eulerian polynomial fails real-rootedness on a positive Ferrers board.",
        H("A counterexample to full multiset rook-Eulerian real-rootedness"),
        Blocks(
            Paragraph(Text("This module uses the original W, asc and R from MultisetRookEulerianInterlacingRefutation. Words retain their source order, asc counts strict adjacent ascents, and R sums X raised to that count over distinct fitting words. Real-rootedness is Polynomial.Splits over the real field, retaining root multiplicity. The result concerns the first clause of Conjecture 28 directly.")),
            RepoNode("counting-bridge", "The exact word sum satisfies the recurrence", "W_sum_eq_dp",
                StatementSource.WithoutFormula(),
                "For every n and k, board l : Fin(n) → N and content a : Fin(k) → N whose sum is n, R(l,a) equals dp(ofFn(l),sourceLetters(a),none). sourceLetters lists a(c) copies of c+1. The recurrence chooses an allowed first letter from the distinct available labels, removes one copy, and multiplies by X precisely when the preceding letter is strictly smaller. Its proof identifies the original W with fitting permutations, decomposes that finite set into disjoint first-letter branches, and proves equality of the complete polynomial sums by induction. There is no numerical approximation or omitted branch."),
            RepoNode("board", "The positive 120-row Ferrers board", "board",
                StatementSource.WithoutFormula(),
                "On zero-based i : Fin(120), board(i) is 2 for i < 3, 3 for 3 ≤ i < 7, 4 for 7 ≤ i < 17, 5 for 17 ≤ i < 19, and 6 otherwise. Thus the row list is (2^3,3^4,4^10,5^2,6^101). Every row is positive and the rows are weakly increasing." , DescribeRole.Definition),
            RepoNode("content", "The nonnegative integer content", "content",
                StatementSource.WithoutFormula(),
                "The six letter multiplicities are (6,1,4,8,1,100), summing to 120. The codomain N enforces nonnegative integer entries. The maximum row length and alphabet size both equal 6.", DescribeRole.Definition),
            RepoNode("polynomial", "The degree-nine factor", "Q",
                StatementSource.WithoutFormula(),
                "Q = 1 + 261X + 21704X² + 591814X³ + 5372605X⁴ + 18550680X⁵ + 27147806X⁶ + 17137014X⁷ + 4318325X⁸ + 352440X⁹. The full polynomial is X²Q, so the two zeros at the origin remain part of the source polynomial.", DescribeRole.Definition),
            RepoNode("exact-polynomial", "The full source polynomial equals X²Q", "R_eq_explicit",
                StatementSource.FromAuthor(F.Disp(Equal(Call("R", Id("board"), Id("content")),
                    Multiply(new Formula.Power(Id("X"), Num(2)), Id("Q"))))),
                "The generic recurrence bridge and the complete 1769-state certificate establish this equality for the original word sum. Every reachable residual state satisfies the defining recurrence through exact child equalities, list erasures and polynomial identities. The root contains all ten nonzero coefficients displayed in Q after multiplication by X²."),
            RepoNode("translation", "An exact translation exposes the Newton obstruction", "translate_eq",
                StatementSource.WithoutFormula(),
                "The exact rational polynomial P is Q composed with X−9/1000. Its first three coefficients p₀,p₁,p₂ are 147002524734936505239773/12500000000000000000000000, −23217846032368454006421/25000000000000000000000, and 12818006465516640352661/1562500000000000000. The equality checks all ten coefficients in Lean."),
            RepoNode("newton-obstruction", "The translated polynomial does not split over the reals", "translated_not_splits",
                StatementSource.FromAuthor(F.Disp(new Formula.Not(Call("Splits", Id("P"))))),
                "If the degree-nine polynomial P split over the reals, Vieta's formula and the existing RealRootedCoefficientNewton.esymm_mul_esymm_le_sq_esymm theorem would imply 4p₁² ≥ 9p₀p₂. Exact rational normalization proves the opposite strict comparison. Translation preserves splitting, so this obstruction proves that Q and X²Q fail real-rootedness."),
            Describe.Lean(DescribeId.Create("claim"), DeclarationHandle.Create(Prefix + "claim"),
                H("The first real-rootedness clause of Conjecture 28"),
                StatementSource.FromAuthor(F.Disp(Claim())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Conjecture 28, Section 3.3: ‘For Ferrers boards, the polynomial R(λ, α; t) is real-rooted.’ The section requires λᵢ > μᵢ; setting μ=0 makes every row strictly positive. It allows nonnegative integer multiplicities totaling n. The formula quantifies every positive n, every k, every monotone positive board and every content of total n. It states only this first clause, using the original R and Polynomial.Splits directly."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("The first real-rootedness clause is false"),
                StatementSource.FromAuthor(F.Disp(new Formula.Not(Id("claim")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Instantiate claim at n=120, k=6, board and content. Positivity, monotonicity and the content sum discharge every source hypothesis. The equality R(board,content)=X²Q and the exact non-splitting certificate then contradict its conclusion. This settles the first clause independently of the earlier six-row interlacing counterexample. No minimality claim for n=120 or classification of all failing boards is made. Rectangular-board and distinct-letter results cited in the source retain their hypotheses and are unaffected."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("alexandersson-jal-quemener-2025-rook-eulerian-real-rootedness"),
                    ResolutionKind.Refuted))
        ), []));

    private static DocumentBlock RepoNode(string id, string title, string name,
        StatementSource statement, string prose, DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner(name) + name), H(title),
            statement, AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static string Owner(string name) => name switch
    {
        "W_sum_eq_dp" => "D5/S3/Combinatorics/Permutation/MultisetRookEulerianWordRecurrence.",
        "Q" or "translate_eq" or "translated_not_splits" => "D5/S3/Combinatorics/Permutation/MultisetRookEulerianNonrealCertificate.",
        _ => Prefix
    };

    private static Formula N => F.Seq(F.Mathbb, F.Grp(F.Id("N")));
    private static Formula Fin(Formula size) => Call("Fin", size);
    private static Formula All(string variable, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), type, body);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula SumOver(string variable, Formula domain, Formula body) =>
        F.Seq(new Formula.Subscript(F.Sum, F.Seq(Id(variable), F.InMacro, domain)), body);

    private static Formula Claim()
    {
        var rowsPositive = All("i", Fin(Id("n")), Lt(Num(0), Call("l", Id("i"))));
        var sum = Equal(SumOver("c", Fin(Id("k")), Call("a", Id("c"))), Id("n"));
        var body = Imp(Lt(Num(0), Id("n")),
            Imp(Call("Monotone", Id("l")), Imp(rowsPositive,
                Imp(sum, Call("Splits", Call("R", Id("l"), Id("a")))))));
        return Equal(Id("claim"), All("n", N, All("k", N,
            All("l", new Formula.TypeArrow(Fin(Id("n")), N),
                All("a", new Formula.TypeArrow(Fin(Id("k")), N), body)))));
    }
}

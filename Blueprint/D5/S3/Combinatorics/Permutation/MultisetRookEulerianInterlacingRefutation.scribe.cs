using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permutation;

internal sealed class MultisetRookEulerianInterlacingRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Permutation/MultisetRookEulerianInterlacingRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/alexanderssonjalquemener2025rook");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Multiset rook-Eulerian interlacing fails on a six-row Ferrers board.",
        H("A counterexample to multiset rook-Eulerian interlacing"),
        Blocks(
            Paragraph(Text("A board is a weakly increasing function l on zero-based positions Fin(n). Content a on Fin(k) specifies the multiplicity of the positive letter c+1. Lists encode the source words in their original order. When the content sum is n, their length is n. Polynomial.Splits over the real field is used directly for real-rootedness; by Mathlib's splits_iff_card_roots it is equivalent to roots.card = natDegree, with multiplicity.")),
            Node("words", "Words with fixed content fitting a Ferrers board", "W", Words(),
                "Section 3.3, page 11: ‘Let α = (α₁, . . . , αₖ) be non-negative integers with total sum n, and let λ and μ be integer partitions such that λᵢ > μᵢ for all i. We let W(λ/μ, α) be all words with αᵢ entries equal to i, such that μᵢ < wᵢ ≤ λᵢ for all i = 1, 2, . . . , n.’ Here μ is zero. The defining expression constructs the list containing a(c) copies of c+1, enumerates its permutations by the existing List.permutations' operation, removes duplicate lists, and retains precisely the row inequalities. List.mem_permutations' identifies membership with permutation of that content list. No word order is identified: only repeated enumeration of the same word is removed. getD(w,i,0) is list lookup with default zero; every queried position exists when the content sum is n.", DescribeRole.Definition),
            Node("ascents", "Strict adjacent ascents", "asc", Ascents(),
                "Section 2, page 4: ‘if w₁w₂ . . . wℓ is a word, then i is an ascent of the word if wᵢ < wᵢ₊₁.’ The zero-based index set is range(length(w) minus one). Subtraction in this natural-valued expression is truncated, including at the empty word.", DescribeRole.Definition),
            Node("full", "The full polynomial", "R", Full(),
                "Section 3.3, page 11, equation (10): R(λ/μ, α; t) := Σ_{w ∈ W(λ/μ, α)} t^{asc(w)}. X is the real polynomial indeterminate; summation is over distinct words.", DescribeRole.Definition),
            Node("refined", "The first-letter refined polynomial", "Rj", Refined(),
                "Section 3.3, page 11, equation (11): Rⱼ(λ/μ, α; t) := Σ_{w ∈ W(λ/μ, α), w₁=j} t^{asc(w)}. The first letter is getD(w,0,0), without an ascent shift. Examples 25–26 use λ = 22233 and α = (2,2,1): twelve fitting words give t³ + 8t² + 3t.", DescribeRole.Definition),
            Node("interlaces", "Interlacing with multiplicity", "Interlaces", Interlacing(),
                "Definition 8, page 6: ‘Let f and g be polynomials with positive leading coefficients and real, non-positive zeros, aᵢ and bᵢ, respectively. We say that f interlaces g, and we write f ≼ g if ⋯ ≤ a₃ ≤ b₃ ≤ a₂ ≤ b₂ ≤ a₁ ≤ b₁ ≤ 0. Note that deg(f) = deg(g) or deg(f) + 1 = deg(g).’ roots is Mathlib's root multiset; sort(roots, (· >= ·)) orders it decreasingly without dropping repeated zeros. The two comparisons use zero-based i. They are exactly aᵢ₊₁ ≤ bᵢ₊₁ and, where it exists, bᵢ₊₂ ≤ aᵢ₊₁. Positive leading coefficients exclude the zero polynomial; Splits makes the multiset lengths equal the degrees. The stated degree alternatives make every compared entry valid, so the default zero in getD is never used.", DescribeRole.Definition),
            Node("claim", "Conjecture 28, including both clauses", "claim", Claim(),
                "Conjecture 28, page 12: ‘For Ferrers boards, the polynomial R(λ, α; t) is real-rooted. Moreover, Rλ₁(λ, α; t), Rλ₁−1(λ, α; t), . . . , R₂(λ, α; t), R₁(λ, α; t) forms an interlacing sequence.’ Definition 9, page 6: ‘A sequence F = (f₁, . . . , fₙ) of real-rooted polynomials is interlacing if fᵢ ≼ fⱼ for 1 ≤ i < j ≤ n.’ The formula quantifies all positive n, all k, all monotone boards and all contents summing to n. The nonzero hypotheses on both refined polynomials are explicit. Since the sequence runs in decreasing letter order, p > q requires R_p to interlace R_q. The binder h is the proof that n is positive, needed to form the first position ⟨0,h⟩.", DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("Refutation on board 333344"), StatementSource.FromAuthor(F.Disp(new Formula.Not(Id("claim")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The content (2,2,1,1) on the board (3,3,3,3,4,4) has sixty fitting words. The two relevant refinements are R₁ = 2X⁴ + 15X³ + 7X² = X²(X+7)(2X+1) and R₃ = X³ + 8X² + 3X. Their decreasing roots, with multiplicity, are respectively [0,0,−1/2,−7] and [0,−4+√13,−4−√13]. Since 3 < √13 < 4, the bottom comparison would require −7 ≤ −4−√13, which is false. This refutes the interlacing-sequence clause and hence the conjunction. The universal real-rootedness clause is not decided by this refutation."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("alexandersson-jal-quemener-2025-rook-eulerian-interlacing"),
                    ResolutionKind.Refuted))
        ), []));

    private static DocumentBlock Node(string id, string title, string name, Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(F.Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula N => F.Seq(F.Mathbb, F.Grp(F.Id("N")));
    private static Formula Reals => F.Seq(F.Mathbb, F.Grp(F.Id("R")));
    private static Formula ListN => Call("List", N);
    private static Formula Polynomials => F.Seq(Reals, F.OpenBracket, Id("X"), F.CloseBracket);
    private static Formula Fin(Formula size) => Call("Fin", size);
    private static Formula Parenthesized(Formula value) => F.Seq(F.Open, value, F.Close);
    private static Formula All(string variable, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), type, body);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Or(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Or, right);
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Lt(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Le(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Lambda(string variable, Formula type, Formula body) =>
        F.Seq(Parenthesized(F.Seq(Id(variable), F.Colon, type)), F.Mapsto, body);
    private static Formula SumOver(string variable, Formula domain, Formula body) =>
        F.Seq(new Formula.Subscript(F.Sum, F.Seq(Id(variable), F.InMacro, domain)), body);
    private static Formula Parameters(Formula body) => All("n", N, All("k", N,
        All("l", new Formula.TypeArrow(Fin(Id("n")), N),
        All("a", new Formula.TypeArrow(Fin(Id("k")), N), body))));
    private static Formula Get(Formula word, Formula index) => Call("getD", word, index, Num(0));

    private static Formula Words()
    {
        var i = Id("i"); var w = Id("w"); var c = Id("c");
        var contents = Call("flatMap", Call("finRange", Id("k")), Lambda("c", Fin(Id("k")),
            Call("replicate", Call("a", c), Add(Call("val", c), Num(1)))));
        var rows = All("i", Fin(Id("n")), And(Lt(Num(0), Get(w, Call("val", i))),
            Le(Get(w, Call("val", i)), Call("l", i))));
        return Parameters(Equal(Call("W", Id("l"), Id("a")),
            Call("filter", Call("toFinset", new Formula.Apply(F.Seq(Id("permutations"), F.Apos), [contents])), Lambda("w", ListN, rows))));
    }
    private static Formula Ascents() => All("w", ListN, Equal(Call("asc", Id("w")),
        Call("card", Call("filter", Call("range", Subtract(Call("length", Id("w")), Num(1))),
            Lambda("i", N, Lt(Get(Id("w"), Id("i")), Get(Id("w"), Add(Id("i"), Num(1)))))))));
    private static Formula Full() => Parameters(Equal(Call("R", Id("l"), Id("a")),
        SumOver("w", Call("W", Id("l"), Id("a")), new Formula.Power(Id("X"), Call("asc", Id("w"))))));
    private static Formula Refined() => Parameters(All("j", N, Equal(Call("Rj", Id("l"), Id("a"), Id("j")),
        SumOver("w", Call("filter", Call("W", Id("l"), Id("a")),
            Lambda("u", ListN, Equal(Get(Id("u"), Num(0)), Id("j")))),
            new Formula.Power(Id("X"), Call("asc", Id("w")))))));
    private static Formula Roots(string name) => Call("roots", Id(name));
    private static Formula Card(string name) => Call("card", Roots(name));
    private static Formula SortedGet(string name, Formula i) => Get(Call("sort", Roots(name), Parenthesized(new Formula.Relation(new Formula.Placeholder(), FormulaRelationOperator.GreaterThanOrEqual, new Formula.Placeholder()))), i);
    private static Formula Interlacing()
    {
        var i = Id("i");
        var comparison = All("i", N, Imp(Lt(i, Card("f")),
            And(Le(SortedGet("f", i), SortedGet("g", i)),
                Imp(Lt(Add(i, Num(1)), Card("g")), Le(SortedGet("g", Add(i, Num(1))), SortedGet("f", i))))));
        var degree = Or(Equal(Call("natDegree", Id("g")), Call("natDegree", Id("f"))),
            Equal(Call("natDegree", Id("g")), Add(Call("natDegree", Id("f")), Num(1))));
        var tail = And(degree, comparison);
        tail = And(All("x", Reals, Imp(new Formula.Relation(Id("x"), FormulaRelationOperator.MemberOf, Roots("g")), Le(Id("x"), Num(0)))), tail);
        tail = And(All("x", Reals, Imp(new Formula.Relation(Id("x"), FormulaRelationOperator.MemberOf, Roots("f")), Le(Id("x"), Num(0)))), tail);
        tail = And(Call("Splits", Id("g")), tail);
        tail = And(Call("Splits", Id("f")), tail);
        tail = And(Lt(Num(0), Call("leadingCoeff", Id("g"))), tail);
        tail = And(Lt(Num(0), Call("leadingCoeff", Id("f"))), tail);
        return All("f", Polynomials, All("g", Polynomials, Equal(Call("Interlaces", Id("f"), Id("g")), tail)));
    }
    private static Formula Claim()
    {
        var l = Id("l"); var a = Id("a"); var p = Id("p"); var q = Id("q");
        var rp = Call("Rj", l, a, p); var rq = Call("Rj", l, a, q);
        var pair = All("p", N, All("q", N, Imp(Le(Num(1), q), Imp(Lt(q, p),
            Imp(Le(p, Call("l", F.Seq(F.Langle, Num(0), F.Comma, Id("h"), F.Rangle))),
            Imp(NotEqual(rp, Num(0)), Imp(NotEqual(rq, Num(0)), Call("Interlaces", rp, rq))))))));
        return Equal(Id("claim"), Parameters(All("h", Parenthesized(Lt(Num(0), Id("n"))),
            Imp(Call("Monotone", l), Imp(Equal(SumOver("c", Fin(Id("k")), Call("a", Id("c"))), Id("n")),
                And(Call("Splits", Call("R", l, a)), pair))))));
    }
}

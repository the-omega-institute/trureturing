using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permutation;

internal sealed class MultisetRookEulerianRealRootednessRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Permutation/MultisetRookEulerianRealRootednessRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/alexanderssonjalquemener2025rook");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Remaining-content counting for the full multiset rook-Eulerian polynomial.",
        H("The full multiset rook-Eulerian polynomial"),
        Blocks(
            Paragraph(Text("The source is Alexandersson, Jal and Quemener, arXiv:2502.05939v1, Section 3.3, equation (10) and the first clause of Conjecture 28. A word contains a(c) copies of the positive letter c+1 and fits the row bounds l. Repeated letters and repeated columns are allowed. The polynomial R is the original sum of X raised to the strict adjacent ascent count, over distinct words W. The original W, asc and R definitions are used directly. There is no initial or terminal ascent, skew inner board, nonattacking restriction or first-letter refinement.")),
            Describe.Lean(DescribeId.Create("claim"), DeclarationHandle.Create(Prefix + "claim"),
                H("The full real-rootedness assertion"), StatementSource.FromAuthor(F.Disp(Claim())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The assertion quantifies every positive row count n, every alphabet size k, every positive weakly increasing row-bound function l, and every natural-valued content a summing to n. It requires the original full R to split over the real field, retaining algebraic multiplicity. Polynomial.Splits includes the zero polynomial; no admissible-word or nonzero-polynomial premise is added. This is only the first clause. The separate interlacing refutation concerns the second clause."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("edge"), DeclarationHandle.Create(Prefix + "edge"),
                H("The boundary edge"), StatementSource.FromAuthor(F.Disp(Edge())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An absent previous letter contributes exponent zero. A present previous letter i contributes one exactly when i<j. Equal adjacent letters therefore contribute zero."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("count"), DeclarationHandle.Create(Prefix + "count"),
                H("Remaining-content recurrence"), StatementSource.FromAuthor(F.Disp(Count())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The state consists of the remaining row list r, a multiset m of remaining positive letters, and an optional previous letter h. On a nonempty row list, the recurrence chooses each distinct available label j once, subject to 0<j and j no larger than the next row bound. It erases one copy of j and multiplies the continuation by X to the boundary-edge exponent. There is no factor equal to the number of remaining copies of j. Each step shortens the row list. With no rows left, the value is one exactly when no letters remain, and zero otherwise. In particular an empty board with empty content contributes the unique empty word, and impossible completions contribute zero."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("count-equality"), DeclarationHandle.Create(Prefix + "count_eq_R"),
                H("Equality with the original full word sum"),
                StatementSource.FromAuthor(F.Disp(CountEquality())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The multiset m(a) contains a(c) copies of c+1 for each c in Fin(k), and ofFn(l) lists the row bounds in their original order. The map from natural to real coefficients is the canonical cast homomorphism. The total-content equality is essential: it makes each rearrangement have exactly n letters, so every original getD row query is in range. The theorem requires neither positivity nor monotonicity of the board and includes n=0, k=0 and zero-content labels.")),
                    Paragraph(Text("Partition completions by their next letter. Erasing that letter and prepending it are inverse on the corresponding class, and classes for different next letters are disjoint. The multiset equality records the exact multiplicities. Pinned List.mem_permutations' identifies the original permutation-list membership with permutation of the content list; toFinset removes repeated listings of the same word. A separate head-edge calculation identifies the recursive weight with X to the original asc. Summing the disjoint classes proves the recurrence equality. Thus the recurrence computes the full polynomial of the source, including all repeated letters, rather than a refinement or a finite replacement."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("A counterexample to full real-rootedness"),
                StatementSource.FromAuthor(F.Disp(new Formula.Not(Id("claim")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Take n=120 and k=6. The board has three rows of length 2, four of length 3, ten of length 4, two of length 5, and 101 of length 6. All bounds are positive and weakly increasing. The content is (6,1,4,8,1,100), with total 120. The first 19 rows exclude the letter 6. Every remaining tail therefore contains 100 sixes and exactly one smaller letter j. For the last prefix letter h, its exact completion polynomial is X^(1+[h<j])+X+99X^2: the two endpoint positions and 99 internal positions account for every tail once. The source recurrence proves this identity by induction, then evaluates the 664 reachable prefix states. Applying the exact full-R counting bridge gives the following full polynomial, including its two zero low coefficients.")),
                    Paragraph(Math(ConcretePolynomial())),
                    Paragraph(Text("In particular R(1)=73492650 and the degree is 11. At x=-1/100 the value of (R'(x))^2-R(x)R''(x) is exactly -2294232329562528073294509555513/12500000000000000000000000000000000000, which is negative. The original laguerre_splits theorem in SourceJensenPositiveExtension states that every real polynomial splitting over the reals has a nonnegative value of this expression at every real argument. Its hypotheses require no positivity, monicity, nonzero condition, root sign or simple roots. Applying it directly contradicts the displayed value.")),
                    Paragraph(Text("Thus the first clause of Conjecture 28 fails for the original full multiset polynomial. This conclusion uses neither refined interlacing nor numerical root isolation. It preserves repeated columns and strict adjacent ascents. The earlier six-row interlacing counterexample remains a separate result about the second clause. Rectangular-board theorems and the distinct-letter theorem are unaffected."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("alexandersson-jal-quemener-2025-rook-eulerian-interlacing"),
                    ResolutionKind.Refuted))
        ), []));

    private static Formula Id(string s) => F.Id(s);
    private static Formula N => F.Seq(F.Mathbb, F.Grp(Id("N")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula ListN => Call("List", N);
    private static Formula MultiN => Call("Multiset", N);
    private static Formula OptionN => Call("Option", N);
    private static Formula All(string x, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), t, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Sum(string x, Formula domain, Formula body) =>
        F.Seq(new Formula.Subscript(F.Sum, F.Seq(Id(x), F.InMacro, domain)), body);
    private static Formula Lam(string x, Formula t, Formula body) =>
        F.Seq(F.Open, Id(x), F.Colon, t, F.Close, F.Mapsto, body);
    private static Formula Parameters(Formula b) => All("n", N, All("k", N,
        All("l", new Formula.TypeArrow(Fin(Id("n")), N),
        All("a", new Formula.TypeArrow(Fin(Id("k")), N), b))));
    private static Formula Total => Equal(Sum("c", Fin(Id("k")), Call("a", Id("c"))), Id("n"));
    private static Formula Claim() => Equal(Id("claim"), Parameters(Imp(Lt(Num(0), Id("n")),
        Imp(All("i", Fin(Id("n")), Lt(Num(0), Call("l", Id("i")))),
        Imp(Call("Monotone", Id("l")), Imp(Total, Call("Splits", Call("R", Id("l"), Id("a")))))))));
    private static Formula Edge() => All("i", N, All("j", N, And(
        Equal(Call("edge", Id("none"), Id("j")), Num(0)),
        Equal(Call("edge", Call("some", Id("i")), Id("j")),
            Call("ite", Lt(Id("i"), Id("j")), Num(1), Num(0))))));
    private static Formula Count()
    {
        var m = Id("m"); var h = Id("h"); var r = Id("r"); var s = Id("s"); var j = Id("j");
        var terminal = All("m", MultiN, All("h", OptionN,
            Equal(Call("count", Id("nil"), m, h), Call("ite", Equal(m, Num(0)), Num(1), Num(0)))));
        var choices = Call("filter", Call("toFinset", m), Lam("j", N, And(Lt(Num(0), j), Le(j, r))));
        var step = All("r", N, All("s", ListN, All("m", MultiN, All("h", OptionN,
            Equal(Call("count", Call("cons", r, s), m, h),
                Sum("j", choices, Multiply(new Formula.Power(Id("X"), Call("edge", h, j)),
                    Call("count", s, Call("erase", m, j), Call("some", j)))))))));
        return And(terminal, step);
    }
    private static Formula CountEquality() => Parameters(Imp(Total,
        Equal(Call("map", Call("count", Call("ofFn", Id("l")), Call("m", Id("a")), Id("none")),
                Call("NatCastReal")), Call("R", Id("l"), Id("a")))));

    private static Formula ConcretePolynomial()
    {
        long[] coefficients = [0, 0, 1, 261, 21704, 591814, 5372605, 18550680,
            27147806, 17137014, 4318325, 352440];
        Formula polynomial = new Formula.Power(Id("X"), Num(2));
        for (var d = 3; d < coefficients.Length; d++)
            polynomial = Add(polynomial, Multiply(Num(coefficients[d]), new Formula.Power(Id("X"), Num(d))));
        return F.Disp(Equal(Id("R"), polynomial));
    }
}

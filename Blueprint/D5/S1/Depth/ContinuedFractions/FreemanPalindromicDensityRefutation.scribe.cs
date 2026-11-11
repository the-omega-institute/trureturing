using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Depth.ContinuedFractions;

internal sealed class FreemanPalindromicDensityRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Depth/ContinuedFractions/FreemanPalindromicDensityRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/freeman2017generalized");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive non-eventually-periodic sequence has 2-palindromic upper-limsup density one.",
        H("Freeman's Upper-Limsup Density Bound Fails"),
        Blocks(
            Node("freeman-finite-cf", "Finite rational continued fractions", "finiteCF",
                FiniteCFFormula(),
                "Section 2 (page 2) writes: “Given i∈ℕ₀, a (rational) continued fraction is "
                    + "denoted by [a₀,a₁,…,aᵢ], where a₀∈ℕ₀ and, for each k such that "
                    + "1≤k≤i, we have aₖ∈ℕ.” The rational evaluator is GenContFract.convs' "
                    + "at tail.length, with all partial numerators equal to one. The empty-list "
                    + "value zero is excluded from every qualifying prefix.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("freeman-finite-m-palindrome", "Finite m-palindromes", "IsFiniteMPalindrome",
                FinitePalindromeFormula(),
                "Section 2 (pages 2–3): “Given A=(a₀,…,aᵢ)∈ℕ*, the reversal of A is defined as Ã = (aᵢ,…,a₀). If there exists a number m∈ℕ such that [A]=m[Ã], we say that A is an m-palindrome, or m-palindromic.” "
                    + "Lists encode finite words. List.reverse reverses their digits; every "
                    + "digit and the length of a qualifying word are strictly positive.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("freeman-prefix-length", "Qualifying positive prefix lengths", "PrefixLength",
                PrefixFormula(),
                "A prefix of length n consists of the digits A(0),…,A(n−1), formed by "
                    + "List.ofFn on Fin n. Section 2 (page 2): “For A∈𝒜*, we write |A| "
                    + "to denote the number of terms in A, and say that A has length |A|.” "
                    + "Thus the prefix ending at index i has length i+1.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("freeman-infinite-m-palindrome", "Infinite m-palindromic sequences", "IsMPalindromic",
                InfinitePalindromeFormula(),
                "Section 2 (page 3): “In the case of an irrational continued fraction α=[A]=[a₀,a₁,…], we say that α (equivalently, A) is an m-palindrome, or m-palindromic, if there exist infinitely many indices i for which the prefix (a₀,…,aᵢ) is an m-palindrome.” "
                    + "Infinite sets of positive lengths express precisely this condition.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("freeman-density", "The upper-limsup density", "density", DensityFormula(),
                "Section 6 (page 8): “Given any irrational m-palindromic continued fraction α=[A], let {Pₖ(A)}ₖ₌₀⁺∞ denote a sequence of m-palindromic prefixes (a₀,…,aᵢₖ) for A such that, for each k∈ℕ, there is no index j such that iₖ₋₁<j<iₖ and for which (a₀,…,a_j) is an m-palindrome. Define the m-palindromic density of α to be the number” "
                    + "dₘ(α)=limsup_{k→+∞}|Pₖ(A)|/|Pₖ₊₁(A)|. "
                    + "Nat.nth enumerates every qualifying length increasingly; both lengths are "
                    + "cast to ℝ before division.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("freeman-conjecture-upper-bound", "Conjecture 7.1, first sentence", "claim",
                Disp(Seq(Call("claim"), Iff, Sp, Parenthesized(ClaimBody()))),
                "Conjecture 7.1 (page 10): “For m∈ℕ and A∈ℕ^ℕ₀ an m-palindromic sequence that is not eventually periodic, we have dₘ([A])≤1/φ. Furthermore, for r,s∈ℕ with r≠s, we have dₘ([F(m,r,s)])=1/φ.” "
                    + "Only the first sentence is asserted by claim. Lean ℕ includes zero, "
                    + "so m>0 and positivity of every digit are explicit. Eventual periodicity "
                    + "means ∃s p:ℕ, p>0 ∧ ∀t, A(s+t+p)=A(s+t). Real.goldenRatio is "
                    + "(1+√5)/2. The separate Fibonacci equality is left open.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("freeman-density-refutation", "Density one refutes the upper bound", "result",
                Disp(Seq(Neg, Sp, Parenthesized(ClaimBody()))),
                "Set m=2. Begin with the stage [4,2]; replace stage k by k+2 copies of "
                    + "it, then k+1 copies of [6,3], then k+2 further copies of stage k. "
                    + "The nested prefixes define a positive infinite sequence. Weighted "
                    + "transpose preserves the matrices of these stages and their powers, "
                    + "as in Freeman's Lemmas 3.1–3.2 and section-7 block substitution. "
                    + "Lengths (k+1)·length(stage k) and (k+2)·length(stage k) both qualify. "
                    + "The next length in the complete list is at most the latter, so "
                    + "arbitrarily late consecutive ratios are at least (k+1)/(k+2). "
                    + "Their upper limsup is one. Arbitrarily long [6,3] blocks followed by [4,2] exclude "
                    + "every eventual period. Since 1/Real.goldenRatio<1, the asserted "
                    + "universal upper bound fails. The finite computations establish no "
                    + "infinite conclusion.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("palindromic-density"), ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Natural() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Rational() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Word() => Call("List", Natural());
    private static Formula Sequence() => Seq(Natural(), Sp, To, Sp, Natural());
    private static Formula Q(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => App(F.Id(name), args);
    private static Formula App(Formula function, params Formula[] args) =>
        args.Length == 0 ? function : Seq(function, Parenthesized(CommaJoin(args)));
    private static Formula CommaJoin(Formula[] args) =>
        args.Length == 1 ? args[0] : Seq(args[0], Comma, Sp, CommaJoin(args[1..]));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula And(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Cast(Formula x, Formula type) => Parenthesized(Seq(x, Colon, Sp, type));
    private static Formula Nil() => Seq(OpenBracket, CloseBracket);
    private static Formula Cons(Formula a, Formula tail) => Seq(a, Colon, Colon, tail);
    private static Formula Length(Formula xs) => App(Q("List", "length"), xs);
    private static Formula Lam(string name, Formula type, Formula body) =>
        Seq(Operatorname, Grp(F.Id("fun")), Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, type)),
            Sp, Mapsto, Sp, body);
    private static Formula Pair(Formula a, Formula b) => Seq(Langle, Sp, a, Comma, Sp, b, Rangle);

    private static Formula FiniteCFFormula()
    {
        var a = F.Id("a");
        var tail = F.Id("tail");
        var pair = Pair(D(1), Cast(F.Id("b"), Rational()));
        var pairs = App(Q("List", "map"), Lam("b", Natural(), pair), tail);
        var ofList = Seq(Operatorname, Grp(F.Id("Stream")), Apos, Dot,
            Operatorname, Grp(F.Id("Seq")), Dot, Operatorname, Grp(F.Id("ofList")));
        var gcf = Cast(Pair(Cast(a, Rational()), App(ofList, pairs)), Call("GenContFract", Rational()));
        var convs = Seq(Q("GenContFract", "convs"), Apos);
        return Disp(And(Seq(Call("finiteCF", Nil()), Eq, D(0)),
            All("a", Natural(), All("tail", Word(),
                Seq(Call("finiteCF", Cons(a, tail)), Eq, App(convs, gcf, Length(tail)))))));
    }

    private static Formula FinitePalindromeFormula()
    {
        var m = F.Id("m");
        var u = F.Id("U");
        var positive = All("a", Natural(), Seq(F.Id("a"), Sp, InMacro, Sp, u, Sp,
            Implies, Sp, D(0), Lt, F.Id("a")));
        var equality = Seq(Call("finiteCF", u), Eq, Cast(m, Rational()), Cdot, Sp,
            Call("finiteCF", App(Q("List", "reverse"), u)));
        return Disp(All("m", Natural(), All("U", Word(), Seq(
            Call("IsFiniteMPalindrome", m, u), Iff, Sp,
            Parenthesized(And(Seq(u, Neq, Sp, Nil()), And(positive, equality)))))));
    }

    private static Formula PrefixFormula()
    {
        var m = F.Id("m");
        var a = F.Id("A");
        var n = F.Id("n");
        var digits = App(Q("List", "ofFn"), Lam("i", Call("Fin", n),
            App(a, App(Call("val"), F.Id("i")))));
        return Disp(All("m", Natural(), All("A", Sequence(), All("n", Natural(), Seq(
            Call("PrefixLength", m, a, n), Iff, Sp,
            Parenthesized(And(Seq(D(0), Lt, n), Call("IsFiniteMPalindrome", m, digits))))))));
    }

    private static Formula InfinitePalindromeFormula()
    {
        var m = F.Id("m");
        var a = F.Id("A");
        var lengths = Seq(OpenBrace, F.Id("n"), Colon, Sp, Natural(), Sp, Bar, Sp,
            Call("PrefixLength", m, a, F.Id("n")), CloseBrace);
        return Disp(All("m", Natural(), All("A", Sequence(), Seq(
            Call("IsMPalindromic", m, a), Iff, Sp, App(Q("Set", "Infinite"), lengths)))));
    }

    private static Formula DensityFormula()
    {
        var m = F.Id("m");
        var a = F.Id("A");
        var k = F.Id("k");
        var predicate = App(F.Id("PrefixLength"), m, a);
        var numerator = Cast(App(Q("Nat", "nth"), predicate, k), Real());
        var denominator = Cast(App(Q("Nat", "nth"), predicate, Seq(k, Plus, D(1))), Real());
        var ratio = new Formula.Fraction(numerator, denominator);
        var limsup = App(Q("Filter", "limsup"), Lam("k", Natural(), ratio), Q("Filter", "atTop"));
        return Disp(All("m", Natural(), All("A", Sequence(), Seq(Call("density", m, a), Eq, limsup))));
    }

    private static Formula ClaimBody()
    {
        var m = F.Id("m");
        var a = F.Id("A");
        var positive = All("n", Natural(), Seq(D(0), Lt, App(a, F.Id("n"))));
        var notPeriodic = Seq(Neg, Sp, App(
            Seq(Q("D5", "S1"), Dot, Operatorname, Grp(F.Id("Words")), Dot,
                Operatorname, Grp(F.Id("Complexity")), Dot,
                Operatorname, Grp(F.Id("EventuallyPeriodicWord"))), a));
        var bound = Seq(Call("density", m, a), Leq, Sp,
            new Formula.Fraction(D(1), Q("Real", "goldenRatio")));
        return All("m", Natural(), Seq(D(0), Lt, m, Sp, Implies, Sp,
            All("A", Sequence(), Seq(Parenthesized(positive), Sp, Implies, Sp,
                Call("IsMPalindromic", m, a), Sp, Implies, Sp, notPeriodic, Sp,
                Implies, Sp, bound))));
    }
}

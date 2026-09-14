using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns;

internal sealed class DerangementLimitsCofinalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Patterns/DerangementLimitsCofinal.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/vatter2026assortment");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bounded decreasing tails yield derangement limits cofinal below one.",
        H("No Largest Derangement Limit Below One"),
        Blocks(
            Paragraph(Text(
                "The paragraph following Question 4.3 in Section 4 of "),
                Ref("D5/L/Words/vatter2026assortment"), Text(
                " asks: Is there a largest possible limit strictly less than 1? "
                + "The question concerns arbitrary permutation classes, with no growth restriction. "
                + "The construction below answers this question negatively. It gives limits "
                + "arbitrarily close to one from below, without classifying all possible limits.")),
            Paragraph(Text(
                "Perm(n) denotes Equiv.Perm(Fin(n)). Positions and values are numbered from zero; "
                + "val is the underlying natural number of a Fin element or the underlying "
                + "permutation of a subtype element, as appropriate. P(n,a) denotes tailPerm "
                + "with the displayed assumption a<=n. C(k) denotes boundedTailClass(k). "
                + "The containment relation Contains, the hereditary-class structure PermClass, "
                + "the fixed-point-free predicate IsDerangement, and the real-valued ratio "
                + "are those of "),
                Ref("D5/S1/Words/Patterns/DerangementRatioNonconvergence"), Text(
                ". Nonempty(S) means that the set S contains a permutation. "
                + "Every cardinality is Fintype.card; all quotients of cardinalities or "
                + "natural parameters in a real formula use their real casts.")),
            Node("tailPerm", "The two-block permutation", PermutationFormula(),
                "In one-based notation this is (a+1,...,n,a,...,1). The head increases "
                + "through the high values and the tail decreases through the low values. "
                + "The inverse sends a value j to j-a when a<=j and to n-1-j otherwise. "
                + "The two branches are inverse bijections on the corresponding disjoint "
                + "intervals. Either block can be empty, and length zero is included.",
                DescribeRole.Definition),
            Node("pattern_tailPerm", "Patterns retain a bounded tail", PatternFormula(),
                "Let f be the order embedding selecting the pattern. There is a cut b "
                + "such that f(i) is in the original head exactly when i<b. To obtain it, "
                + "take the least b after which every selected position is in the tail; "
                + "monotonicity of f makes every earlier selected position a head position. "
                + "The m-b selected tail positions inject into the original a tail positions. "
                + "For i<j, the selected values increase exactly when j<b. The permutation "
                + "P(m,m-b) has precisely the same comparisons. Composing one permutation "
                + "with the inverse of the other gives a strictly increasing self-map of "
                + "a finite chain, which is the identity. Hence the pattern equals P(m,m-b)."),
            Node("boundedTailClass", "The hereditary class", ClassFormula(),
                "Membership means being one of the permutations with tail length at most k. "
                + "The preceding theorem supplies arbitrary-pattern closure: a contained "
                + "pattern has tail length at most that of the containing permutation, "
                + "and therefore still at most k. Membership concerns permutations themselves; "
                + "different witnesses for a do not create distinct members.", DescribeRole.Definition),
            Node("boundedTailClass_counts", "Exact eventual counts", CountsFormula(),
                "When n>2*k+2, every a from 0 through k has a nonempty head. Its first "
                + "value is a, so these k+1 permutations are distinct and exhaust the slice. "
                + "The parameter a=0 gives the identity, which has a fixed point because n>0. "
                + "For a>0 a head position shifts upward by a. A tail position is at least "
                + "n-a, whereas its value is less than a; the threshold separates these "
                + "intervals. Thus precisely the k positive parameters give derangements. "
                + "Bijections from Fin(k+1) and Fin(k) give the two displayed subtype counts. "
                + "No distinctness claim is made at smaller lengths: P(n,n) and P(n,n-1) "
                + "coincide when n>0."),
            Node("exists_derangement_limit_between", "Attained limits are cofinal below one",
                EndpointFormula(),
                "For a real q<1 choose a natural k greater than q/(1-q). Positive-denominator "
                + "arithmetic gives q<k/(k+1)<1. Choose C(k) and this real limit. At every "
                + "length P(n,0) is a member, so all slices are nonempty. The two exact counts "
                + "make the ratio identically k/(k+1) for n>2*k+2, and eventual constancy "
                + "gives convergence. Applying the theorem to any attained limit below one "
                + "produces a larger attained limit still below one. These classes have "
                + "eventually constant slice cardinality; the assertion is the arbitrary-class "
                + "question. The cited source supplies the question; the construction and "
                + "proof are derived here.", DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("vatter-largest-derangement-limit-below-one"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role = DescribeRole.Theorem,
        AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("derangement-limits-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula N() => F.Id("n");
    private static Formula M() => F.Id("m");
    private static Formula K() => F.Id("k");
    private static Formula A() => F.Id("a");
    private static Formula C() => F.Id("C");
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Par(Formula formula) => Seq(Open, formula, Close);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);
    private static Formula Perm(Formula length) => Call("Perm", length);
    private static Formula P(Formula length, Formula tail) => Call("P", length, tail);
    private static Formula Family() => Call("C", K());
    private static Formula Mem(Formula family, Formula length) => Call("mem", family, length);
    private static Formula Bound(Formula variable, Formula type) =>
        Seq(Forall, Sp, variable, Colon, Sp, type, Comma, Sp);
    private static Formula ExistsIn(Formula variable, Formula type) =>
        Seq(Exists, Sp, variable, Colon, Sp, type, Comma, Sp);
    private static Formula Leq(Formula first, Formula second) => Seq(first, Sp, Le, Sp, second);
    private static Formula Less(Formula first, Formula second) => Seq(first, Sp, Lt, Sp, second);
    private static Formula EqualTo(Formula first, Formula second) => Seq(first, Sp, Eq, Sp, second);
    private static Formula Member(Formula value, Formula set) => Seq(value, Sp, InMacro, Sp, set);
    private static Formula Subtype(Formula variable, Formula type, Formula predicate) =>
        Seq(OpenBrace, variable, Colon, Sp, type, Sp, Mid, Sp, predicate, CloseBrace);
    private static Formula And(Formula first, Formula second) => Seq(first, Sp, Land, Sp, second);

    private static Formula PermutationFormula()
    {
        var i = F.Id("i");
        var value = Call("val", i);
        var headLength = Seq(N(), Sp, Minus, Sp, A());
        return Disp(Seq(Bound(N(), Naturals()), Bound(A(), Naturals()),
            Leq(A(), N()), Sp, Implies, Sp,
            And(Seq(P(N(), A()), Colon, Sp, Perm(N())),
                Par(Seq(Bound(i, Call("Fin", N())),
                    EqualTo(Call("val", Apply(P(N(), A()), i)),
                        Seq(Named("if"), Sp, Less(value, headLength), Sp,
                            Named("then"), Sp, A(), Sp, Plus, Sp, value, Sp,
                            Named("else"), Sp, N(), Sp, Minus, Sp, D(1), Sp, Minus, Sp, value)))))));
    }

    private static Formula PatternFormula()
    {
        var t = F.Id("t");
        return Disp(Seq(Bound(M(), Naturals()), Bound(N(), Naturals()), Bound(A(), Naturals()),
            Leq(A(), N()), Sp, Implies, Sp, Bound(SigmaLower, Perm(M())),
            Call("Contains", SigmaLower, P(N(), A())), Sp, Implies, Sp,
            ExistsIn(t, Naturals()), And(Leq(t, M()),
                And(Leq(t, A()), EqualTo(SigmaLower, P(M(), t))))));
    }

    private static Formula Downset() => Seq(Bound(M(), Naturals()), Bound(N(), Naturals()),
        Bound(SigmaLower, Perm(M())), Bound(Pi, Perm(N())),
        Member(Pi, Mem(Family(), N())), Sp, Implies, Sp,
        Call("Contains", SigmaLower, Pi), Sp, Implies, Sp,
        Member(SigmaLower, Mem(Family(), M())));

    private static Formula ClassFormula() => Disp(new Formula.Aligned([
        Seq(Bound(K(), Naturals()), Family(), Colon, Sp, Named("PermClass")),
        Seq(Bound(K(), Naturals()), Bound(N(), Naturals()),
            EqualTo(Mem(Family(), N()), Subtype(Pi, Perm(N()),
                Seq(ExistsIn(A(), Naturals()), And(Leq(A(), N()),
                    And(Leq(A(), K()), EqualTo(Pi, P(N(), A())))))))),
        Seq(Bound(K(), Naturals()), Call("downset", Family()), Colon, Sp, Downset())
    ]));

    private static Formula CountsFormula() => Disp(Seq(Bound(K(), Naturals()),
        Bound(N(), Naturals()),
        Less(Seq(D(2), Sp, Times, Sp, K(), Sp, Plus, Sp, D(2)), N()), Sp, Implies, Sp,
        And(EqualTo(Call("card", Mem(Family(), N())), Seq(K(), Sp, Plus, Sp, D(1))),
            EqualTo(Call("card", Subtype(Pi, Mem(Family(), N()),
                Call("IsDerangement", Call("val", Pi)))), K()))));

    private static Formula EndpointFormula()
    {
        var q = F.Id("q");
        var l = F.Id("l");
        return Disp(Seq(Bound(q, Reals()), Less(q, D(1)), Sp, Implies, Sp,
            ExistsIn(C(), Named("PermClass")), ExistsIn(l, Reals()),
            And(Less(q, l), And(Less(l, D(1)),
                And(Par(Seq(Bound(N(), Naturals()), Call("Nonempty", Mem(C(), N())))),
                    Call("Tendsto", Call("ratio", C()), Named("atTop"), Call("nhds", l)))))));
    }
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Sumfree;

internal sealed class GreedyThreeSumfreeTwoParameterDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Greedy three-sumfree membership has a universal two-parameter periodic formula.",
        H("The Two-Parameter Greedy Three-Sumfree Characterization"),
        Blocks(
            Paragraph(Text(
                "This repository proof establishes Conjecture 17 as printed on page 18 of "
                + "Bosma, Bruin, Fokkink, Grube, Reuijl and Tromp, Using Walnut to Solve Problems "
                + "from the OEIS, Journal of Integer Sequences 28 (2025), Article 25.3.8 "
                + "(arXiv:2503.04122). The source states a conjecture, not a prior proof. "
                + "Shtrezi's arXiv:2606.17447 treats the different third seed g+1, Conjecture 16. "
                + "All nine declarations below are derived here; these citations identify scope.")),
            Paragraph(Text(
                "Every integer variable is natural. Subtraction is truncated at zero, mod is "
                + "the natural-number remainder, Icc is the inclusive natural interval, union "
                + "is set union, image is direct image, and an indexed union binds its natural "
                + "index. A set used as a predicate means membership in that set.")),
            Node("RestrictedThreeSum", "Restricted sums of three distinct entries",
                RestrictedFormula(),
                "The strict inequalities order three different entries. The definition does "
                + "not assume they precede their sum; positivity supplies that fact on the "
                + "candidate set when comparing it with the greedy rule.", DescribeRole.Definition),
            Node("A", "The initial interval and translated periodic intervals", CandidateFormula(),
                "This is the stated union expression itself: the two isolated seeds, the "
                + "closed initial interval, and every translate with t at least one. The "
                + "translation function sends r to t times the modulus plus r.", DescribeRole.Definition),
            Node("greedyPrefix", "Literal least-next-entry greedy prefixes", PrefixFormula(),
                "Prefixes are stored in reverse order, so the head is the most recent entry; "
                + "headD has default zero. The minimum is Nat.find applied to the displayed "
                + "predicate. Its existence follows by taking a number above three times "
                + "the sum of the list and its head. Thus the recurrence is total, and for "
                + "the theorem's parameters it generates the increasing sequence starting "
                + "with 1, g, g+d. No periodic formula enters this definition.", DescribeRole.Definition),
            Node("S", "Membership in the greedy sequence", MembershipFormula(),
                "An integer occurs if it belongs to some generated prefix. A private "
                + "induction identifies these prefixes with an independent scan through "
                + "successive natural numbers, which obeys the greedy membership recurrence.",
                DescribeRole.Definition),
            Node("initial_gap_covered", "Coverage of the complete initial gap", InitialFormula(),
                "The construction uses (1+g)+I(0), one plus a distinct pair from I(0), g plus "
                + "a distinct pair from I(0), and a distinct triple from I(0), where "
                + "I(0)=Icc(g+d,2g+d). The last family covers the remaining interval from "
                + "M through M+a-1, with M=5g+2d and a=g+d-2. It is the fourth initial "
                + "family recorded in witness version two.", DescribeRole.Theorem),
            Node("periodic_gap_covered", "Coverage of every periodic gap", PeriodicFormula(),
                "For t at least one, write I(t)=tM+Icc(a,b), M=5g+2d, a=g+d-2, b=2g+d-2. "
                + "The four families are (1+g)+I(t), 1+I(0)+I(t), g+I(0)+I(t), and a "
                + "distinct pair from I(0) plus I(t). Interval-sum existence uses "
                + "Set.Icc_add_Icc; explicit pair constructions and the parameter inequalities "
                + "establish the overlaps and distinctness.", DescribeRole.Theorem),
            Node("restricted_three_sum_eq_complement", "The exact restricted-sum complement",
                ComplementFormula(),
                "Both gap-coverage theorems are used in the complement-to-sum direction. "
                + "Conversely, residue bounds exclude all candidate triple sums from A, "
                + "including the exceptional initial endpoints. This identity is used on "
                + "the live path to the characterization.", DescribeRole.Theorem),
            Node("conjecture17", "The full published characterization", CharacterizationFormula(),
                "The sumset identity proves that the candidate satisfies the greedy rule. "
                + "Strong induction gives uniqueness of that rule, and the prefix-scan "
                + "invariant transfers it to the literal least-next-entry sequence. The "
                + "four exceptions and the non-strict cutoff z at least g+d agree with the "
                + "published version. The result is universal in both parameters; finite "
                + "prefix checks are anonymous fidelity examples, not separate certificates.",
                DescribeRole.Theorem),
            Node("s_eq_A", "The greedy sequence equals the interval candidate",
                Disp(Seq(Parameters("g", "d"), Hypotheses(), Sp, Implies, Sp,
                    Parenthesized(Seq(Call("S", G(), DeltaParameter()), Sp, Eq, Sp,
                        Call("A", G(), DeltaParameter()))), Dot)),
                "The pointwise characterization and the candidate's residue description "
                + "give equality of the two predicates by function extensionality.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create("greedy-three-sumfree-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create("D5/S1/Words/Sumfree/GreedyThreeSumfreeTwoParameter." + name),
        H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), role);

    private static Formula RestrictedFormula()
    {
        var p = F.Id("P");
        var z = F.Id("z");
        return Disp(Seq(Forall, Sp, p, Colon, Sp,
            Parenthesized(Seq(Naturals(), Sp, To, Sp, Named("Prop"))), Comma, Sp,
            Bound(z), Comma, Sp, Call("RestrictedThreeSum", p, z), Sp, Leftrightarrow, Sp,
            TripleBody(z, x => Apply(p, x)), Dot));
    }

    private static Formula CandidateFormula()
    {
        var t = F.Id("t");
        var r = F.Id("r");
        var translate = Parenthesized(Seq(r, Sp, Mapsto, Sp, Add(Mul(t, Modulus()), r)));
        var blocks = Seq(new Formula.Subscript(Named("union"), Seq(t, Sp, Ge, Sp, D(1))), Sp,
            Call("image", translate, Call("Icc", Lower(), Upper())));
        return Disp(Seq(Parameters("g", "d"),
            Call("A", G(), DeltaParameter()), Sp, Eq, Sp,
            Call("union", Call("union", new Formula.SetLiteral([D(1), G()]),
                Call("Icc", Seed(), InitialEnd())), blocks), Dot));
    }

    private static Formula PrefixFormula()
    {
        var n = F.Id("n");
        var z = F.Id("z");
        var pn = Call("greedyPrefix", G(), DeltaParameter(), n);
        var eligible = Seq(Call("headD", pn, D(0)), Sp, Lt, Sp, z, Sp, Land, Sp,
            Neg, Sp, Parenthesized(TripleBody(z, x => Member(x, pn))));
        var choices = Seq(OpenBrace, z, Sp, InMacro, Sp, Naturals(), Sp, Mid, Sp, eligible, CloseBrace);
        return Disp(Seq(Parameters("g", "d"),
            Call("greedyPrefix", G(), DeltaParameter(), D(0)), Sp, Eq, Sp,
            ListLiteral(Seed(), G(), D(1)), Sp, Land, Sp,
            Parenthesized(Seq(Forall, Sp, Bound(n), Comma, Sp,
                Call("greedyPrefix", G(), DeltaParameter(), Add(n, D(1))), Sp, Eq, Sp,
                Call("cons", Seq(Min, Sp, choices), pn))), Dot));
    }

    private static Formula MembershipFormula() => Disp(Seq(
        Parameters("g", "d", "z"), Call("S", G(), DeltaParameter(), F.Id("z")),
        Sp, Leftrightarrow, Sp, Exists, Sp, Bound(F.Id("n")), Comma, Sp,
        Member(F.Id("z"), Call("greedyPrefix", G(), DeltaParameter(), F.Id("n"))), Dot));

    private static Formula InitialFormula() => Disp(new Formula.Aligned([
        Parameters("g", "d", "z"),
        Seq(Hypotheses(), Sp, Implies, Sp),
        Seq(Parenthesized(Seq(InitialEnd(), Sp, Lt, Sp, F.Id("z"), Sp, Land, Sp,
            F.Id("z"), Sp, Lt, Sp, Add(Parenthesized(Modulus()), Parenthesized(Lower())))),
            Sp, Implies, Sp),
        Seq(CandidateTriple(), Dot),
    ]));

    private static Formula PeriodicFormula()
    {
        var tm = Mul(F.Id("t"), Modulus());
        return Disp(new Formula.Aligned([
            Parameters("g", "d", "t", "z"),
            Seq(Hypotheses(), Sp, Implies, Sp, D(1), Sp, Le, Sp, F.Id("t"), Sp, Implies, Sp),
            Seq(Parenthesized(Seq(Add(tm, Parenthesized(Upper())), Sp, Lt, Sp,
                F.Id("z"), Sp, Land, Sp, F.Id("z"), Sp, Lt, Sp,
                Add(Add(tm, Parenthesized(Modulus())), Parenthesized(Lower())))),
                Sp, Implies, Sp),
            Seq(CandidateTriple(), Dot),
        ]));
    }

    private static Formula ComplementFormula() => Disp(new Formula.Aligned([
        Parameters("g", "d", "z"),
        Seq(Hypotheses(), Sp, Implies, Sp),
        Seq(Parenthesized(Seq(CandidateTriple(), Sp, Leftrightarrow, Sp,
            Parenthesized(Seq(Seed(), Sp, Lt, Sp, F.Id("z"), Sp, Land, Sp,
                Neg, Sp, Parenthesized(Member(F.Id("z"), Call("A", G(), DeltaParameter()))))))), Dot),
    ]));

    private static Formula CharacterizationFormula()
    {
        var z = F.Id("z");
        var residue = new Formula.Modulo(z, Modulus());
        var exceptions = Seq(z, Sp, Eq, Sp, D(1), Sp, Lor, Sp,
            z, Sp, Eq, Sp, G(), Sp, Lor, Sp,
            z, Sp, Eq, Sp, Subtract(InitialEnd(), D(1)), Sp, Lor, Sp,
            z, Sp, Eq, Sp, InitialEnd());
        var periodic = Parenthesized(Seq(Seed(), Sp, Le, Sp, z, Sp, Land, Sp,
            Lower(), Sp, Le, Sp, residue, Sp, Land, Sp, residue, Sp, Le, Sp, Upper()));
        return Disp(new Formula.Aligned([
            Parameters("g", "d", "z"),
            Seq(Hypotheses(), Sp, Implies, Sp),
            Seq(Parenthesized(Seq(Call("S", G(), DeltaParameter(), z), Sp, Leftrightarrow, Sp,
                Parenthesized(Seq(exceptions, Sp, Lor, Sp, periodic)))), Dot),
        ]));
    }

    private static Formula TripleBody(Formula z, Func<Formula, Formula> membership)
    {
        var x = F.Id("x");
        var y = F.Id("y");
        var w = F.Id("w");
        return Seq(Exists, Sp, x, Comma, Sp, y, Comma, Sp, w, Colon, Sp, Naturals(), Comma, Sp,
            Parenthesized(Seq(x, Sp, Lt, Sp, y, Sp, Land, Sp, y, Sp, Lt, Sp, w, Sp, Land, Sp,
                membership(x), Sp, Land, Sp, membership(y), Sp, Land, Sp, membership(w),
                Sp, Land, Sp, Add(Add(x, y), w), Sp, Eq, Sp, z)));
    }

    private static Formula Hypotheses() => Parenthesized(Seq(D(2), Sp, Le, Sp,
        DeltaParameter(), Sp, Land, Sp, Add(DeltaParameter(), D(1)), Sp, Le, Sp, G()));
    private static Formula CandidateTriple() =>
        Call("RestrictedThreeSum", Call("A", G(), DeltaParameter()), F.Id("z"));
    private static Formula G() => F.Id("g");
    private static Formula DeltaParameter() => F.Id("d");
    private static Formula Seed() => Add(G(), DeltaParameter());
    private static Formula InitialEnd() => Add(Mul(D(2), G()), DeltaParameter());
    private static Formula Modulus() => Add(Mul(D(5), G()), Mul(D(2), DeltaParameter()));
    private static Formula Lower() => Subtract(Seed(), D(2));
    private static Formula Upper() => Subtract(InitialEnd(), D(2));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Apply(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Member(Formula x, Formula set) => Seq(x, Sp, InMacro, Sp, set);
    private static Formula Bound(Formula variable) => Seq(variable, Colon, Sp, Naturals());
    private static Formula Parameters(params string[] names) =>
        Seq(Forall, Sp, Joined(names.Select(F.Id).ToArray()), Colon, Sp, Naturals(), Comma);
    private static Formula ListLiteral(params Formula[] values) => Seq(OpenBracket, Joined(values), CloseBracket);
    private static Formula Joined(Formula[] values)
    {
        var items = new List<Formula>();
        foreach (var value in values)
        {
            if (items.Count > 0) items.AddRange([Comma, Sp]);
            items.Add(value);
        }
        return Seq([.. items]);
    }
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Subtract(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
}

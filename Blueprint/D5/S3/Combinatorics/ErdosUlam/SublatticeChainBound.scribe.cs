using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.ErdosUlam;

internal sealed class SublatticeChainBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ErdosUlam/SublatticeChainBound.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "In every odd dimension at least eleven, one more member than the chain guarantee is unavoidable. "
            + "A balanced binary rank word of even length at least twelve has either three "
            + "equally spaced consecutive occurrences of one colour or a balanced interval of length twelve. "
            + "Balanced colourings of twelve ranks admit a seven-member monochromatic sublattice.",
        H("The odd-dimensional improvement"),
        Blocks(
            Node("consecutive-ap", "Equally spaced consecutive occurrences", "ConsecutiveAP",
                APFormula(),
                "The ranks a, b, c have one colour and equal positive gaps. Every rank "
                    + "strictly between a and b or between b and c has the other colour.",
                DescribeRole.Definition),
            Node("balanced-window", "Balanced interval of length twelve", "BalancedWindow",
                WindowFormula(),
                "The interval beginning at b contains six true ranks and six false ranks.",
                DescribeRole.Definition),
            Node("rank-word-alternative", "The balanced rank-word alternative", "rank_word_lemma",
                LemmaFormula(),
                "An equally spaced consecutive triple is present in each of the local words "
                    + "000, 111, 01010, 10101, 0110110 and 1001001. Extend a word one letter "
                    + "at a time, excluding those suffixes and balanced suffixes of length twelve. "
                    + "The resulting collection is empty at length fifteen. At length fourteen "
                    + "none of its words has seven letters of each colour. A balanced word "
                    + "of length twelve is already the required interval. These three cases "
                    + "cover every even length at least twelve.",
                DescribeRole.Theorem),
            Node("balanced-base", "Balanced rank colourings", "balanced_rank_base", BaseFormula(),
                "Of the 924 balanced rank patterns, 874 contain three consecutive occurrences of one colour in arithmetic progression. The corresponding diamond augments the six same-colour prefixes. Each of the remaining fifty patterns is covered by one of ten bitmask families closed under union and intersection, with seven or eight distinct members.", DescribeRole.Theorem),
            Node("extremal-function", "Guaranteed size", "f", ExtremalFormula(),
                "Minimize over all colourings the largest cardinality of a monochromatic sublattice.", DescribeRole.Definition),
            Node("ceiling-formula", "Proposed formula", "claim", ClaimFormula(),
                "The proposed equality is asserted in every natural dimension.", DescribeRole.Definition),
            Node("odd-bound", "The odd-dimensional lower bound", "odd_lower_bound", OddBoundFormula(),
                "If every monochromatic sublattice had at most half the number of ranks, equal-size subsets would have equal colour and both rank colours would be balanced. A consecutive arithmetic progression adds a diamond member. Otherwise a balanced twelve-rank interval admits a seven-member sublattice; embedding it and adjoining the same-colour prefixes outside the interval again adds one member.", DescribeRole.Theorem),
            Node("refutation", "The formula is false", "result", Disp(new Formula.Not(F.Id("claim"))),
                "At dimension eleven the lower bound is seven, whereas the proposed formula gives six. The separate linear-growth question remains open.", DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("bhattacharjee-mandal-bhattacharya-2026-sublattice-chain-bound-refutation"), ResolutionKind.Refuted))), []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Bool() => new Formula.NamedConstant(FormulaIdentifier.Create("Bool"));
    private static Formula Sets(Formula n) => Call("Finset", Call("Fin", n));
    private static Formula Families(Formula n) => Call("Finset", Sets(n));
    private static Formula Colourings(Formula n) => new Formula.TypeArrow(Sets(n), Bool());
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Ex(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Eqn(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);



    private static Formula ExtremalFormula()
    {
        var n = F.Id("n"); var chi = F.Id("chi"); var l = F.Id("L");
        var minimum = new Formula.Subscript(Min, Seq(chi, Colon, Sp, Colourings(n)));
        var maximum = new Formula.Subscript(Max, Seq(l, Colon, Sp, Families(n), Comma, Sp,
            Call("IsSublattice", l), Sp, Land, Sp, Call("Monochromatic", chi, l)));
        return Disp(All("n", Nat(), Eqn(Call("f", n), Seq(minimum, Sp, maximum, Sp, Call("card", l)))));
    }

    private static Formula ClaimFormula()
    {
        var n = F.Id("n");
        var value = new Formula.Floor(new Formula.Fraction(
            new Formula.Binary(n, FormulaBinaryOperator.Add, D(2)), D(2)));
        return Disp(Iff(F.Id("claim"), All("n", Nat(), Eqn(Call("f", n), value))));
    }

    private static Formula OddBoundFormula()
    {
        var n = F.Id("n");
        var bound = new Formula.Floor(new Formula.Fraction(new Formula.Binary(n, FormulaBinaryOperator.Add, D(3)), D(2)));
        return Disp(All("n", Nat(), Imp(Leq(D(1,1), n), Imp(Call("Odd", n), Leq(bound, Call("f", n))))));
    }

    private static Formula Word() => new Formula.TypeArrow(Nat(), Bool());
    private static Formula Lt(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Add(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Add, y);

    private static Formula APFormula()
    {
        var g = F.Id("g"); var n = F.Id("n"); var a = F.Id("a");
        var b = F.Id("b"); var c = F.Id("c"); var r = F.Id("r");
        var left = All("r", Nat(), Imp(And(Lt(a, r), Lt(r, b)),
            new Formula.Not(Eqn(Call("g", r), Call("g", b)))));
        var right = All("r", Nat(), Imp(And(Lt(b, r), Lt(r, c)),
            new Formula.Not(Eqn(Call("g", r), Call("g", b)))));
        var body = And(Lt(a, b), And(Lt(b, c), And(Leq(c, n),
            And(Eqn(Add(a, c), Call("mul", D(2), b)), And(Eqn(Call("g", a), Call("g", b)),
            And(Eqn(Call("g", b), Call("g", c)), And(left, right)))))));
        return Disp(All("g", Word(), All("n", Nat(),
            Iff(Call("ConsecutiveAP", g, n), Ex("a", Nat(),
                Ex("b", Nat(), Ex("c", Nat(), body)))))));
    }

    private static Formula Count(Formula g, Formula b, Formula length) =>
        Call("card", Call("filter", Call("range", length),
            Call("trueAtOffset", g, b)));

    private static Formula WindowFormula()
    {
        var g = F.Id("g"); var b = F.Id("b");
        return Disp(All("g", Word(), All("b", Nat(), Iff(Call("BalancedWindow", g, b),
            Eqn(Count(g, b, D(1,2)), D(6))))));
    }

    private static Formula LemmaFormula()
    {
        var g = F.Id("g"); var n = F.Id("n"); var b = F.Id("b");
        var balance = Eqn(Count(g, D(0), Add(n, D(1))),
            Call("div", Add(n, D(1)), D(2)));
        var alternative = new Formula.Logic(Call("ConsecutiveAP", g, n), FormulaLogicOperator.Or,
            Ex("b", Nat(), And(Leq(Add(b, D(1,1)), n), Call("BalancedWindow", g, b))));
        return Disp(All("g", Word(), All("n", Nat(),
            Imp(And(Leq(D(1,1), n), And(Call("Odd", n), balance)), alternative))));
    }

    private static Formula BaseFormula()
    {
        var g = F.Id("g"); var l = F.Id("L");
        var balanced = Eqn(Call("card", Call("filter", Call("trueRanks", g), Call("range", D(1,2)))), D(6));
        var mono = Call("Monochromatic", Call("rankColouring", g), l);
        return Disp(All("g", new Formula.TypeArrow(Nat(), Bool()), Imp(balanced,
            Ex("L", Families(D(1,1)), And(Call("IsSublattice", l), And(mono, Leq(D(7), Call("card", l))))))));
    }
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Interpolation;

internal sealed class SelfConjugateGridSchurRatioRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Interpolation/SelfConjugateGridSchurRatioRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Analytic/ostrovskii2025amplitude");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A self-conjugate pair in the closed unit disk violates the shifted Schur-ratio bound in Conjecture 6.2 of Ostrovskii and Shcherbakov. The tableau definition gives the ratio 73/60 at t = 3, n = 2, k = 1.",
        H("A self-conjugate grid with Schur ratio above one"),
        Blocks(
            Node("self-conjugate", "Self-conjugate grids", SelfConjugateFormula(),
                "Entries are indexed by Fin n, starting at zero. The first condition requires membership of each nonreal conjugate; the second counts every real value, including absent values. ofReal is the embedding from R into C.",
                "selfConjugate", DescribeRole.Definition, true, SelfConjugateQuote()),
            Node("elementary", "Elementary symmetric functions", ElementaryFormula(),
                "Equation (17), page 7, defines e_d as the sum of products over strictly increasing index tuples, with e_0 = 1. A tuple is represented by its d-element subset of Fin n. univ(Fin n) is the finite set of all indices, and powersetCard(U,d) consists of the d-element subsets of U.",
                "e", DescribeRole.Definition, true),
            Node("homogeneous", "Complete homogeneous symmetric functions", HomogeneousFormula(),
                "Equation (17), page 7, defines h_d as the sum of products over weakly increasing index tuples, with h_0 = 1. Sym(Fin n,d) is the type of multisets of cardinality d. Sorting in the ordered alphabet Fin n identifies each multiset with exactly one such tuple, including repeated indices. val extracts the multiset; map applies z to every occurrence; prod multiplies with multiplicity.",
                "h", DescribeRole.Definition, true),
            Node("hook", "Hook Schur functions by tableaux", HookFormula(),
                "Equation (19) defines the Schur function by its Kostka expansion. For the hook (a+1,1^b), c is the corner, A is the arm multiset of cardinality a, and L is the leg set of cardinality b. Sorting A gives the weakly increasing arm; sorting L gives the strictly increasing leg. All arm entries are at least c, and all leg entries exceed c. Fin n relabels the source entries 1,...,n by 0,...,n-1. Grouping tableau monomials by weights and then permuted weights recovers the Kostka expansion. Each tableau occurs once. ite(P,u,v) is u when P holds and v otherwise.",
                "schurHook", DescribeRole.Definition, true, HookQuote()),
            Node("ratio", "The alternating Schur ratio", RatioFormula(),
                "The defining alternating sum is displayed with every parameter bound. choose(t,r) is the natural binomial coefficient. Nat.cast gives the typed natural-to-complex coercions. Natural subtraction is truncated at zero. Fractions here are complex field division; Lean assigns value zero to division by zero. The counterexample denominator is 3/5, so this convention has no effect on the refutation.",
                "Q", DescribeRole.Definition, true, RatioQuote()),
            Node("claim", "Both clauses of Conjecture 6.2", ClaimFormula(),
                "Natural k encodes 0 <= k. The complex norm is the absolute value; the disk is closed; the nonnegative orthant includes zero. The pointwise numeral 1 is added to z. The implication for nonnegative real parts belongs to the second conjunct only. All natural subtractions are truncated, in the source range k < n <= t.",
                "claim", DescribeRole.Definition, true, ClaimQuote()),
            Node("result", "Refutation by a conjugate pair", Disp(new Formula.Not(F.Id("claim"))),
                "Take z = (-9/10 + (2/5)i, -9/10 - (2/5)i). Each entry has squared norm 97/100; the entries are nonreal conjugates, so each real multiplicity is zero. For w = z plus the pointwise numeral 1 on Fin 2, the finite sums give e_1(w) = 1/5, schurHook(0,0,w) = 1/5 and schurHook(1,0,w) = -13/100. Hence Q(3,2,1,w) = 73/60, whose norm exceeds one. The first conjunct fails, refuting the whole universal conjunction.",
                "result", DescribeRole.Theorem, false, null,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("ostrovskii-shcherbakov-conjecture-62-refutation"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, bool literature, DocumentBlock? quote = null,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("self-conjugate-schur-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            quote is null ? Blocks(Paragraph(Text(prose))) : Blocks(quote, Paragraph(Text(prose))), role,
            resolution);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] arguments)
    {
        var parts = new List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (parts.Count > 0) parts.Add(Dot);
            parts.Add(F.Id(part));
        }
        return new Formula.Apply(Seq(Operatorname, Grp([.. parts])), [.. arguments]);
    }
    private static Formula All(Formula variable, Formula domain, Formula body) =>
        Seq(Forall, Sp, variable, Colon, Sp, domain, Comma, Sp, body);
    private static Formula Some(Formula variable, Formula domain, Formula body) =>
        Seq(Exists, Sp, variable, Colon, Sp, domain, Comma, Sp, body);
    private static Formula Rel(Formula x, FormulaRelationOperator op, Formula y) =>
        new Formula.Relation(x, op, y);
    private static Formula Eqn(Formula x, Formula y) => Rel(x, FormulaRelationOperator.Equal, y);
    private static Formula LeqTo(Formula x, Formula y) => Rel(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Less(Formula x, Formula y) => Rel(x, FormulaRelationOperator.LessThan, y);
    private static Formula And(Formula x, Formula y) =>
        new Formula.Logic(Parenthesized(x), FormulaLogicOperator.And, Parenthesized(y));
    private static Formula Imp(Formula x, Formula y) =>
        new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Implies, Parenthesized(y));
    private static Formula IffTo(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.Iff, Parenthesized(y));
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Type(string letter) => Seq(Mathbb, Grp(F.Id(letter)));
    private static Formula FinOf(Formula n) => Call("Fin", n);
    private static Formula Family(Formula n) => new Formula.TypeArrow(FinOf(n), Type("C"));
    private static Formula At(Formula f, Formula i) => new Formula.Apply(f, [i]);
    private static Formula SymOf(Formula n, Formula d) => Call("Sym", FinOf(n), d);
    private static Formula Subsets(Formula n, Formula d) => Call("powersetCard", Call("univ", FinOf(n)), d);
    private static Formula InSet(Formula i, Formula s) => Rel(i, FormulaRelationOperator.MemberOf, s);
    private static Formula SumTyped(Formula i, Formula domain, Formula body) =>
        Seq(Sum, Underscore, Grp(i, Colon, domain), Sp, body);
    private static Formula SumIn(Formula i, Formula set, Formula body) =>
        Seq(Sum, Underscore, Grp(i, InMacro, Sp, set), Sp, body);
    private static Formula ProdIn(Formula i, Formula set, Formula body) =>
        Seq(Prod, Underscore, Grp(i, InMacro, Sp, set), Sp, body);
    private static Formula Choose(Formula t, Formula n) => Call("choose", t, n);

    private static Formula SourceGrid() => new Formula.Subscript(F.Id("z"), Seq(D(1), Colon, F.Id("n")));
    private static Formula SourceOnes() => new Formula.Subscript(D(1), F.Id("n"));
    private static Formula SourceRatio() => new Formula.Subscript(F.Id("Q"),
        Seq(F.Id("t"), Comma, F.Id("n"), Comma, F.Id("k")));

    private static DocumentBlock SelfConjugateQuote()
    {
        Formula n = F.Id("n"), z = F.Id("z");
        Formula entries = new Formula.SetLiteral([
            new Formula.Subscript(z, D(1)), Seq(Dot, Dot, Dot), new Formula.Subscript(z, n)]);
        return Paragraph(Text("Definition 6.1, page 15: “A list "),
            Math(InSet(SourceGrid(), new Formula.Power(Type("C"), n))),
            Text(" is self-conjugate if (i) for any "), Math(InSet(z, entries)),
            Text(" with "), Math(Rel(Call("Im", z), FormulaRelationOperator.NotEqual, D(0))),
            Text(", the conjugate "), Math(Seq(Overline, Grp(z))),
            Text(" is also contained in "), Math(entries), Text("; (ii) "), Math(SourceGrid()),
            Text(" contains even number of copies of each "), Math(InSet(z, Type("R"))), Text(".”"));
    }

    private static DocumentBlock HookQuote()
    {
        Formula lambda = LambdaLower;
        return Paragraph(Text("Page 8: “A semi-standard Young tableau (SSYT) with shape "),
            Math(InSet(lambda, Seq(Operatorname, Grp(F.Id("Par"))))),
            Text(" is a two-dimensional array "), Math(F.Id("T")),
            Text(" that fills the cells of the Young diagram of "), Math(lambda),
            Text(" with positive integers, such that the entries (a) srtictly increase in each column; (b) do not decrease in each row.”"));
    }

    private static DocumentBlock RatioQuote() => Paragraph(
        Text("Page 13: “Let us define the rational multivariate function "),
        Math(Seq(SourceRatio(), Colon, new Formula.TypeArrow(
            new Formula.Power(Type("C"), F.Id("n")), Type("C")))),
        Text(", symmetric in its arguments, by” the displayed alternating sum."));

    private static DocumentBlock ClaimQuote()
    {
        Formula n = F.Id("n"), t = F.Id("t"), k = F.Id("k"), grid = SourceGrid();
        Formula hook = Parenthesized(Seq(Sub(t, n), Sp, Mid, Sp, Sub(Sub(n, k), D(1))));
        Formula schur = At(new Formula.Subscript(F.Id("s"), hook), grid);
        Formula elementary = At(new Formula.Subscript(F.Id("e"), Sub(n, k)), grid);
        Formula binomial = Parenthesized(new Formula.Aligned([t, n]));
        return Paragraph(Text("Conjecture 6.2 (Equivalent to Conjecture 6.1), page 15: “For all "),
            Math(Seq(D(0), Sp, Le, Sp, k, Sp, Lt, Sp, n, Sp, Le, Sp, t)), Text(" and self-conjugate "),
            Math(InSet(grid, new Formula.Power(Type("D"), n))), Text(", "),
            Math(LeqTo(new Formula.Absolute(At(SourceRatio(), Add(grid, SourceOnes()))), D(1))),
            Text(". Moreover, if the grid additionally satisfies "),
            Math(InSet(Call("Re", grid), new Formula.Subscript(new Formula.Power(Type("R"), n), Plus))),
            Text(", then "), Math(LeqTo(new Formula.Absolute(schur),
                Mul(binomial, new Formula.Absolute(elementary)))), Text(".”"));
    }

    private static Formula SelfConjugateFormula()
    {
        Formula n = F.Id("n"), z = F.Id("z"), i = F.Id("i"), j = F.Id("j"), x = F.Id("x");
        Formula conjugate = All(i, FinOf(n), Imp(
            Rel(Call("Im", At(z, i)), FormulaRelationOperator.NotEqual, D(0)),
            Some(j, FinOf(n), Eqn(At(z, j), Call("conj", At(z, i))))));
        Formula realEntries = Seq(OpenBrace, i, Colon, FinOf(n), Sp, Mid, Sp,
            Eqn(At(z, i), Call("ofReal", x)), CloseBrace);
        Formula even = All(x, Type("R"), Call("Even", Call("card", realEntries)));
        return Disp(All(n, Type("N"), All(z, Family(n),
            IffTo(Call("selfConjugate", z), And(conjugate, even)))));
    }

    private static Formula ElementaryFormula()
    {
        Formula n = F.Id("n"), d = F.Id("d"), z = F.Id("z"), s = F.Id("s"), i = F.Id("i");
        return Disp(All(n, Type("N"), All(d, Type("N"), All(z, Family(n),
            Eqn(Call("e", d, z), SumIn(s, Subsets(n, d), ProdIn(i, s, At(z, i))))))));
    }

    private static Formula HomogeneousFormula()
    {
        Formula n = F.Id("n"), d = F.Id("d"), z = F.Id("z"), s = F.Id("s");
        return Disp(All(n, Type("N"), All(d, Type("N"), All(z, Family(n),
            Eqn(Call("h", d, z), SumTyped(s, SymOf(n, d),
                Call("prod", Call("map", z, Call("val", s)))))))));
    }

    private static Formula HookFormula()
    {
        Formula n = F.Id("n"), a = F.Id("a"), b = F.Id("b"), z = F.Id("z");
        Formula c = F.Id("c"), arm = F.Id("A"), leg = F.Id("L"), i = F.Id("i"), j = F.Id("j");
        Formula condition = And(
            All(i, FinOf(n), Imp(InSet(i, Call("val", arm)), LeqTo(c, i))),
            All(j, FinOf(n), Imp(InSet(j, leg), Less(c, j))));
        Formula monomial = Mul(Mul(At(z, c), Call("prod", Call("map", z, Call("val", arm)))),
            ProdIn(j, leg, At(z, j)));
        Formula value = SumTyped(c, FinOf(n), SumTyped(arm, SymOf(n, a),
            SumIn(leg, Subsets(n, b), Call("ite", condition, monomial, D(0)))));
        return Disp(All(n, Type("N"), All(a, Type("N"), All(b, Type("N"), All(z, Family(n),
            Eqn(Call("schurHook", a, b, z), value))))));
    }

    private static Formula RatioFormula()
    {
        Formula t = F.Id("t"), n = F.Id("n"), k = F.Id("k"), zeta = Zeta, d = F.Id("d");
        Formula b = Sub(Sub(n, k), D(1));
        Formula numerator = Mul(Call("Nat.cast", Type("C"), Choose(t, Add(n, d))), Call("schurHook", d, b, zeta));
        Formula denominator = Mul(Call("Nat.cast", Type("C"), Choose(t, n)), Call("e", Sub(n, k), zeta));
        Formula term = Mul(new Formula.Power(Parenthesized(new Formula.Negate(D(1))), d),
            new Formula.Fraction(numerator, denominator));
        Formula value = Seq(Sum, Underscore, Grp(d, F.Eq, D(0)), Caret, Grp(Sub(t, n)), Sp, term);
        return Disp(All(t, Type("N"), All(n, Type("N"), All(k, Type("N"), All(zeta, Family(n),
            Eqn(Call("Q", t, n, k, zeta), value))))));
    }

    private static Formula ClaimFormula()
    {
        Formula k = F.Id("k"), n = F.Id("n"), t = F.Id("t"), z = F.Id("z"), i = F.Id("i");
        Formula disk = All(i, FinOf(n), LeqTo(new Formula.Norm(At(z, i)), D(1)));
        Formula first = LeqTo(new Formula.Norm(Call("Q", t, n, k,
            Parenthesized(Add(z, D(1))))), D(1));
        Formula nonnegative = All(i, FinOf(n), LeqTo(D(0), Call("Re", At(z, i))));
        Formula second = Imp(nonnegative, LeqTo(new Formula.Norm(
            Call("schurHook", Sub(t, n), Sub(Sub(n, k), D(1)), z)),
            Mul(Call("Nat.cast", Type("R"), Choose(t, n)), new Formula.Norm(Call("e", Sub(n, k), z)))));
        Formula body = All(k, Type("N"), All(n, Type("N"), All(t, Type("N"),
            Imp(Less(k, n), Imp(LeqTo(n, t), All(z, Family(n),
                Imp(Call("selfConjugate", z), Imp(disk, And(first, second)))))))));
        return Disp(IffTo(F.Id("claim"), body));
    }
}

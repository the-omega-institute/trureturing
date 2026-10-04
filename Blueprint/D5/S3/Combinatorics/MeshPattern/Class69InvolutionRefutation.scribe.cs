using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MeshPattern;

internal sealed class Class69InvolutionRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MeshPattern/Class69InvolutionRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/fangfukitaevlisusun2026mesh");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The four Class 69 length-2 mesh patterns fail equidistribution on involutions at length three.",
        H("Class 69 Mesh Patterns Are Not Equidistributed on Involutions"),
        Blocks(
            Node("class69-r", "The four Class 69 shaded-cell sets", "R", RFormula(),
                "The function R : Fin 4 → Finset (Nat × Nat) assigns the four shaded-cell sets in the source order. The source macro \\pattern{scale=0.5}{2}{1/1,2/2}{x/y,...} shades the unit box with lower-left corner (x,y) for each listed x/y; its dots are at (1,1) and (2,2).",
                DescribeRole.Definition),
            Node("class69-box", "The relative box", "box", BoxFormula(),
                "For two selected positions i and j and a third position r, box records the number of selected positions below r and the number of their values below the value at r.",
                DescribeRole.Definition),
            Node("class69-occurrence", "A length-2 mesh occurrence", "IsOccurrence", IsOccurrenceFormula(),
                "A pair is an occurrence when its positions and values are increasing and every other position has its relative box outside the selected shaded set.",
                DescribeRole.Definition),
            Node("class69-occ", "The occurrence count", "occ", OccFormula(),
                "The occurrence count is the cardinality of the filtered Cartesian product of all pairs of positions.",
                DescribeRole.Definition),
            Node("class69-claim", "Conjecture 1", "claim", ClaimFormula(),
                "Fang, Fu, Kitaev, Li, Su and Sun write: \"The patterns in the set {\\pattern{scale=0.5}{2}{1/1,2/2}{1/2,1/1,2/1,0/0},\\pattern{scale=0.5}{2}{1/1,2/2}{2/2,0/1,1/1,1/0},\\pattern{scale=0.5}{2}{1/1,2/2}{0/2,1/1,2/1,1/0},\\pattern{scale=0.5}{2}{1/1,2/2}{1/2,0/1,1/1,2/0}} are equidistributed on involutions. (The first two patterns, as well as the last two patterns, are trivially equidistributed via the composition of reverse and complement.)\" (Conjecture 1, arXiv:2606.14367v1, Concluding remarks). The displayed formula encodes involutions as σ * σ = 1 and counts exactly k occurrences for every n and every pair of pattern indices.",
                DescribeRole.Definition),
            Node("class69-result", "The conjecture is refuted", "result", ResultFormula(),
                "At n = 3 and k = 0, the involutions 132 and 321 avoid R 0 while only 321 avoids R 2. The two filtered cardinalities are therefore 2 and 1, contradicting equidistribution.",
                DescribeRole.Theorem, repositoryDerived: true)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, DescribeRole role, bool repositoryDerived = false) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula),
            repositoryDerived ? AssessedProvenance.FromRepo(Source) : AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula RFormula()
    {
        var s0 = SetOf(Pair(D(1), D(2)), Pair(D(1), D(1)), Pair(D(2), D(1)), Pair(D(0), D(0)));
        var s1 = SetOf(Pair(D(2), D(2)), Pair(D(0), D(1)), Pair(D(1), D(1)), Pair(D(1), D(0)));
        var s2 = SetOf(Pair(D(0), D(2)), Pair(D(1), D(1)), Pair(D(2), D(1)), Pair(D(1), D(0)));
        var s3 = SetOf(Pair(D(1), D(2)), Pair(D(0), D(1)), Pair(D(1), D(1)), Pair(D(2), D(0)));
        return Disp(All("a", Fin(D(4)), Eq(Call("R", F.Id("a")),
            Ite(Eq(Call("val", F.Id("a")), D(0)), s0,
                Ite(Eq(Call("val", F.Id("a")), D(1)), s1,
                    Ite(Eq(Call("val", F.Id("a")), D(2)), s2, s3))))));
    }

    private static Formula BoxFormula()
    {
        var n = F.Id("n");
        var sigma = F.Id("s");
        var i = F.Id("i");
        var j = F.Id("j");
        var r = F.Id("r");
        var first = Add(Ite(Lt(i, r), D(1), D(0)), Ite(Lt(j, r), D(1), D(0)));
        var second = Add(Ite(Lt(Apply(sigma, i), Apply(sigma, r)), D(1), D(0)),
            Ite(Lt(Apply(sigma, j), Apply(sigma, r)), D(1), D(0)));
        return Disp(All("n", Naturals(), All("s", Apply(Seq(F.Id("Equiv"), Dot, F.Id("Perm")), Fin(n)),
            All("i", Fin(n), All("j", Fin(n), All("r", Fin(n),
                new Formula.Relation(Call("box", sigma, i, j, r), FormulaRelationOperator.Equal,
                    Pair(first, second))))))));
    }

    private static Formula IsOccurrenceFormula()
    {
        var n = F.Id("n");
        var Rv = F.Id("R");
        var sigma = F.Id("s");
        var i = F.Id("i");
        var j = F.Id("j");
        var r = F.Id("r");
        var body = And(Lt(i, j), And(Lt(Apply(sigma, i), Apply(sigma, j)),
            All("r", Fin(n), Implies(NotEqual(r, i),
                Implies(NotEqual(r, j), Not(In(Call("box", sigma, i, j, r), Rv)))))));
        return Disp(All("n", Naturals(), All("R", Call("Finset", PairType(Naturals(), Naturals())),
            All("s", Apply(Seq(F.Id("Equiv"), Dot, F.Id("Perm")), Fin(n)), All("i", Fin(n), All("j", Fin(n),
                Iff(Call("IsOccurrence", Rv, sigma, i, j), body)))))));
    }

    private static Formula OccFormula()
    {
        var n = F.Id("n");
        var Rv = F.Id("R");
        var sigma = F.Id("s");
        var p = F.Id("p");
        var domain = Product(Apply(Seq(F.Id("Finset"), Dot, F.Id("univ")), Fin(n)), Apply(Seq(F.Id("Finset"), Dot, F.Id("univ")), Fin(n)));
        var predicate = Lambda(p, Call("IsOccurrence", Rv, sigma, Call("fst", p), Call("snd", p)));
        return Disp(All("n", Naturals(), All("R", Call("Finset", PairType(Naturals(), Naturals())),
            All("s", Apply(Seq(F.Id("Equiv"), Dot, F.Id("Perm")), Fin(n)),
                Eq(Call("occ", Rv, sigma), Apply(Seq(F.Id("Finset"), Dot, F.Id("card")), Apply(Seq(F.Id("Finset"), Dot, F.Id("filter")), predicate, domain)))))));
    }

    private static Formula ClaimFormula()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var a = F.Id("a");
        var b = F.Id("b");
        var sigma = F.Id("s");
        var perm = Apply(Seq(F.Id("Equiv"), Dot, F.Id("Perm")), Fin(n));
        var involution = Eq(Mul(sigma, sigma), D(1));
        var left = Apply(Seq(F.Id("Finset"), Dot, F.Id("card")), Apply(Seq(F.Id("Finset"), Dot, F.Id("filter")), Lambda(sigma,
            And(involution, Eq(Call("occ", Call("R", a), sigma), k))), Apply(Seq(F.Id("Finset"), Dot, F.Id("univ")), perm)));
        var right = Apply(Seq(F.Id("Finset"), Dot, F.Id("card")), Apply(Seq(F.Id("Finset"), Dot, F.Id("filter")), Lambda(sigma,
            And(involution, Eq(Call("occ", Call("R", b), sigma), k))), Apply(Seq(F.Id("Finset"), Dot, F.Id("univ")), perm)));
        var quantified = All("n", Naturals(), All("k", Naturals(), All("a", Fin(D(4)),
            All("b", Fin(D(4)), Eq(left, right)))));
        return Disp(Iff(Call("claim"), quantified));
    }

    private static Formula ResultFormula() => Disp(new Formula.Not(F.Id("claim")));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Fin(Formula n) => Call("Fin", n);

    private static Formula PairType(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Times, Sp, Parenthesized(b));

    private static Formula SetOf(params Formula[] entries)
    {
        var items = new List<Formula> { OpenBrace };
        for (var i = 0; i < entries.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(entries[i]);
        }
        items.Add(CloseBrace);
        return Seq([.. items]);
    }

    private static Formula Pair(Formula left, Formula right) => Parenthesized(Seq(left, Comma, Sp, right));

    private static Formula Product(Formula left, Formula right) => Seq(left, Sp, Times, Sp, right);

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Lambda(Formula variable, Formula body) => Parenthesized(Seq(variable, Sp, Mapsto, Sp, body));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Ite(Formula condition, Formula yes, Formula no) =>
        Call("ite", condition, yes, no);

    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Eq(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Lt(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula NotEqual(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula In(Formula left, Formula right) => Call("mem", left, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Not(Formula value) => new Formula.Not(value);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class LatinEulerianFormulaDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/LatinEulerianFormula.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/mirzavaziri2026latin");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A cyclicly shifted Latin square has an ascent total controlled by row ascents, endpoints, and unit cyclic steps.",
        H("The Shifted-Square Ascent Formula"),
        Blocks(
            Node("swap-fin", "Symbol transposition", "swapFin", SwapFinFormula(),
                "For an order at least two, swapFin is the permutation exchanging the symbols zero and one.",
                DescribeRole.Definition),
            Node("shifted-square", "Shifted Latin square", "shiftedSquare", ShiftedSquareFormula(),
                "The shifted square adds a column index to the row permutation and then applies the symbol transposition.",
                DescribeRole.Definition),
            Node("shifted-pair-count", "Shifted pair count", "shifted_pair_count", PairCountFormula(),
                "For distinct row symbols, the swapped cyclic comparison count is n minus their cyclic difference, with the two endpoint corrections.",
                DescribeRole.Theorem),
            Node("row-at", "Cyclic row entry", "rowAt", RowAtFormula(),
                "Read the permutation at a natural index reduced modulo the order.",
                DescribeRole.Definition),
            Node("row-delta", "Cyclic row difference", "rowDelta", RowDeltaFormula(),
                "The cyclic difference is the next row entry minus the current row entry in Fin n.",
                DescribeRole.Definition),
            Node("ordinary-ascents", "Ordinary row ascents", "ordinaryAscents", OrdinaryAscentsFormula(),
                "Count increasing adjacent entries of the row permutation over the noncyclic indices.",
                DescribeRole.Definition),
            Node("forward-units", "Forward unit steps", "forwardUnits", ForwardUnitsFormula(),
                "Count cyclic differences whose Fin representative is one.",
                DescribeRole.Definition),
            Node("backward-units", "Backward unit steps", "backwardUnits", BackwardUnitsFormula(),
                "Count cyclic differences whose Fin representative is n minus one.",
                DescribeRole.Definition),
            Node("shifted-square-formula", "Shifted-square ascent identity", "shiftedSquare_formula",
                MainFormula(),
                "The total ascent count equals n times the ordinary row ascents, plus the endpoint difference, minus forward unit steps, plus backward unit steps.",
                DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Perm(Formula n) => Call("EquivPerm", Fin(n));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula And(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Ne(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Card(Formula value) => Call("card", value);

    private static Formula SwapFinFormula()
    {
        var n = F.Id("n"); var h = F.Id("h");
        return Disp(All("n", Nat(), All("h", Call("Prop"),
            Eq(Call("swapFin", n, h), Call("swap", D(0), D(1))))));
    }

    private static Formula ShiftedSquareFormula()
    {
        var n = F.Id("n"); var h = F.Id("h"); var p = F.Id("p");
        var i = F.Id("i"); var c = F.Id("c");
        var body = Eq(Call("shiftedSquare", n, h, p, i, c),
            Call("swapFin", n, h, Add(Call("p", i), c)));
        return Disp(All("n", Nat(), All("h", Call("Prop"), All("p", Perm(n),
            All("i", Fin(n), All("c", Fin(n), body))))));
    }

    private static Formula PairCountFormula()
    {
        var n = F.Id("n"); var h = F.Id("h"); var a = F.Id("a"); var b = F.Id("b");
        var d = Call("sub", b, a); var c = F.Id("c");
        var set = Seq(OpenBrace, c, Sp, InMacro, Sp, Fin(n), Bar, Sp,
            Lt(Call("swapFin", n, h, Add(a, c)),
                Call("swapFin", n, h, Add(b, c))), CloseBrace);
        var lhs = Add(Card(set), Call("if", Eq(Call("val", d), D(1)), D(1), D(0)));
        var rhs = Add(Sub(n, Call("val", d)),
            Call("if", Eq(Call("val", d), Sub(n, D(1))), D(1), D(0)));
        var hyp = And(Le(D(3), n), And(Le(D(2), n), Ne(a, b)));
        return Disp(All("n", Nat(), All("h", Call("Prop"), All("a", Fin(n), All("b", Fin(n),
            Imp(hyp, Eq(lhs, rhs)))))));
    }

    private static Formula RowAtFormula()
    {
        var n = F.Id("n"); var h = F.Id("h"); var p = F.Id("p"); var j = F.Id("j");
        var value = Call("p", Call("fin", Call("mod", j, n), n));
        return Disp(All("n", Nat(), All("h", Call("Prop"), All("p", Perm(n),
            All("j", Nat(), Eq(Call("rowAt", h, p, j), value))))));
    }

    private static Formula RowDeltaFormula()
    {
        var n = F.Id("n"); var h = F.Id("h"); var p = F.Id("p"); var j = F.Id("j");
        return Disp(All("n", Nat(), All("h", Call("Prop"), All("p", Perm(n), All("j", Nat(),
            Eq(Call("rowDelta", h, p, j),
                Sub(Call("rowAt", h, p, Add(j, D(1))), Call("rowAt", h, p, j))))))));
    }

    private static Formula OrdinaryAscentsFormula() =>
        StatisticFormula("ordinaryAscents", "lt", D(1));
    private static Formula ForwardUnitsFormula() =>
        StatisticFormula("forwardUnits", "forward", D(1));
    private static Formula BackwardUnitsFormula() =>
        StatisticFormula("backwardUnits", "backward", D(1));

    private static Formula StatisticFormula(string name, string predicate, Formula value)
    {
        var n = F.Id("n"); var h = F.Id("h"); var p = F.Id("p"); var j = F.Id("j");
        var condition = predicate == "lt"
            ? Lt(Call("rowAt", h, p, j), Call("rowAt", h, p, Add(j, D(1))))
            : Eq(Call("val", Call("rowDelta", h, p, j)),
                predicate == "forward" ? value : Sub(n, D(1)));
        var summand = Call("if", condition, D(1), D(0));
        var sum = Seq(Sum, Sp, j, Sp, InMacro, Sp, Call("range", Sub(n, D(1))), Sp, summand);
        return Disp(All("n", Nat(), All("h", Call("Prop"), All("p", Perm(n),
            Eq(Call(name, h, p), sum)))));
    }

    private static Formula MainFormula()
    {
        var n = F.Id("n"); var h = F.Id("h"); var hp = F.Id("hp"); var p = F.Id("p");
        var lhs = Call("Int", Call("totalAscents", n, Call("shiftedSquare", n, h, p)));
        var rhs = Add(Mul(n, Call("ordinaryAscents", hp, p)),
            Sub(Call("val", Call("rowAt", hp, p, D(0))),
                Call("val", Call("rowAt", hp, p, Sub(n, D(1))))));
        rhs = Add(Sub(rhs, Call("forwardUnits", hp, p)), Call("backwardUnits", hp, p));
        var hyp = And(Le(D(3), n), And(Le(D(2), n), Lt(D(0), n)));
        var body = Imp(hyp, Eq(lhs, rhs));
        var quantified = All("p", Perm(n), body);
        quantified = All("hp", Call("Prop"), quantified);
        quantified = All("h", Call("Prop"), quantified);
        quantified = All("n", Nat(), quantified);
        return Disp(quantified);
    }
}

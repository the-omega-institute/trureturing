using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Games;

internal sealed class DivisorNimBoundArithmeticDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Games/DivisorNimBoundArithmetic.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A divisor-sensitive integer recurrence bounds the values associated with a distinguished heap.",
        H("Distinguished-Heap Recurrence Estimates"),
        Blocks(
            Node("coarseBound", "Coarse ceiling", CoarseFormula(),
                "The coarse ceiling adds the quotients by successive powers of two and one unit for each depth.", DescribeRole.Definition),
            Node("oddDivisorCount", "Divisor count", DivisorFormula(),
                "The divisor count is the cardinality of the positive-divisor set.", DescribeRole.Definition),
            Node("changedBound", "Changed reference heap", ChangedFormula(),
                "The changed-reference ceiling accounts for the subtraction of a removal of lower valuation.", DescribeRole.Definition),
            Node("exceptionalCount", "Exceptional removals", ExceptionalFormula(),
                "Below the distinguished valuation the divisor count controls exceptional removals; at that valuation the odd part controls them.", DescribeRole.Definition),
            Node("recurrenceBound", "Distinguished-heap recurrence", RecurrenceFormula(),
                "At each depth take the largest previous ceiling and add the exceptional-removal count and one. A supremum over an empty set of natural numbers is zero.", DescribeRole.Definition),
            Node("bound", "Terminal recurrence ceiling", BoundFormula(),
                "The terminal ceiling is the recurrence evaluated at the distinguished valuation.", DescribeRole.Definition),
            Node("recurrenceBound_mono", "Increasing depth ceiling", MonotoneFormula(),
                "Each recurrence step contains its predecessor in the maximum and adds nonnegative quantities.", DescribeRole.Theorem),
            Node("oddDivisorCount_le", "Divisor count ceiling", DivisorBoundFormula(),
                "Every positive divisor of u lies in the interval from one through u.", DescribeRole.Theorem),
            Node("finite_bound", "Finite valuation range", FiniteFormula(),
                "For valuations one through fifteen and positive odd parts at most the valuation, the ceiling is at most twice the heap, apart from the three odd-part-one exceptions.", DescribeRole.Theorem),
            Node("triangle", "Triangular budget", TriangleFormula(),
                "The triangular budget sums the coefficients of the exceptional-removal counts.", DescribeRole.Definition),
            Node("triangle_twice", "Doubled triangular budget", TriangleTwiceFormula(),
                "The product of two consecutive natural numbers is even.", DescribeRole.Theorem),
            Node("large_exponential_square", "Exponential square estimate", SquareFormula(),
                "After translating the valuation by sixteen, the consecutive-value comparison becomes a polynomial with nonnegative coefficients. Induction compares it with the doubling exponential.", DescribeRole.Theorem),
            Node("large_exponential_linear", "Exponential linear estimate", LinearFormula(),
                "The same consecutive-value comparison bounds the quadratic budget by the doubling exponential.", DescribeRole.Theorem),
            Node("recurrence_le_budget", "Unrolled recurrence ceiling", UnrollFormula(),
                "A common ceiling for the initial value and every changed-reference ceiling leaves only the sum of recurrence increments.", DescribeRole.Theorem),
            Node("sum_descending", "Descending coefficient sum", DescendingFormula(),
                "Reflecting the summation interval identifies the descending sum with the triangular budget.", DescribeRole.Theorem),
            Node("total_increment_le", "Total recurrence increments", IncrementFormula(),
                "Bound the divisor count by the odd part and sum the resulting descending coefficients.", DescribeRole.Theorem),
            Node("large_gap", "Lower-valuation gap", GapFormula(),
                "The quotient and power-of-two terms have product twice the heap. The arithmetic mean-geometric mean inequality and the exponential square estimate supply the gap.", DescribeRole.Theorem),
            Node("large_changedBound", "Changed ceiling with budget", ChangedBudgetFormula(),
                "The gap pays for the whole recurrence budget and the lower-valuation additive terms.", DescribeRole.Theorem),
            Node("large_initial", "Initial ceiling with budget", InitialFormula(),
                "The exponential linear estimate pays for the initial divisor count and the entire recurrence budget.", DescribeRole.Theorem),
            Node("large_bound", "All large valuations", LargeFormula(),
                "Unroll the recurrence using the initial and changed-reference ceilings, then spend the triangular budget. Every valuation at least sixteen satisfies the twice-heap bound.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string declaration, string title, Formula formula,
        string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create(declaration.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + declaration), H(title),
        StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), role);

    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Call(string name, params Formula[] xs) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. xs]);
    private static Formula All(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), Nat(), body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Div(Formula a, Formula b) => Call("div", a, b);
    private static Formula SumRange(string name, Formula end, Formula body) =>
        Seq(Sum, Underscore, Grp(F.Id(name), Sp, InMacro, Sp, Call("range", end)), Sp, body);
    private static Formula MaxRange(string name, Formula end, Formula body) =>
        Seq(Max, Underscore, Grp(F.Id(name), Sp, InMacro, Sp, Call("range", end)), Sp, body);
    private static Formula Heap(Formula v, Formula u) => Mul(Pow(D(2), v), u);
    private static Formula TwiceHeap(Formula v, Formula u) => Mul(Mul(D(2), Pow(D(2), v)), u);
    private static Formula Tri(Formula v) => Call("triangle", v);
    private static Formula Rec(Formula v, Formula u, Formula k) => Call("recurrenceBound", v, u, k);
    private static Formula Changed(Formula v, Formula u, Formula j) => Call("changedBound", v, u, j);
    private static Formula IncrementSum(Formula v, Formula u, Formula k) =>
        SumRange("i", k, Add(Call("exceptionalCount", v, u, Add(F.Id("i"), D(1))), D(1)));
    private static Formula Budget(Formula v, Formula u) => Add(Mul(Tri(v), u), v);
    private static Formula LargeConditions(Formula v, Formula u) =>
        And(Le(D(1,6), v), And(Le(D(1), u), Le(u, v)));

    private static Formula CoarseFormula()
    {
        var k = F.Id("k"); var h = F.Id("h"); var j = F.Id("j");
        return Disp(All("k", All("h", Eq(Call("coarseBound", k, h),
            Add(Add(SumRange("j", Add(k, D(1)), Div(h, Pow(D(2), j))), k), D(1))))));
    }
    private static Formula DivisorFormula()
    {
        var u = F.Id("u");
        return Disp(All("u", Eq(Call("oddDivisorCount", u), Call("card", Call("divisors", u)))));
    }
    private static Formula ChangedFormula()
    {
        var v = F.Id("v"); var u = F.Id("u"); var j = F.Id("j"); var m = Heap(v,u);
        return Disp(All("v", All("u", All("j", Eq(Changed(v,u,j),
            Add(Add(Sub(Sub(Mul(D(2),m), Div(m,Pow(D(2),j))), Pow(D(2),Add(j,D(1)))),j),D(2)))))));
    }
    private static Formula ExceptionalFormula()
    {
        var v = F.Id("v"); var u = F.Id("u"); var k = F.Id("k");
        return Disp(All("v", All("u", All("k", Eq(Call("exceptionalCount",v,u,k),
            Call("if", Eq(k,v), u, Mul(Add(Sub(v,k),D(1)),Call("oddDivisorCount",u))))))));
    }
    private static Formula RecurrenceFormula()
    {
        var v = F.Id("v"); var u = F.Id("u"); var k = F.Id("k"); var j = F.Id("j");
        var initial = Eq(Rec(v,u,D(0)),Add(Mul(Add(v,D(1)),Call("oddDivisorCount",u)),D(1)));
        var step = Eq(Rec(v,u,Add(k,D(1))),Add(Add(Call("max",Rec(v,u,k),
            MaxRange("j",Add(k,D(1)),Changed(v,u,j))),Call("exceptionalCount",v,u,Add(k,D(1)))),D(1)));
        return Disp(All("v",All("u",And(initial,All("k",step)))));
    }
    private static Formula BoundFormula()
    {
        var v=F.Id("v"); var u=F.Id("u");
        return Disp(All("v",All("u",Eq(Call("bound",v,u),Rec(v,u,v)))));
    }
    private static Formula MonotoneFormula()
    {
        var v=F.Id("v"); var u=F.Id("u"); var i=F.Id("i"); var j=F.Id("j");
        return Disp(All("v",All("u",All("i",All("j",Imp(Le(i,j),Le(Rec(v,u,i),Rec(v,u,j))))))));
    }
    private static Formula DivisorBoundFormula()
    {
        var u=F.Id("u"); return Disp(All("u",Le(Call("oddDivisorCount",u),u)));
    }
    private static Formula FiniteFormula()
    {
        var v=F.Id("v"); var u=F.Id("u");
        var conditions=And(Le(D(1),v),And(Le(v,D(1,5)),And(Le(D(1),u),And(Le(u,v),
            And(Eq(Call("mod",u,D(2)),D(1)),new Formula.Not(And(Eq(u,D(1)),Le(v,D(3)))))))));
        return Disp(All("v",All("u",Imp(conditions,Le(Call("bound",v,u),TwiceHeap(v,u))))));
    }
    private static Formula TriangleFormula()
    {
        var v=F.Id("v"); return Disp(All("v",Eq(Tri(v),Div(Mul(v,Add(v,D(1))),D(2)))));
    }
    private static Formula TriangleTwiceFormula()
    {
        var v=F.Id("v"); return Disp(All("v",Eq(Mul(D(2),Tri(v)),Mul(v,Add(v,D(1))))));
    }
    private static Formula SquareFormula()
    {
        var v=F.Id("v");
        return Disp(All("v",Imp(Le(D(1,6),v),Le(Mul(v,Pow(Add(Add(Tri(v),Mul(D(2),v)),D(1)),D(2))),Pow(D(2),Add(v,D(3)))))));
    }
    private static Formula LinearFormula()
    {
        var v=F.Id("v");
        return Disp(All("v",Imp(Le(D(1,6),v),Le(Add(Add(Tri(v),Mul(D(2),v)),D(2)),Pow(D(2),Add(v,D(1)))))));
    }
    private static Formula UnrollFormula()
    {
        var v=F.Id("v"); var u=F.Id("u"); var k=F.Id("k"); var n=F.Id("n"); var j=F.Id("j");
        var conditions=And(Le(k,v),And(Le(Rec(v,u,D(0)),n),All("j",Imp(Lt(j,v),Le(Changed(v,u,j),n)))));
        return Disp(All("v",All("u",All("k",All("n",Imp(conditions,Le(Rec(v,u,k),Add(n,IncrementSum(v,u,k)))))))));
    }
    private static Formula DescendingFormula()
    {
        var v=F.Id("v"); var i=F.Id("i");
        return Disp(All("v",Eq(SumRange("i",v,Sub(v,i)),Tri(v))));
    }
    private static Formula IncrementFormula()
    {
        var v=F.Id("v"); var u=F.Id("u");
        return Disp(All("v",All("u",Le(IncrementSum(v,u,v),Budget(v,u)))));
    }
    private static Formula GapFormula()
    {
        var v=F.Id("v"); var u=F.Id("u"); var j=F.Id("j");
        var lhs=Add(Add(Mul(Tri(v),u),Mul(D(2),v)),D(1));
        var rhs=Add(Div(Heap(v,u),Pow(D(2),j)),Pow(D(2),Add(j,D(1))));
        return Disp(All("v",All("u",All("j",Imp(And(LargeConditions(v,u),Lt(j,v)),Le(lhs,rhs))))));
    }
    private static Formula ChangedBudgetFormula()
    {
        var v=F.Id("v"); var u=F.Id("u"); var j=F.Id("j");
        return Disp(All("v",All("u",All("j",Imp(And(LargeConditions(v,u),Lt(j,v)),
            Le(Add(Add(Changed(v,u,j),Mul(Tri(v),u)),v),TwiceHeap(v,u)))))));
    }
    private static Formula InitialFormula()
    {
        var v=F.Id("v"); var u=F.Id("u");
        return Disp(All("v",All("u",Imp(And(Le(D(1,6),v),Le(D(1),u)),
            Le(Add(Add(Rec(v,u,D(0)),Mul(Tri(v),u)),v),TwiceHeap(v,u))))));
    }
    private static Formula LargeFormula()
    {
        var v=F.Id("v"); var u=F.Id("u");
        return Disp(All("v",All("u",Imp(LargeConditions(v,u),Le(Call("bound",v,u),TwiceHeap(v,u))))));
    }
}

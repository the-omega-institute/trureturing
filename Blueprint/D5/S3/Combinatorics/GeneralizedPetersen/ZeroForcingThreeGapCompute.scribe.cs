using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.GeneralizedPetersen;

internal sealed class ZeroForcingThreeGapComputeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCompute.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/krishnan2026correction");

    public DocumentDefinition Create()
    {
        var c = V("c"); var m = V("m"); var p = V("p"); var i = V("i");
        var j = V("j"); var k = V("k"); var d = V("d"); var reverse = V("reverse");
        var price = V("price"); var scores = V("scores"); var fuel = V("fuel");
        var common = new (string Name, Formula Domain)[]
            { ("c", Nat()), ("m", Nat()), ("p", List(Nat())) };
        var directional = new (string Name, Formula Domain)[]
            { ("c", Nat()), ("m", Nat()), ("p", List(Nat())), ("i", Nat()), ("reverse", Name("Bool")) };
        var index = If(Eq(reverse, True()), Call("backward", c, i, k), Call("forward", c, i, k));
        var oldMask = Call("reachMask", c, m, p, i, reverse, k);
        var nextMask = Call("foldl", Lambda("mask", Nat(), Lambda("x", Nat(),
            Call("bitwise", Name("or"), V("mask"), Mul(oldMask, Pow(Num(2), V("x")))))),
            Num(0), Call("choices", m, p, index));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Short-prefix masks and dual prices bound the ten largest layer scores of every bounded completion.",
            H("Bounds for Partial Cyclic Gap Words"),
            Blocks(
            Node("choices", "Allowed values of an unfinished gap", "choices",
                Disp(Q(Eq(Call("choices", m, p, j), If(Lt(j, Len(p)), ListOf(At(p, j)), Call("map", Lambda("k", Nat(), Add(k, Num(1))), Call("range", m)))), ("m", Nat()), ("p", List(Nat())), ("j", Nat()))),
                "An already specified gap has its single fixed value. Every later gap may take any value from one through m.",
                DescribeRole.Definition),
            Node("forward", "Forward cyclic position", "forward",
                Disp(Q(Eq(Call("forward", c, i, j), Mod(Add(i, j), c)), ("c", Nat()), ("i", Nat()), ("j", Nat()))),
                "Advance j positions around a cycle of length c.",
                DescribeRole.Definition),
            Node("backward", "Backward cyclic position", "backward",
                Disp(Q(Eq(Call("backward", c, i, j), Mod(Sub(Add(i, c), Add(j, Num(1))), c)), ("c", Nat()), ("i", Nat()), ("j", Nat()))),
                "The reverse scan starts at the gap immediately before i. Natural-number subtraction is truncated at zero.",
                DescribeRole.Definition),
            Node("outer-gap-bound", "Largest possible outer-gap score", "phiUpper",
                Disp(Q(Eq(Call("phiUpper", m, p, j), If(Mem(Num(1), Call("choices", m, p, j)), Num(2), If(Mem(Num(2), Call("choices", m, p, j)), Num(1), Num(0)))), ("m", Nat()), ("p", List(Nat())), ("j", Nat()))),
                "A possible gap of one contributes two; otherwise a possible gap of two contributes one; all larger gaps contribute zero.",
                DescribeRole.Definition),
            Node("outer-slot", "Upper bound for an outer slot", "outer",
                Disp(Q(Eq(Call("outer", c, m, p, i), Add(Call("phiUpper", m, p, Call("backward", c, i, Num(0))), Call("phiUpper", m, p, i))), [.. common, ("i", Nat())])),
                "The outer slot is bounded by the sum of the preceding and following gap bounds.",
                DescribeRole.Definition),
            Node("price-bound", "A dual price for ten slots", "priceBound",
                Disp(Q(Eq(Call("priceBound", scores, price), Add(Mul(Num(10), price), Call("sum", Call("map", Lambda("s", Nat(), Sub(V("s"), price)), scores)))), ("scores", List(Nat())), ("price", Nat()))),
                "Charge a common price to ten selected slots and add every positive excess above that price. Each subtraction in the natural numbers is truncated at zero.",
                DescribeRole.Definition),
            Node("exceptional-roots", "The six exceptional rooted words", "exceptionalRoots",
                Disp(Eq(Name("exceptionalRoots"), ListOf(ListOf(Num(6), Num(2), Num(1), Num(2), Num(1), Num(2)),
                    ListOf(Num(3), Num(2), Num(1), Num(2), Num(1), Num(2), Num(3)),
                    ListOf(Num(3), Num(3), Num(2), Num(1), Num(2), Num(1), Num(2)),
                    ListOf(Num(6), Num(2), Num(1), Num(1), Num(1), Num(1), Num(2)),
                    ListOf(Num(3), Num(2), Num(1), Num(1), Num(1), Num(1), Num(2), Num(3)),
                    ListOf(Num(3), Num(3), Num(2), Num(1), Num(1), Num(1), Num(1), Num(2))))),
                "These six positive gap lists are the exceptional leaves of the bounded recurrence.",
                DescribeRole.Definition),
            Node("reach-mask", "Reachable short prefix sums", "reachMask",
                Disp(Q(And(Eq(Call("reachMask", c, m, p, i, reverse, Num(0)), Num(1)), Q(Eq(Call("reachMask", c, m, p, i, reverse, Add(k, Num(1))), Mod(nextMask, Num(128))), ("k", Nat()))), directional)),
                "Bit zero initially represents the empty sum. Each step shifts the preceding mask by every allowed gap and takes their bitwise union, retaining bits zero through six.",
                DescribeRole.Definition),
            Node("mask-hit", "A reachable target distance", "maskHit",
                Disp(Q(Iff(Eq(Call("maskHit", c, m, p, i, reverse, d), True()), Ex("j", Nat(), And(Lt(j, c), Eq(Call("testBit", Call("reachMask", c, m, p, i, reverse, Add(j, Num(1))), d), True())))), [.. directional, ("d", Nat())])),
                "A target distance is hit if its bit occurs after one through c prefix steps.",
                DescribeRole.Definition),
            Node("direction-score", "One directional inner score", "maskDirection",
                Disp(Q(Eq(Call("maskDirection", c, m, p, i, reverse), If(Eq(Call("maskHit", c, m, p, i, reverse, Num(3)), True()), Num(2), If(Eq(Call("maskHit", c, m, p, i, reverse, Num(6)), True()), Num(1), Num(0)))), directional)),
                "A possible prefix of length three scores two. In its absence, a possible prefix of length six scores one.",
                DescribeRole.Definition),
            Node("inner-slot", "Upper bound for an inner slot", "maskInner",
                Disp(Q(Eq(Call("maskInner", c, m, p, i), Add(Call("maskDirection", c, m, p, i, False()), Call("maskDirection", c, m, p, i, True()))), [.. common, ("i", Nat())])),
                "Add the forward and backward inner-direction bounds.",
                DescribeRole.Definition),
            Node("slot-list", "The list of outer and inner bounds", "maskSlots",
                Disp(Q(Eq(Call("maskSlots", c, m, p), Call("flatten", Call("ofFn", Lambda("i", Fin(c), ListOf(Call("outer", c, m, p, Val(i)), Call("maskInner", c, m, p, Val(i))))))), common)),
                "At each cyclic index, list the outer bound followed by the inner bound, giving twice c entries.",
                DescribeRole.Definition),
            Node("minimum-price", "The best of five dual prices", "maskUpper",
                Disp(Q(Eq(Call("maskUpper", c, m, p), Call("min", Call("priceBound", Call("maskSlots", c, m, p), Num(0)), Call("min", Call("priceBound", Call("maskSlots", c, m, p), Num(1)), Call("min", Call("priceBound", Call("maskSlots", c, m, p), Num(2)), Call("min", Call("priceBound", Call("maskSlots", c, m, p), Num(3)), Call("priceBound", Call("maskSlots", c, m, p), Num(4))))))), common)),
                "Take the minimum of priceBound at the five prices zero through four.",
                DescribeRole.Definition),
            Node("mask-recurrence", "The bounded-completion recurrence", "maskCheck",
                Disp(Q(Iff(Eq(Call("maskCheck", c, fuel, m, p), True()), Or(Le(Call("maskUpper", c, m, p), Add(Mul(Num(4), c), Num(5))), And(Lt(Add(Mul(Num(4), c), Num(5)), Call("maskUpper", c, m, p)), Or(And(Eq(fuel, Num(0)), Or(Lt(Call("sum", p), Num(14)), Mem(p, Name("exceptionalRoots")))), And(Lt(Num(0), fuel), Q(Imp(Lt(j, m), Eq(Call("maskCheck", c, Sub(fuel, Num(1)), m, Call("append", p, ListOf(Add(j, Num(1))))), True())), ("j", Nat()))))))), ("c", Nat()), ("fuel", Nat()), ("m", Nat()), ("p", List(Nat())))),
                "A prefix is accepted when its upper score is at most four times c plus five. Otherwise the recurrence checks every next gap; a leaf must have sum below fourteen or belong to exceptionalRoots.",
                DescribeRole.Definition)),
            []));
    }

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Name(string name) => new Formula.NamedConstant(FormulaIdentifier.Create(name));
    private static Formula V(string name) => F.Id(name);
    private static Formula Num(long value) => new Formula.Number(value);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Q(Formula body, params (string Name, Formula Domain)[] variables)
    {
        for (var i = variables.Length - 1; i >= 0; i--)
            body = new Formula.Bind(FormulaQuantifier.ForAll,
                FormulaIdentifier.Create(variables[i].Name), variables[i].Domain, body);
        return body;
    }
    private static Formula Ex(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Mem(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula And(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Or, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Pow(Formula value, Formula power) => new Formula.Power(value, power);
    private static Formula Mod(Formula value, Formula modulus) => new Formula.Modulo(value, modulus);
    private static Formula Len(Formula value) => Call("length", value);
    private static Formula Fin(Formula value) => Call("Fin", value);
    private static Formula List(Formula value) => Call("List", value);
    private static Formula Val(Formula value) => Call("val", value);
    private static Formula At(Formula value, Formula index) => Seq(value, OpenBracket, index, CloseBracket);
    private static Formula ListOf(params Formula[] values) =>
        Seq(OpenBracket, Seq([.. values.SelectMany((value, index) => index == 0
            ? new[] { value } : new[] { Comma, Sp, value })]), CloseBracket);
    private static Formula Lambda(string variable, Formula domain, Formula body) =>
        Seq(Open, LambdaLower, Sp, V(variable), Colon, domain, Comma, Sp, body, Close);
    private static Formula If(Formula condition, Formula yes, Formula no) => Call("if", condition, yes, no);
    private static Formula True() => Name("true");
    private static Formula False() => Name("false");
}

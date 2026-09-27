using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.GeneralizedPetersen;

internal sealed class ZeroForcingThreeGapExactDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapExact.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/krishnan2026correction");

    public DocumentDefinition Create()
    {
        var positions = V("positions"); var code = V("code"); var j = V("j");
        var x = V("X"); var v = V("v"); var start = V("start"); var count = V("count");
        var vertex = Vertices(Num(14));
        var decoded = Call("labelledSupport", positions, code);
        return DocumentDefinition.Create(ScribeNode.Create(
            "Base-three labels select the outer, inner, or both vertices at each support column.",
            H("Exact Layer Codes on Exceptional Supports"),
            Blocks(
            Node("positions6", "The positions6 support", "positions6",
                Disp(Eq(Name("positions6"), ListOf(Num(0), Num(6), Num(8), Num(9), Num(11), Num(12)))),
                "This ordered list gives the 6 support positions at circumference fourteen.",
                DescribeRole.Definition),
            Node("positions7a", "The positions7a support", "positions7a",
                Disp(Eq(Name("positions7a"), ListOf(Num(0), Num(3), Num(6), Num(8), Num(9), Num(11), Num(12)))),
                "This ordered list gives the 7 support positions at circumference fourteen.",
                DescribeRole.Definition),
            Node("positions7b", "The positions7b support", "positions7b",
                Disp(Eq(Name("positions7b"), ListOf(Num(0), Num(6), Num(8), Num(9), Num(10), Num(11), Num(12)))),
                "This ordered list gives the 7 support positions at circumference fourteen.",
                DescribeRole.Definition),
            Node("positions8", "The positions8 support", "positions8",
                Disp(Eq(Name("positions8"), ListOf(Num(0), Num(3), Num(6), Num(8), Num(9), Num(10), Num(11), Num(12)))),
                "This ordered list gives the 8 support positions at circumference fourteen.",
                DescribeRole.Definition),
            Node("positions7r", "The positions7r support", "positions7r",
                Disp(Eq(Name("positions7r"), ListOf(Num(0), Num(3), Num(5), Num(6), Num(8), Num(9), Num(11)))),
                "This ordered list gives the 7 support positions at circumference fourteen.",
                DescribeRole.Definition),
            Node("positions8r", "The positions8r support", "positions8r",
                Disp(Eq(Name("positions8r"), ListOf(Num(0), Num(3), Num(5), Num(6), Num(7), Num(8), Num(9), Num(11)))),
                "This ordered list gives the 8 support positions at circumference fourteen.",
                DescribeRole.Definition),
            Node("label-digit", "A base-three digit", "labelDigit",
                Disp(Q(Eq(Call("labelDigit", code, j), Mod(Call("div", code, Pow(Num(3), j)), Num(3))), ("code", Nat()), ("j", Nat()))),
                "The digit at position j is obtained by natural-number division by three to the jth power, followed by reduction modulo three.",
                DescribeRole.Definition),
            Node("labelled-support", "Decode a layer assignment", "labelledSupport",
                Disp(Q(Eq(decoded, SetOf("v", vertex, Ex("j", Nat(), And(Lt(j, Len(positions)), Eq(Val(Second(v)), At(positions, j)), Or(And(Eq(First(v), True()), Ne(Call("labelDigit", code, j), Num(0))), And(Eq(First(v), False()), Ne(Call("labelDigit", code, j), Num(1)))))))), ("positions", List(Nat())), ("code", Nat()))),
                "Digit zero selects only the outer vertex, digit one only the inner vertex, and digit two both vertices at the corresponding column.",
                DescribeRole.Definition),
            Node("direct-score", "Count occupied requests and empty collisions", "directScore",
                Disp(Q(Eq(Call("directScore", x), Add(Add(Card(SetOf("v", x, Mem(Second(Call("positiveShift", Num(14), v)), Call("columns", x)))), Card(SetOf("v", x, Mem(Second(Call("negativeShift", Num(14), v)), Call("columns", x))))), Card(SetOf("v", vertex, And(Not(Mem(Second(v), Call("columns", x))), Mem(Call("negativeShift", Num(14), v), x), Mem(Call("positiveShift", Num(14), v), x)))))), ("X", Fs(vertex)))),
                "Count forward requests into occupied columns, backward requests into occupied columns, and vertices in empty columns receiving requests from both directions.",
                DescribeRole.Definition),
            Node("exact-row", "The exact score test for one label code", "exactRow",
                Disp(Q(Iff(Eq(Call("exactRow", positions, code), True()), Or(Ne(Card(decoded), Num(10)), Le(Call("directScore", decoded), Add(Mul(Num(2), Len(positions)), Num(2))))), ("positions", List(Nat())), ("code", Nat()))),
                "Only decoded sets of size ten require the bound on directScore; all other cardinalities satisfy the test automatically.",
                DescribeRole.Definition),
            Node("exact-chunk", "A consecutive interval of label codes", "exactChunk",
                Disp(Q(Iff(Eq(Call("exactChunk", positions, start, count), True()), Q(Imp(Lt(j, count), Eq(Call("exactRow", positions, Add(start, j)), True())), ("j", Nat()))), ("positions", List(Nat())), ("start", Nat()), ("count", Nat()))),
                "Every code from start through start plus count minus one must satisfy exactRow.",
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
    private static Formula Ne(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
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
    private static Formula Not(Formula value) => new Formula.Not(value);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Pow(Formula value, Formula power) => new Formula.Power(value, power);
    private static Formula Mod(Formula value, Formula modulus) => new Formula.Modulo(value, modulus);
    private static Formula Card(Formula value) => Call("card", value);
    private static Formula Len(Formula value) => Call("length", value);
    private static Formula Fin(Formula value) => Call("Fin", value);
    private static Formula Vertices(Formula n) => Seq(Name("Bool"), Times, Sp, Fin(n));
    private static Formula Fs(Formula value) => Call("Finset", value);
    private static Formula List(Formula value) => Call("List", value);
    private static Formula First(Formula value) => Call("fst", value);
    private static Formula Second(Formula value) => Call("snd", value);
    private static Formula Val(Formula value) => Call("val", value);
    private static Formula At(Formula value, Formula index) => Seq(value, OpenBracket, index, CloseBracket);
    private static Formula ListOf(params Formula[] values) =>
        Seq(OpenBracket, Seq([.. values.SelectMany((value, index) => index == 0
            ? new[] { value } : new[] { Comma, Sp, value })]), CloseBracket);
    private static Formula SetOf(string variable, Formula domain, Formula predicate) =>
        Seq(OpenBrace, Sp, V(variable), Sp, InMacro, Sp, domain, Bar, Sp, predicate, CloseBrace, Sp);
    private static Formula True() => Name("true");
    private static Formula False() => Name("false");
}

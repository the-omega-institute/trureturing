using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.GeneralizedPetersen;

internal sealed class ZeroForcingThreeShiftCoreDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeShiftCore.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/krishnan2026correction");

    public DocumentDefinition Create()
    {
        var n = V("n"); var x = V("X"); var v = V("v");
        return DocumentDefinition.Create(ScribeNode.Create(
            "Column support and the two layer-dependent shifts organize requests from selected vertices.",
            H("Columns and Cyclic Neighbor Shifts"),
            Blocks(
            Node("columns", "Occupied columns", "columns",
                Disp(Q(Eq(Call("columns", x), Image(x, "v", Second(v))), ("n", Nat()), ("X", Fs(Vertices(n))))),
                "Project the selected vertices onto their column indices.",
                DescribeRole.Definition),
            Node("occupied-vertices", "Both vertices of every occupied column", "occupiedVertices",
                Disp(Q(Eq(Call("occupiedVertices", x), Seq(Name("Bool"), Times, Sp, Call("columns", x))), ("n", Nat()), ("X", Fs(Vertices(n))))),
                "For each occupied column, include both its outer and inner vertex.",
                DescribeRole.Definition),
            Node("positive-shift", "Forward layer neighbor", "positiveShift",
                Disp(Q(Imp(Lt(Num(0), n), Eq(Call("positiveShift", n, v), Pair(First(v), Add(Second(v), Call("ofNat", n, If(Eq(First(v), True()), Num(3), Num(1))))))), ("n", Nat()), ("v", Vertices(n)))),
                "The equivalence adds one in the outer layer and three in the inner layer, with arithmetic modulo n.",
                DescribeRole.Definition),
            Node("negative-shift", "Backward layer neighbor", "negativeShift",
                Disp(Q(Imp(Lt(Num(0), n), Eq(Call("negativeShift", n, v), Pair(First(v), Sub(Second(v), Call("ofNat", n, If(Eq(First(v), True()), Num(3), Num(1))))))), ("n", Nat()), ("v", Vertices(n)))),
                "The inverse of positiveShift subtracts the corresponding layer step modulo n.",
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
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Fin(Formula value) => Call("Fin", value);
    private static Formula Vertices(Formula n) => Seq(Name("Bool"), Times, Sp, Fin(n));
    private static Formula Fs(Formula value) => Call("Finset", value);
    private static Formula Pair(Formula left, Formula right) => Seq(Open, left, Comma, Sp, right, Close);
    private static Formula First(Formula value) => Call("fst", value);
    private static Formula Second(Formula value) => Call("snd", value);
    private static Formula Image(Formula set, string variable, Formula value) =>
        new Formula.SetBuilder(value, V(variable), set);
    private static Formula If(Formula condition, Formula yes, Formula no) => Call("if", condition, yes, no);
    private static Formula True() => Name("true");
}

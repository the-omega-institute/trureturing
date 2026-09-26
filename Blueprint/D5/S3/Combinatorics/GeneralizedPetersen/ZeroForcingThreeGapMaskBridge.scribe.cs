using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.GeneralizedPetersen;

internal sealed class ZeroForcingThreeGapMaskBridgeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapMaskBridge.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/krishnan2026correction");

    public DocumentDefinition Create()
    {
        var c = V("c"); var m = V("m"); var p = V("p"); var h = V("h");
        var j = V("j"); var price = V("price"); var fuel = V("fuel"); var e = V("e");
        var prefix = Q(Imp(Lt(Val(j), Len(p)), Eq(Call("h", j), At(p, Val(j)))), ("j", Fin(c)));
        var bounds = Q(And(Le(Num(1), Call("h", j)), Le(Call("h", j), m)), ("j", Fin(c)));
        var common = new (string Name, Formula Domain)[]
            { ("c", Nat()), ("m", Nat()), ("p", List(Nat())), ("h", Arrow(Fin(c), Nat())) };
        return DocumentDefinition.Create(ScribeNode.Create(
            "Every bounded completion inherits the slot-price bound and the classification of accepted large-score leaves.",
            H("Sound Bounds for the Mask Recurrence"),
            Blocks(
            Node("slot-price", "A dual price bounds every completion", "T_le_maskPrice",
                Disp(Q(Imp(And(Lt(Num(0), c), prefix, bounds), Le(Call("T", h), Call("priceBound", Call("maskSlots", c, m, p), price))), [.. common, ("price", Nat())])),
                "For a positive-length word extending the prescribed prefix, with every gap between one and m, every natural dual price bounds T by priceBound of the computed slot list.",
                DescribeRole.Theorem),
            Node("recurrence-sound", "Accepted large-score completions are exceptional", "maskCheck_sound",
                Disp(Q(Imp(And(Lt(Num(0), c), Eq(Add(Len(p), fuel), c), prefix, bounds, Eq(Call("maskCheck", c, fuel, m, p), True()), Le(Num(14), SumOver("j", Fin(c), Call("h", j))), Le(Add(Mul(Num(4), c), Num(6)), Call("T", h))), Ex("e", List(Nat()), And(Mem(e, Name("exceptionalRoots")), Eq(Len(e), c), Q(Imp(Lt(Val(j), Len(e)), Eq(Call("h", j), At(e, Val(j)))), ("j", Fin(c)))))), [.. common, ("fuel", Nat())])),
                "An accepted completion with total at least fourteen and score at least four times c plus six is exactly one of the exceptional rooted words. Induction on the remaining prefix length carries the pointwise completion through the recurrence.",
                DescribeRole.Theorem)),
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
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Len(Formula value) => Call("length", value);
    private static Formula Fin(Formula value) => Call("Fin", value);
    private static Formula List(Formula value) => Call("List", value);
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula Val(Formula value) => Call("val", value);
    private static Formula At(Formula value, Formula index) => Seq(value, OpenBracket, index, CloseBracket);
    private static Formula SumOver(string variable, Formula domain, Formula body) =>
        Seq(Sum, Sp, Underscore, Grp(V(variable), Sp, InMacro, Sp, domain), body);
    private static Formula True() => Name("true");
}

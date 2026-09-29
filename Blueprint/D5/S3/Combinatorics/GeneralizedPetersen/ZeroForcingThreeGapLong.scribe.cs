using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.GeneralizedPetersen;

internal sealed class ZeroForcingThreeGapLongDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapLong.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/krishnan2026correction");

    public DocumentDefinition Create()
    {
        var c = V("c"); var h = V("h"); var r = V("r"); var i = V("i");
        return DocumentDefinition.Create(ScribeNode.Create(
            "Rotating a long gap to the root reduces its score bound to positive compositions of fourteen.",
            H("Fourteen-Column Words with a Long Gap"),
            Blocks(
            Node("rotate-word", "Cyclic rotation of a gap word", "rotateWord",
                Disp(Q(Eq(Call("rotateWord", h, r, i), Call("h", Add(r, i))), ("c", Nat()), ("h", Arrow(Fin(c), Nat())), ("r", Fin(c)), ("i", Fin(c)))),
                "The rotated word starts at r and retains the cyclic order of the gaps.",
                DescribeRole.Definition),
            Node("rotation", "Rotation as an index equivalence", "rotation",
                Disp(Q(Imp(Lt(Num(0), c), Eq(Call("rotation", r, i), Add(r, i))), ("c", Nat()), ("r", Fin(c)), ("i", Fin(c)))),
                "Cyclic addition by r is an equivalence of Fin c; its inverse subtracts r.",
                DescribeRole.Definition),
            Node("long-gap-score", "A long gap bounds the ten-slot score", "long_gap_score",
                Disp(Q(Imp(And(Le(Num(5), c), Le(c, Num(8)), Q(Le(Num(1), Call("h", i)), ("i", Fin(c))), Eq(SumOver("i", Fin(c), Call("h", i)), Num(14)), Le(Num(8), Call("h", r))), Le(Call("T", h), Add(Mul(Num(4), c), Num(5)))), ("c", Nat()), ("h", Arrow(Fin(c), Nat())), ("r", Fin(c)))),
                "A positive cyclic word with five through eight entries, total fourteen, and an entry at least eight has T at most four times its length plus five. The rooted positive-composition family contains twenty-two words.",
                DescribeRole.Theorem)),
            []));
    }

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
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
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
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
    private static Formula Fin(Formula value) => Call("Fin", value);
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula SumOver(string variable, Formula domain, Formula body) =>
        Seq(Sum, Sp, Underscore, Grp(V(variable), Sp, InMacro, Sp, domain), body);
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class OddParityExtensionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/OddParityExtension.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An odd parity condition determines exactly one omitted binary coordinate.",
        H("Unique Completion of an Odd-Parity Word"),
        Blocks(
            Node("agrees-off", "Agreement away from one coordinate", "agreesOff", Agreement(),
                "Binary words x and y agree off i when x(j) equals y(j) at every coordinate "
                + "j other than i.", DescribeRole.Definition),
            Node("odd-parity-extension", "Exactly one odd completion", "odd_parity_unique_extension",
                Completion(), "For any positive length L, any coordinate i, and any binary "
                + "word y, there is exactly one word x that agrees with y off i and has an "
                + "odd number of zero bits. The product of the signs on the other positions "
                + "is either one or minus one; precisely one choice at i makes the full "
                + "product minus one. This works for every omitted position.", DescribeRole.Theorem)), []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Cube(Formula n) => new Formula.Power(Fin(D(2)), Fin(n));
    private static Formula All(string n, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), domain, body);
    private static Formula Apply(Formula f, Formula i) => new Formula.Apply(f, [i]);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Agreement()
    {
        var l = F.Id("L"); var i = F.Id("i"); var j = F.Id("j"); var x = F.Id("x"); var y = F.Id("y");
        return Disp(All("L", Nat(), All("i", Fin(l), All("x", Cube(l), All("y", Cube(l),
            new Formula.Logic(Call("agreesOff", i, x, y), FormulaLogicOperator.Iff,
                All("j", Fin(l), new Formula.Logic(
                    new Formula.Relation(j, FormulaRelationOperator.NotEqual, i), FormulaLogicOperator.Implies,
                    Eqn(Apply(x, j), Apply(y, j))))))))));
    }
    private static Formula Completion()
    {
        var l = F.Id("L"); var i = F.Id("i"); var x = F.Id("x"); var y = F.Id("y");
        var property = Seq(Call("agreesOff", i, x, y), Land,
            x, InMacro, Call("parityFiber", l, Seq(Minus, D(1))));
        return Disp(All("L", Nat(), new Formula.Logic(
            new Formula.Relation(D(0), FormulaRelationOperator.LessThan, l), FormulaLogicOperator.Implies,
            All("i", Fin(l), All("y", Cube(l),
                Seq(Exists, Bang, Sp,
                    x, InMacro, Cube(l), Comma, property))))));
    }
}

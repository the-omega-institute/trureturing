using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Asymptotics;

internal sealed class BarnesSineBoundsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Analytic/braams2026barnesmittagport");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complex sine grows exponentially on every vertical line away from its real zeros.", H("BarnesSineBounds"), Blocks(
            Describe.Lean(DescribeId.Create("barnessinebounds-barnesRes-sin-lower-line"),
                DeclarationHandle.Create("D5/S3/Analytic/Asymptotics/BarnesSineBounds.barnesRes_sin_lower_line"),
                H("A sine lower bound"), StatementSource.FromAuthor(Disp(All("x", R, All("y", R, Leq(Mul(Div(Abs(Call("sin", Mul(V("pi"), V("x")))), Num(2)), Call("exp", Mul(V("pi"), Abs(V("y"))))), Norm(Call("sin", Mul(V("pi"), Add(V("x"), Mul(V("y"), V("i"))))))))))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("Here pi is the circle constant, i is the imaginary unit, and real inputs in complex expressions are embedded in Complex. The square of the sine norm is sin(x)^2+sinh(y)^2; its cosh bound yields the displayed estimate."))),
                DescribeRole.Theorem))));

    private static Formula R => F.Id("Real");
    private static Formula Cx => F.Id("Complex");
    private static Formula N => F.Id("Nat");
    private static Formula V(string name) => F.Id(name);
    private static Formula Num(byte digit) => D(digit);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
    private static Formula Map(string name, Formula type, Formula value) =>
        Seq(Open, F.Id(name), Colon, type, Sp, Mapsto, Sp, value, Close);
    private static Formula Add(Formula a, Formula b) => Seq(Open, a, Plus, b, Close);
    private static Formula Sub(Formula a, Formula b) => Seq(Open, a, Minus, b, Close);
    private static Formula Mul(Formula a, Formula b) => Seq(Open, a, Star, b, Close);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Negate(Formula a) => Seq(Minus, Open, a, Close);
    private static Formula Abs(Formula a) => new Formula.Absolute(a);
    private static Formula Norm(Formula a) => new Formula.Norm(a);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Asymptotics;

internal sealed class BarnesSineBoundsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Asymptotics/braams2026barnesmittagport");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complex sine grows exponentially on every vertical line away from its real zeros.", H("Sine bounds for Barnes contours"), Blocks(
            Describe.Lean(DescribeId.Create("barnessinebounds-barnesres-sin-lower-line"),
                DeclarationHandle.Create("D5/S3/Analytic/Asymptotics/BarnesSineBounds.barnesRes_sin_lower_line"),
                H("A sine lower bound"), StatementSource.FromAuthor(Disp(All("x", R, All("y", R, Leq(Mul(Div(Abs(Call("sin", Mul(Seq(Pi, Sp), V("x")))), Num(2)), Call("exp", Mul(Seq(Pi, Sp), Abs(V("y"))))), Norm(Call("sin", Mul(Seq(Pi, Sp), Add(V("x"), Mul(V("y"), Seq(Operatorname, Grp(F.Id("ComplexI"))))))))))))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("Here pi is the circle constant, i is the imaginary unit, and real inputs in complex expressions are embedded in Complex. The square of the sine norm is sin(x)^2+sinh(y)^2; its cosh bound yields the displayed estimate."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("barnessinebounds-barnesres-sin-lower-far"),
                DeclarationHandle.Create("D5/S3/Analytic/Asymptotics/BarnesSineBounds.barnesRes_sin_lower_far"),
                H("A bound uniform in the real coordinate"),StatementSource.FromAuthor(Disp(FarFormula())),
                AssessedProvenance.FromLiterature(Source),Blocks(Paragraph(Text("For abs(y) at least one, the sinh term gives exp(pi*abs(y))/4 independently of x. The literal kernel horizontal-decay proof uses this bound uniformly on each finite strip."))),DescribeRole.Theorem))));

    private static Formula FarFormula()
    {
        Formula lhs=Mul(Div(Num(1),D(4)),Call("exp",Mul(Seq(Pi,Sp),Abs(V("y")))));
        Formula rhs=Norm(Call("sin",Mul(Seq(Pi,Sp),Add(V("x"),Mul(V("y"),Seq(Operatorname,Grp(F.Id("ComplexI"))))))));
        Formula implication=new Formula.Logic(Leq(Num(1),Abs(V("y"))),FormulaLogicOperator.Implies,Leq(lhs,rhs));
        return All("x",R,All("y",R,implication));
    }

    private static Formula R => F.Id("Real");
    private static Formula V(string name) => F.Id(name);
    private static Formula Num(byte digit) => D(digit);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
    private static Formula Add(Formula a, Formula b) => Seq(Open, a, Plus, b, Close);
    private static Formula Mul(Formula a, Formula b) => Seq(Open, a, Star, b, Close);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Abs(Formula a) => new Formula.Absolute(a);
    private static Formula Norm(Formula a) => new Formula.Norm(a);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Asymptotics;

internal sealed class MittagLefflerBarnesKernelDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Analytic/braams2026barnesmittagport");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal Barnes kernel is integrable on exterior vertical contours.", H("The Mittag-Leffler Barnes kernel"), Blocks(
            Describe.Lean(DescribeId.Create("mittaglefflerbarneskernel-kernel"),
                DeclarationHandle.Create("D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.kernel"),
                H("The literal Barnes kernel"), StatementSource.FromAuthor(Disp(KernelFormula())),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("ComplexGamma is complex Gamma, log is the principal complex logarithm, and all real scalars are embedded into Complex. The formula uses the entire reciprocal Gamma, including its zeros."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("mittaglefflerbarneskernel-margin"),
                DeclarationHandle.Create("D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.margin"),
                H("The angular margin"), StatementSource.FromAuthor(Disp(All("alpha", R, All("z", Cx, Equal(Call("margin", V("alpha"), V("z")), Sub(Mul(Seq(Pi, Sp), Sub(Num(1), Div(V("alpha"), Num(2)))), Abs(Call("arg", Negate(V("z")))))))))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The strict exterior sector is exactly the set where margin(alpha,z) is positive."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("mittaglefflerbarneskernel-exists-line-majorant"),
                DeclarationHandle.Create("D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.exists_line_majorant"),
                H("A majorant on a vertical line"), StatementSource.FromAuthor(Disp(MajorantFormula())),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("For alpha positive and a real line c with sin(pi*c) nonzero, the constants C and K are independent of the line coordinate y. Reflection converts the two Gamma factors into pi/sin(pi*s), leaving the reciprocal Gamma bound and the exact principal-logarithm exponential norm. No series representation is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("mittaglefflerbarneskernel-integrable-line"),
                DeclarationHandle.Create("D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.integrable_line"),
                H("Integrability in the strict exterior sector"), StatementSource.FromAuthor(Disp(IntegrableFormula())),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The polynomial-exponential majorant is integrable when the angular margin is positive. The reflected expression is measurable because reciprocal Gamma is entire; division by sine is a measurable operation."))),
                DescribeRole.Theorem))));

    private static Formula KernelFormula() => All("alpha", R, All("beta", R, All("z", Cx,
        All("s", Cx, Equal(Call("kernel", V("alpha"), V("beta"), V("z"), V("s")),
        Mul(Mul(Mul(Call("ComplexGamma", V("s")), Call("ComplexGamma", Sub(Num(1), V("s")))),
            Div(Num(1), Call("ComplexGamma", Sub(V("beta"), Mul(V("alpha"), V("s")))))),
            Call("exp", Mul(Negate(V("s")), Call("log", Negate(V("z")))))))))));
    private static Formula Params(Formula conclusion) => All("alpha", R,
        Imp(Lt(Num(0), V("alpha")), All("beta", R, All("c", R, All("z", Cx,
            Imp(Seq(Call("sin", Mul(Seq(Pi, Sp), V("c"))), Neq, Sp, Num(0)), conclusion))))));
    private static Formula MajorantFormula() => Params(Some("C", R, Some("K", N,
        All("y", R, Leq(Norm(Call("kernel", V("alpha"), V("beta"), V("z"), Add(V("c"), Mul(V("y"), Seq(Operatorname, Grp(F.Id("ComplexI"))))))),
            Mul(Mul(V("C"), Pow(Add(Num(1), Abs(V("y"))), V("K"))),
                Call("exp", Negate(Mul(Call("margin", V("alpha"), V("z")), Abs(V("y")))))))))));
    private static Formula IntegrableFormula() => Params(Imp(Lt(Num(0), Call("margin", V("alpha"), V("z"))),
        Call("Integrable", Map("y", R, Call("kernel", V("alpha"), V("beta"), V("z"), Add(V("c"), Mul(V("y"), Seq(Operatorname, Grp(F.Id("ComplexI"))))))))));

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
}

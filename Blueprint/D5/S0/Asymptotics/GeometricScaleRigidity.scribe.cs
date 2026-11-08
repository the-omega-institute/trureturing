using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics;

internal sealed class GeometricScaleRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A continuous profile constant on a shrinking geometric orbit takes its value at zero.",
        H("Geometric Scale Rigidity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("geometric-scale-rigidity"),
                DeclarationHandle.Create(
                    "D5/S0/Asymptotics/GeometricScaleRigidity.geometric_scale_rigidity"),
                H("Geometric-orbit rigidity at the limiting point"),
                StatementSource.FromAuthor(Disp(TheoremFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The powers of rho converge to zero because rho is nonnegative and less "
                            + "than one. Multiplication by the fixed M preserves this limit, and "
                            + "continuity of h at zero sends the geometric orbit to h(0).")),
                    Paragraph(Text(
                        "The orbit is also constant at h(M) by the stated hypothesis. Uniqueness "
                            + "of limits identifies the two values. This is the shrinking-scale "
                            + "step used in the Continuation XII argument; the surrounding quantum "
                            + "orbit, rate, and response hypotheses remain separate."))),
                DescribeRole.Theorem)),
        []));

    private static Formula TheoremFormula()
    {
        var h = V("h");
        var rho = V("rho");
        var m = V("M");
        var real = Real;
        var scale = Seq(rho, Caret, Grp(V("n")), Sp, Times, Sp, m);
        var hscale = All("n", Naturals(), Eq(Call("h", scale), Call("h", m)));
        var assumptions = And(
            Call("ContinuousAt", h, D(0)),
            Seq(D(0), Sp, Le, Sp, rho),
            Seq(rho, Sp, Lt, Sp, D(1)),
            hscale);
        return All("h", Arrow(real, real),
            All("rho", real,
                All("M", real,
                    Implies(assumptions, Eq(Call("h", m), Call("h", D(0)))))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Arrow(Formula a, Formula b) => Paren(Seq(a, Sp, To, Sp, b));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Paren(Formula formula) => Seq(Open, formula, Close);
    private static Formula Eq(Formula left, Formula right) => Seq(left, Sp, F.Eq, Sp, right);
    private static Formula And(params Formula[] terms) =>
        Seq([.. terms.SelectMany((term, index) =>
            index == 0 ? new[] { Paren(term) } : new[] { Sp, Land, Sp, Paren(term) })]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Paren(Seq(V(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Implies(Formula premise, Formula conclusion) =>
        Seq(Paren(premise), Sp, Rightarrow, Sp, conclusion);
}

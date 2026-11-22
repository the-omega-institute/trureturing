using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder;

internal sealed class RHMobiusEvenCutoffShrinkingWidthDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffShrinkingWidth";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The centered root spectrum on shrinking signed prime windows",
        H("Shrinking logarithmic widths"),
        Blocks(Describe.Lean(DescribeId.Create("signed-window-even-cutoff-shrinking-width"),
            DeclarationHandle.Create(Owner + ".signed_window_even_cutoff_shrinking_width"),
            H("The centered root spectrum is recovered uniformly in the late start"),
            StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Put q=m+1=2r, s=1/2−1/q, δ=1/q−1/(q+1) and c(m)=μ(q)q/(m s). "
                    + "F(m,u,L) is the original signed residual for exp(u), exp(u+L), divided by "
                    + "its power gap. P(r,u,L) is the root-primitive increment at the same endpoints "
                    + "divided by the same gap.")),
                Paragraph(Text("S(r,u) is the real part of the sum over all actual zero occurrences "
                    + "of rootCoeff(r,k) exp((ρₖ−1/2)u/r), divided by s. A(r,u,L) is the integral "
                    + "of exp(−st) S(r,u+t) over [0,L] divided by the integral of exp(−st) over "
                    + "the same interval. The denominator is positive for L>0.")),
                Paragraph(Text("The known integral of the root density gives the primitive "
                    + "increment. Removing its exponential decay yields the positive normalized "
                    + "average of the centered series. Under RH, each centered mode is uniformly "
                    + "continuous and bounded in modulus by its coefficient. The summable "
                    + "coefficient bound passes uniform continuity to the full series. The "
                    + "weighted mean value theorem identifies the average with a value of the "
                    + "series within the window. Its modulus controls the error at that point, "
                    + "and the even-cutoff expansion supplies the decaying arithmetic remainder."))),
            DescribeRole.Theorem))));

    private static Formula Domain(string name) => F.Seq(F.Mathbb, F.Grp(F.Id(name)));
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);

    private static Formula Statement()
    {
        var m = Id("m");
        var r = Id("r");
        var u = Id("u");
        var width = Id("L");
        var threshold = Id("U");
        var widthThreshold = Id("H");
        var error = Id("e");
        var constant = Id("K");
        var zero = Num(0);

        var exactAverage = All("u", Domain("R"), All("L", Domain("R"),
            Imp(Lt(zero, width), Equal(Call("P", r, u, width), Call("A", r, u, width)))));
        var remainder = new Formula.Absolute(Add(
            Add(Call("F", m, u, width), Call("c", m)),
            Multiply(Call("mu", r), Call("S", r, u))));
        var bound = Add(error, Multiply(constant,
            Call("exp", new Formula.Negate(Multiply(Call("delta", m), u)))));
        var lateWindows = All("u", Domain("R"), All("L", Domain("R"),
            Imp(And(Le(threshold, u), And(Lt(zero, width), Lt(width, widthThreshold))),
                Le(remainder, bound))));
        var estimate = Exists("K", Domain("R"), And(Lt(zero, constant),
            All("e", Domain("R"), Imp(Lt(zero, error),
                Exists("H", Domain("R"), And(Lt(zero, widthThreshold), lateWindows))))));
        var orders = All("m", Domain("N"), All("r", Domain("N"),
            Imp(And(Le(Num(2), m), Equal(Add(m, Num(1)), Multiply(Num(2), r))),
                And(exactAverage, estimate))));
        return F.Disp(Imp(Id("RH"),
            Exists("U", Domain("R"), And(Lt(zero, threshold), orders))));
    }
}

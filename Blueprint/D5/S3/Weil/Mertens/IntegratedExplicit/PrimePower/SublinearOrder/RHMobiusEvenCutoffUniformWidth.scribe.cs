using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder;

internal sealed class RHMobiusEvenCutoffUniformWidthDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffUniformWidth";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A width-uniform error estimate at each tested frequency",
        H("Fourier recovery at every positive logarithmic width"),
        Blocks(Describe.Lean(DescribeId.Create("signed-window-even-cutoff-fourier-uniform-width"),
            DeclarationHandle.Create(Owner + ".signed_window_even_cutoff_fourier_uniform_width"),
            H("The error constant can be chosen before the width"),
            StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Use q=m+1=2r, s=1/2−1/q and c(m)=μ(q)q/(m s). "
                    + "The original signed residual at exp(u), exp(u+L) is divided by their power gap "
                    + "and multiplied by exp(−iwu). Avg is its interval mean over [U,U+T], and "
                    + "Integrable asserts Lebesgue integrability on that interval.")),
                Paragraph(Text("Let ω(ρ,r)=Im(ρ)/r. The contribution W(r,L,ρ) is "
                    + "2r²/[ρ(r−ρ)(r−2ρ)] times (exp((−s+iω(ρ,r))L)−1)/(1−exp(−sL)). "
                    + "A(m,r,L,w) is −μ(r) times the sum over all occurrences with ω(ρ,r)=w, "
                    + "with −c(m) added at w=0. Mult is the analytic order of the zero.")),
                Paragraph(Text("The width multiplier has modulus at most 1+|ω(ρ,r)|/s for every L>0. "
                    + "Split its numerator at exp(−sL) and use the bound on the complex phase "
                    + "increment together with L exp(−sL)/(1−exp(−sL))≤1/s. "
                    + "The modulus of the root exponent absorbs the extra frequency factor. "
                    + "The resulting coefficient majorant is summable and independent of L. "
                    + "The Fourier error is bounded by a term independent of L plus a multiple of "
                    + "the norm sum, all divided by T."))),
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
        var l = Id("L");
        var w = Id("w");
        var u = Id("U");
        var t = Id("T");
        var a = Id("B");
        var c = Id("C");
        var z = Id("z");
        var zero = Num(0);
        var target = Call("A", m, r, l, w);
        var error = Le(new Formula.Norm(Subtract(Call("Avg", m, l, w, u, t), target)),
            new Formula.Fraction(c, t));
        var averages = All("U", Domain("R"), All("T", Domain("R"),
            Imp(And(Le(a, u), Lt(zero, t)),
                And(Call("Integrable", m, l, w, u, t), error))));
        var estimates = All("w", Domain("R"), Exists("C", Domain("R"),
            And(Lt(zero, c), All("L", Domain("R"), Imp(Lt(zero, l), averages)))));
        var zeroMode = Equal(Call("A", m, r, l, zero), new Formula.Negate(Call("c", m)));
        var factor = Call("W", r, l, z);
        var order = Multiply(Multiply(new Formula.Negate(Call("mu", r)), Call("Mult", z)), factor);
        var zeros = All("z", Domain("C"), Imp(Call("Nontrivial", z),
            And(Equal(Call("A", m, r, l, Call("omega", z, r)), order), NotEqual(factor, zero))));
        var widths = All("L", Domain("R"), Imp(Lt(zero, l), And(zeroMode, zeros)));
        var orders = All("m", Domain("N"), All("r", Domain("N"),
            Imp(And(Le(Num(2), m), Equal(Add(m, Num(1)), Multiply(Num(2), r))),
                And(estimates, widths))));
        return F.Disp(Imp(Id("RH"), Exists("B", Domain("R"), And(Lt(zero, a), orders))));
    }
}

using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder;

internal sealed class RHMobiusEvenCutoffFourierResolutionDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffFourierResolution";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Frequency offsets of order one over the averaging length",
        H("Finite averaging resolution of the signed prime window"),
        Blocks(Describe.Lean(DescribeId.Create("signed-window-even-cutoff-detuned-fourier"),
            DeclarationHandle.Create(Owner + ".signed_window_even_cutoff_detuned_fourier"),
            H("The unit interval Fourier profile"),
            StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Use q=m+1=2r, s=1/2−1/q and c(m)=μ(q)q/(m s). "
                    + "Divide the original signed residual at exp(u), exp(u+L) by their power gap. "
                    + "Multiply it by exp(−iwu) and exp(−iv(u−U)/T). Avg is the interval mean "
                    + "of this function over [U,U+T], and Integrable asserts its Lebesgue integrability.")),
                Paragraph(Text("A(m,r,L,w) is the fixed-frequency coefficient. Its zero mode is "
                    + "−c(m). For nonzero w it is −μ(r) times the sum of W(r,L,ρ) over all occurrences "
                    + "with frequency ω(ρ,r)=Im(ρ)/r equal to w. The contribution W(r,L,ρ) is "
                    + "2r²/[ρ(r−ρ)(r−2ρ)] times (exp((−s+iω(ρ,r))L)−1)/(1−exp(−sL)). "
                    + "Mult is analytic order. The profile K(v) is the integral of exp(−ivt) "
                    + "over [0,1].")),
                Paragraph(Text("The uniform-width Fourier estimate bounds the integral of the "
                    + "modulated residual minus its coefficient on every prefix starting at U. "
                    + "Apply the scalar weighted-primitive bound to the real and imaginary "
                    + "coordinate products. The new phase has modulus one and derivative norm "
                    + "|v|/T. Substituting u=U+Tt in the constant contribution gives K(v). "
                    + "The coefficient identities follow from the uniform-width theorem."))),
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
        var v = Id("v");
        var bound = Id("R");
        var target = Multiply(Call("A", m, r, l, w), Call("K", v));
        var error = Le(new Formula.Norm(Subtract(Call("Avg", m, l, w, u, t, v), target)),
            new Formula.Fraction(Multiply(c, Add(Num(1), bound)), t));
        var offsets = All("R", Domain("R"), All("v", Domain("R"),
            Imp(And(Le(zero, bound), Le(new Formula.Absolute(v), bound)),
                And(Call("Integrable", m, l, w, u, t, v), error))));
        var averages = All("U", Domain("R"), All("T", Domain("R"),
            Imp(And(Le(a, u), Lt(zero, t)), offsets)));
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

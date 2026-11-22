using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder;

internal sealed class RHMobiusEvenCutoffFourierDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffFourier";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fourier coefficients of the even-cutoff signed prime window",
        H("Recovering zeta zero frequencies and multiplicities"),
        Blocks(Describe.Lean(DescribeId.Create("signed-window-even-cutoff-fourier"),
            DeclarationHandle.Create(Owner + ".signed_window_even_cutoff_fourier"),
            H("Quantitative coefficient recovery"),
            StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Write q=m+1=2r and s=1/2−1/q. Let c(m)=μ(q)q/(m s), and let "
                    + "ω(ρ,r)=Im(ρ)/r. The function with integral Avg(m,L,w,U,T) times T is the "
                    + "original signed residual at endpoints exp(u), exp(u+L), divided by their "
                    + "power gap and multiplied by exp(−iwu). Integrable denotes Lebesgue "
                    + "interval integrability on [U,U+T].")),
                Paragraph(Text("The factor W(r,L,ρ) is 2r² divided by ρ(r−ρ)(r−2ρ), multiplied "
                    + "by (exp((−s+iω(ρ,r))L)−1)/(1−exp(−sL)). The target A(m,r,L,w) is the sum "
                    + "of these factors over actual zero occurrences with ω(ρ,r)=w, scaled by −μ(r). "
                    + "At w=0 add the arithmetic constant −c(m). Nontrivial(ρ) means a nontrivial "
                    + "zeta zero and Mult(ρ) is its analytic order of vanishing.")),
                Paragraph(Text("Conjugation of the actual zero occurrences makes the normalized "
                    + "root series real. After multiplication by exp(−iwu), all frequencies "
                    + "outside the matching fiber have positive separation from zero. The closed discrete "
                    + "zero set gives this separation after the matching point is removed. "
                    + "Termwise integration of the absolutely summable series bounds the contribution "
                    + "outside the fiber independently of U and T. The normalized arithmetic remainder "
                    + "has an integrable exponential bound. At an actual zero, the whole fiber "
                    + "consists of exactly its analytic number of occurrences. The modulus of the "
                    + "exponential in the numerator of the width factor is exp(−sL)<1."))),
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
            And(Lt(zero, c), averages)));
        var zeroMode = Equal(Call("A", m, r, l, zero), new Formula.Negate(Call("c", m)));
        var factor = Call("W", r, l, z);
        var order = Multiply(Multiply(new Formula.Negate(Call("mu", r)), Call("Mult", z)), factor);
        var zeros = All("z", Domain("C"), Imp(Call("Nontrivial", z),
            And(Equal(Call("A", m, r, l, Call("omega", z, r)), order), NotEqual(factor, zero))));
        var widths = All("L", Domain("R"), Imp(Lt(zero, l),
            And(estimates, And(zeroMode, zeros))));
        var orders = All("m", Domain("N"), All("r", Domain("N"),
            Imp(And(Le(Num(2), m), Equal(Add(m, Num(1)), Multiply(Num(2), r))), widths)));
        return F.Disp(Imp(Id("RH"), Exists("B", Domain("R"), And(Lt(zero, a), orders))));
    }
}

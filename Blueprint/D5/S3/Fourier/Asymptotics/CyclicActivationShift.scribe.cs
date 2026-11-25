using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class CyclicActivationShiftDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Asymptotics/CyclicActivationShift";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The front support changes at one parity-dependent budget near each positive lattice activation.",
        H("Displacement of a cyclic activation threshold"),
        Blocks(
            Describe.Lean(DescribeId.Create("cyclic-activation-shift"),
                DeclarationHandle.Create(Owner + ".cyclic_activation_shift"),
                H("The switch, its coefficient, and the support on both sides"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix an integer n≥2 and a parity. The moduli q are 2k+2 in the even case " +
                        "and 2k+1 in the odd case. Write h=2π/q and m₀=(n²−1)/5, and take d=0 " +
                        "or d=1/2 respectively. There are a fixed ε>0 and switch budgets r(k) " +
                        "whose shift in units h² has the displayed limit as k tends to infinity.")),
                    Paragraph(Text(
                        "For all sufficiently large k, the budget r(k) belongs to (m₀−ε,m₀+ε). " +
                        "For every m in the closed ε-neighborhood of m₀, with moment floor θ=1−2mh², " +
                        "there is a feasible law v attaining both floors. Its squared mass is " +
                        "strictly smaller than that of every other feasible law. The support " +
                        "display uses the absolute value of the centered representative j and " +
                        "c_min, the sampled first cosine at floor(q/2). The boundary pair ±n " +
                        "enters only when m exceeds r(k).")),
                    Paragraph(Text(
                        "On the inclusive front window and nearest antipodal sites, the moment " +
                        "solve is affine in m. The boundary reading has positive limiting slope. " +
                        "The shift is the negative ratio of its mesh-squared variation to that slope. " +
                        "The front fourth moment equals (n²−1)(3n²−5)/35. The total antipodal " +
                        "variation equals 3m₀/4 and its squared offset is d².")),
                    Paragraph(Text(
                        "At the switch the vanishing boundary readings allow the same fit on " +
                        "both windows. The bounding excluded cosine levels have strict negative " +
                        "signs, which extend by convexity to the complement. Interpolating the " +
                        "switch certificate with fixed certified budgets on the two sides gives " +
                        "the optimizer throughout the neighborhood."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var n = F.Id("n");
        var d = F.Id("d");
        var h = F.Id("h");
        var m = F.Id("m");
        var m0 = new Formula.Subscript(m, F.D(0));
        var n2 = new Formula.Power(n, F.D(2));
        var d2 = new Formula.Power(d, F.D(2));
        var q = F.Id("q");
        var v = F.Id("v");
        var i = F.Id("i");
        var absJ = Call("Abs", Call("Centered", i));
        var r = Call("r", F.Id("k"));
        var cMin = Call("AntipodalCosine", q);
        var threshold = Subtract(F.D(1), Multiply(Multiply(F.D(2), m),
            new Formula.Power(h, F.D(2))));
        var coefficient = new Formula.Fraction(
            Multiply(Subtract(n2, F.D(1)),
                Subtract(Add(Multiply(F.Seq(F.D(6), F.D(3)), d2), F.Seq(F.D(4), F.D(7))), Multiply(F.Seq(F.D(3), F.D(1)), n2))),
            F.Seq(F.D(4), F.D(2), F.D(0)));
        var scaled = new Formula.Fraction(Subtract(r, m0), new Formula.Power(h, F.D(2)));
        var support = new Formula.Logic(Lt(F.D(0), Call("PositivePart", Call("v", i))),
            FormulaLogicOperator.Iff,
            new Formula.Logic(Lt(absJ, n), FormulaLogicOperator.Or,
                new Formula.Logic(And(Lt(r, m), Eq(absJ, n)), FormulaLogicOperator.Or,
                    Eq(Call("c", i), cMin))));
        var moments = And(Eq(Call("M", F.D(1), v), threshold), Eq(Call("M", F.D(2), v), threshold));
        return F.Disp(And(Eq(Call("Limit", scaled), coefficient),
            And(Call("Feasible", q, threshold, v), And(moments, support))));
    }
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);

    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);

    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
}

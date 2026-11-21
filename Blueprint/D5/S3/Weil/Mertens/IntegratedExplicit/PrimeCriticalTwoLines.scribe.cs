using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class PrimeCriticalTwoLinesDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Weil/Mertens/IntegratedExplicit/PrimeCriticalTwoLines.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two-line approximation and joint contacts of the prime tail",
        H("Subleading zeta phases in critical-width windows"),
        Blocks(
            Describe.Lean(DescribeId.Create("prime-tail-two-line-approx"),
                DeclarationHandle.Create(Module + "prime_tail_two_line_approx"),
                H("Approximation after exact removal of the upper line"),
                StatementSource.FromAuthor(F.Disp(TwoLineApproximation())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/zhao2025mertensmeans")),
                Blocks(
                    Paragraph(Text(
                        "Write Qϑ for primeTail and Fα(h,u) for the signed line profile "
                        + "phaseProfile Re α h u. The phase φ(t) runs over the actual "
                        + "simultaneous zeta-zero occurrences, counted with multiplicity.")),
                    Paragraph(Text(
                        "The unaveraged integrated explicit formula splits the complete zero series "
                        + "into the β-line and its exact remainder. On the removed line set the "
                        + "coefficients and replacement coordinates to zero. All remaining coordinates "
                        + "then have real part at most γ. Their γ-line projection agrees termwise "
                        + "with the original projection because γ<β.")),
                    Paragraph(Text(
                        "At the γ scale the full β-line contribution is exp((β−γ)t)·Fβ(φ(t),0). "
                        + "After its exact subtraction, the maximal-real-part projection gives "
                        + "Fγ(φ(t),0) plus a term tending to zero. The elementary explicit-formula "
                        + "correction and the prime-power error both tend to zero at the same scale. "
                        + "The prime-only arithmetic input is Zhao's equation (14).")),
                    Paragraph(Text(
                        "The critical strip gives a closed instance at β=2 and γ=1, with both "
                        + "line cuts empty. The line bounds may be attained or unattained."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("prime-tail-negative-windows-of-two-line-contact"),
                DeclarationHandle.Create(Module + "prime_tail_negative_windows_of_two_line_contact"),
                H("Uniform negative points and positive window mass"),
                StatementSource.FromAuthor(F.Disp(ContactTransfer())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let N(A,B) be the integral of max(−Qϑ(x),0)/√x from A to B. "
                        + "Let H be the closure of the actual simultaneous phase orbit φ. At width W>0, "
                        + "a contact is a pair (h,s) in H×[0,W] where Fβ(h,−s)=0 and the "
                        + "whole first profile is nonnegative over the lag interval. Assume "
                        + "Fγ(h,−s)<0 at every such pair.")),
                    Paragraph(Text(
                        "The first profile must take a nonpositive value in each phase window. "
                        + "This holds if every wider window has nonzero lower limit of the normalized "
                        + "mass. Indeed, a phase strictly positive throughout [0,W] stays positive "
                        + "after a short extension at lag W. Its extended phase window has zero mass. "
                        + "The fixed-width cluster theorem gives an actual cluster value of zero "
                        + "for that wider width, hence a zero lower limit by eventual nonnegativity.")),
                    Paragraph(Text(
                        "The first-profile minimizers form a compact graph in H×[0,W]. The graph is "
                        + "cut out by the closed comparison inequalities with every other lag. "
                        + "At a minimizing pair, Fβ≤0, and equality activates the strict contact "
                        + "condition. The maximum of min(Fβ,Fγ) on the graph is therefore −d<0. "
                        + "The same graph supplies a finite upper bound for Fγ.")),
                    Paragraph(Text(
                        "Apply this graph estimate at φ(t) and put u=t−s at the chosen minimizing lag. "
                        + "If Fβ≤−d, the growing factor exp((β−γ)u) makes it dominate the upper bound "
                        + "for Fγ. If Fγ≤−d, the leading term is nonpositive. As u≥t−W, one threshold "
                        + "makes the γ-scale approximation error smaller than d/2 throughout all later "
                        + "windows. Thus there is a point in each such window with γ-normalized tail "
                        + "at most −d/2. Continuity of the tail makes the negative-part integral "
                        + "positive even when the selected point is an endpoint.")),
                    Paragraph(Text(
                        "At an attained maximal real part β>1/2, the critical-width theorem "
                        + "supplies exactly the wider-width premise at W=W*. Thus arbitrarily late "
                        + "zero-mass critical windows force a joint contact with Fγ≥0. The "
                        + "arithmetic gap and the joint contact sign remain hypotheses."))),
                DescribeRole.Theorem))));

    private static Formula Real => F.Seq(F.Mathbb, F.Grp(F.Id("R")));
    private static Formula Complex => F.Seq(F.Mathbb, F.Grp(F.Id("C")));
    private static Formula Half => new Formula.Fraction(F.D(1), F.D(2));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Lt(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Le(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Implies(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Parens(Formula x) => F.Seq(F.Open, x, F.Close);
    private static Formula Neg(Formula x) => new Formula.Negate(x);

    private static Formula SpectralBounds(Formula beta, Formula gamma)
    {
        var z = F.Id("z");
        var maximal = All("z", Complex, Implies(Call("NontrivialZero", z), Le(Call("Re", z), beta)));
        var remaining = All("z", Complex, Implies(
            And(Call("NontrivialZero", z), Lt(Call("Re", z), beta)), Le(Call("Re", z), gamma)));
        return And(And(Lt(Half, gamma), Lt(gamma, beta)), And(Parens(maximal), Parens(remaining)));
    }

    private static Formula NormalizedTail(Formula gamma, Formula u) =>
        Multiply(Call("exp", Multiply(Parens(Subtract(F.D(1), gamma)), u)),
            Call("Qtheta", Call("exp", u)));

    private static Formula AtInfinity(string kind, Formula variable, Formula body) =>
        F.Seq(F.Operatorname, F.Grp(F.Id(kind)), F.Underscore,
            F.Grp(F.Seq(variable, F.Sp, F.To, F.Sp, F.Plus, F.Infty)), F.Sp, body);

    private static Formula TwoLineApproximation()
    {
        var beta = F.Id("beta");
        var gamma = F.Id("gamma");
        var t = F.Id("t");
        var top = Multiply(Call("exp", Multiply(Parens(Subtract(beta, gamma)), t)),
            Call("F", beta, Call("phi", t), F.D(0)));
        var lower = Call("F", gamma, Call("phi", t), F.D(0));
        var residual = Subtract(Subtract(NormalizedTail(gamma, t), top), lower);
        return All("beta", Real, All("gamma", Real, Implies(
            Parens(SpectralBounds(beta, gamma)), Equal(AtInfinity("lim", t, Parens(residual)), F.D(0)))));
    }

    private static Formula ContactTransfer()
    {
        var beta = F.Id("beta");
        var gamma = F.Id("gamma");
        var width = F.Id("W");
        var largerWidth = F.Id("V");
        var right = F.Id("B");
        var h = F.Id("h");
        var s = F.Id("s");
        var v = F.Id("v");
        var c = F.Id("c");
        var threshold = F.Id("T");
        var t = F.Id("t");
        var u = F.Id("u");
        var zero = F.D(0);
        var phases = F.Id("H");
        var lags = Call("Icc", zero, width);
        var upperProfile = Call("F", beta, h, Neg(s));
        var lowerProfile = Call("F", gamma, h, Neg(s));
        var nonpositivePoint = All("h", phases, Exists("s", lags, Le(upperProfile, zero)));
        var widerMass = new Formula.Fraction(
            Call("N", Multiply(right, Call("exp", Neg(largerWidth))), right),
            new Formula.Power(right, Subtract(beta, Half)));
        var widerCutoff = All("V", Real, Implies(Lt(width, largerWidth),
            new Formula.Relation(AtInfinity("liminf", right, widerMass), FormulaRelationOperator.NotEqual, zero)));
        var widthPremise = new Formula.Logic(Parens(nonpositivePoint), FormulaLogicOperator.Or,
            Parens(widerCutoff));
        var contact = All("h", phases, All("s", lags, Implies(
            And(Equal(upperProfile, zero),
                Parens(All("v", lags, Le(zero, Call("F", beta, h, Neg(v)))))),
            Lt(lowerProfile, zero))));
        var sameWindow = Exists("u", Call("Icc", Subtract(t, width), t),
            Le(NormalizedTail(gamma, u), Neg(c)));
        var mass = Call("N", Multiply(Call("exp", t), Call("exp", Neg(width))), Call("exp", t));
        var lateWindows = All("t", Real, Implies(Le(threshold, t),
            And(Parens(sameWindow), Lt(zero, mass))));
        var conclusion = Exists("c", Real, And(Lt(zero, c), Parens(Exists("T", Real, lateWindows))));
        return All("beta", Real, All("gamma", Real, All("W", Real,
            Implies(Parens(And(Lt(zero, width), SpectralBounds(beta, gamma))),
                Implies(Parens(widthPremise), Implies(Parens(contact), conclusion))))));
    }
}

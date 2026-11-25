using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class PrimeAttainedCriticalWidthDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Critical width for prime-tail negative mass",
        H("Critical width at an attained zeta abscissa"),
        Blocks(Describe.Lean(
            DescribeId.Create("prime-tail-zero-liminf-iff-le-critical-width"),
            DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/"
                + "PrimeAttainedCriticalWidth.prime_tail_zero_liminf_iff_le_critical_width"),
            H("The zero set of the lower mass limit"),
            StatementSource.FromAuthor(F.Disp(Claim())),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/zhao2025mertensmeans")),
            Blocks(
                Paragraph(Text("Let θ(u) sum log q over the primes q≤u. Write Qθ(x) for the "
                    + "integral of (θ(u)−u)/u² over u>x, the tail in Zhao's equation (14). "
                    + "Let N(A,B) be the integral of max(−Qθ(x),0)/√x from A to B. "
                    + "For a nontrivial zeta zero ρ attaining the largest real part β>1/2, "
                    + "set p=β−1/2 and M_W(B)=N(B exp(−W),B)/B^p for real W≥0. "
                    + "The lower limit a(W) is taken through real B→+∞.")),
                Paragraph(Text("The normalized complete tail is approximated by the real "
                    + "part of the maximal-line series with a minus sign. The series is bounded "
                    + "by the sum of the coefficient norms, and the normalized prime-power "
                    + "correction tends to zero. Thus some C>0 bounds |x^(1−β) Qθ(x)| "
                    + "for all sufficiently large x, and the integrand of N is at most "
                    + "C x^(p−1) there.")),
                Paragraph(Text("For fixed 0≤U≤W and sufficiently large B, the two windows "
                    + "differ by the segment from B exp(−W) to B exp(−U). Integrating the power "
                    + "bound on that segment gives 0≤M_W(B)−M_U(B)≤(C/p)(exp(−pU)−exp(−pW))"
                    + "≤C(W−U), with C independent of U and W. Taking U=0 also bounds each "
                    + "late normalized mass by C/p. The corresponding lower limits satisfy "
                    + "0≤a(W)−a(U)≤C(W−U).")),
                Paragraph(Text("Recurring positive prime-tail windows give a positive width "
                    + "where a vanishes. The fixed-ratio lower bound at exponent p gives a finite "
                    + "width where a is positive. Monotonicity bounds the zero set from above, "
                    + "and the width estimate makes a vanish at its supremum W*. Thus the zero "
                    + "set is exactly [0,W*]. At W* the normalized mass is arbitrarily small "
                    + "on arbitrarily late windows. The value of W* and the occurrence of an "
                    + "exact zero-mass window there remain open.")),
                Paragraph(Text("Kaczorowski and Ramaré discuss the translation hull in the "
                    + "uniform norm in §4, pp. 289–290 (DOI 10.4064/aa106-3-6). Lee et al., "
                    + "Appendix A.2 (arXiv:1907.07017), connect hull compactness, relatively "
                    + "dense almost periods, and the Bohr compactification. Eremenko and Novikov "
                    + "study sign-change density for functions with a spectral gap "
                    + "(DOI 10.1073/pnas.0302874101). The estimate here integrates the "
                    + "weighted prime-tail negative part over the segment added by widening."))),
            DescribeRole.Theorem))));

    private static Formula Field(string name) => F.Seq(F.Mathbb, F.Grp(F.Id(name)));

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula Le(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);

    private static Formula Lt(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThan, y);

    private static Formula Implies(Formula p, Formula q) => new Formula.Logic(p, FormulaLogicOperator.Implies, q);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula Claim()
    {
        var real = Field("R");
        var complex = Field("C");
        var rho = F.Id("rho");
        var z = F.Id("z");
        var beta = Call("Re", rho);
        var half = new Formula.Fraction(F.D(1), F.D(2));
        var maximal = All("z", complex, Implies(Call("NontrivialZero", z), Le(Call("Re", z), beta)));
        var width = F.Id("W");
        var cutoff = new Formula.Power(width, F.Star);
        var right = F.Id("B");
        var left = Multiply(right, Call("exp", F.Seq(F.Minus, width)));
        var mass = new Formula.Fraction(Call("N", left, right),
            new Formula.Power(right, Subtract(beta, half)));
        var limit = F.Seq(F.Operatorname, F.Grp(F.Id("liminf")), F.Underscore,
            F.Grp(F.Seq(right, F.Sp, F.InMacro, F.Sp, real, F.Comma, F.Sp, right, F.Sp, F.To, F.Sp,
                F.Plus, F.Infty)), F.Sp, mass);
        var iff = new Formula.Logic(Equal(limit, F.D(0)), FormulaLogicOperator.Iff, Le(width, cutoff));
        var property = new Formula.Logic(Lt(F.D(0), cutoff), FormulaLogicOperator.And,
            All("W", real, Implies(Le(F.D(0), width), iff)));
        var unique = F.Seq(F.Exists, F.Bang, F.Sp, cutoff, F.Colon, F.Sp, real, F.Comma, F.Sp, property);
        return All("rho", complex, Implies(Call("NontrivialZero", rho),
            Implies(Lt(half, beta), Implies(maximal, unique))));
    }
}

using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class PrimePrescribedRatioWindowMassDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime-tail negative mass on prescribed-ratio windows",
        H("An unattained zeta abscissa"),
        Blocks(Describe.Lean(
            DescribeId.Create("prime-tail-prescribed-ratio-mass-of-unattained"),
            DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/"
                + "PrimePrescribedRatioWindowMass.prime_tail_prescribed_ratio_mass_of_unattained"),
            H("Every prescribed ratio and every strict surplus exponent"),
            StatementSource.FromAuthor(F.Disp(Claim())),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/zhao2025mertensmeans")),
            Blocks(
                Paragraph(Text("Let Θ be the supremum of the real parts of the nontrivial zeros "
                    + "of the Riemann zeta function, and assume every such zero has real part "
                    + "strictly below Θ. The exponent range 1/2 < σ < Θ entails Θ > 1/2. "
                    + "Write Qθ(x) for the integral of (θ(t)−t)/t² above x, as in Zhao's "
                    + "equation (14), and N(A,B) for the integral of max(−Qθ(x),0)/√x from A to B.")),
                Paragraph(Text("For the prescribed ratio κ, set W=log κ and h=W/2. Choose a "
                    + "probability filter supported on [0,h] that retains a conjugate pair with "
                    + "real part β and positive ordinate γ > 4π/h. Its other surviving zeros "
                    + "have real parts at most b, with σ ≤ b < β. If P=2π/γ, then h+2P<W.")),
                Paragraph(Text("The negative filtered complete Chebyshev tail has a cosine term "
                    + "with positive amplitude at scale exp((β−1)t). Its error divided by that "
                    + "scale decays with exponent b−β. Every interval [T,T+2P] contains a "
                    + "subinterval of length π/(3γ) on which the cosine is at least one half. "
                    + "For all sufficiently large T, the signed integral over this subinterval "
                    + "is bounded below by a positive constant times exp((β−1)T). "
                    + "Every translate by a point in the filter support lies in [T,T+W]. "
                    + "Exchanging the integrals then bounds the signed average by the "
                    + "unaveraged negative mass of the complete tail on that log interval.")),
                Paragraph(Text("The substitution x=exp(t) and the inequality Qθ≤Q transfer the "
                    + "log mass to the weighted prime-only mass, giving a positive constant "
                    + "times exp((β−1/2)T). With T=log B−W, the interval [exp T,exp(T+W)] "
                    + "is [B/κ,B], which is contained in [A,B] whenever κA≤B. The shift of "
                    + "the log endpoint changes only the constant. Since B≥1 and β>σ, "
                    + "the power B^(β−1/2) is at least B^(σ−1/2). "
                    + "The resulting coefficient and cutoff are chosen before either endpoint."))),
            DescribeRole.Theorem))));

    private static Formula Field(string name) => F.Seq(F.Mathbb, F.Grp(F.Id(name)));

    private static Formula Bind(FormulaQuantifier quantifier, string name, Formula domain, Formula body) =>
        new Formula.Bind(quantifier, FormulaIdentifier.Create(name), domain, body);

    private static Formula Le(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);

    private static Formula Lt(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThan, y);

    private static Formula Implies(Formula p, Formula q) => new Formula.Logic(p, FormulaLogicOperator.Implies, q);

    private static Formula And(Formula p, Formula q) => new Formula.Logic(p, FormulaLogicOperator.And, q);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula Claim()
    {
        var rho = F.Id("rho");
        var theta = F.Id("Theta");
        var sigma = F.Id("sigma");
        var half = new Formula.Fraction(F.D(1), F.D(2));
        var a = F.Id("A");
        var b = F.Id("B");
        var ratio = F.Id("kappa");
        var c = F.Id("c");
        var threshold = F.Id("S");
        var real = Field("R");
        var unattained = Bind(FormulaQuantifier.ForAll, "rho", Field("C"),
            Implies(Call("NontrivialZero", rho), Lt(Call("Re", rho), theta)));
        var estimate = Le(Multiply(c, new Formula.Power(b, Subtract(sigma, half))), Call("N", a, b));
        var endpoints = Bind(FormulaQuantifier.ForAll, "B", real, Implies(Le(threshold, b),
            Bind(FormulaQuantifier.ForAll, "A", real, Implies(Le(F.D(2), a),
                Implies(Le(Multiply(ratio, a), b), estimate)))));
        var constants = Bind(FormulaQuantifier.Exists, "c", real,
            Bind(FormulaQuantifier.Exists, "S", real, And(Lt(F.D(0), c), endpoints)));
        return Implies(unattained,
            Bind(FormulaQuantifier.ForAll, "kappa", real,
                Bind(FormulaQuantifier.ForAll, "sigma", real,
                    Implies(Lt(F.D(1), ratio), Implies(Lt(half, sigma),
                        Implies(Lt(sigma, theta), constants))))));
    }
}

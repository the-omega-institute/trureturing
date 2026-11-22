using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class PrimeFixedRatioWindowMassDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime-tail negative mass on fixed-ratio windows",
        H("A lower bound from each off-line zero"),
        Blocks(Describe.Lean(
            DescribeId.Create("prime-tail-fixed-ratio-mass-of-zero"),
            DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/"
                + "PrimeFixedRatioWindowMass.prime_tail_fixed_ratio_mass_of_zero"),
            H("The exponent of a supplied off-line zero"),
            StatementSource.FromAuthor(F.Disp(Claim())),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/zhao2025mertensmeans")),
            Blocks(
                Paragraph(Text("Let Q be the tail obtained by integrating (ψ(t)−t)/t² above x, "
                    + "and let Qθ be the analogous prime-only tail with θ in place of ψ. "
                    + "Zhao's equation (14) uses this prime-only tail. Define N(A,B) as the integral "
                    + "of max(−Qθ(x),0)/√x from A to B.")),
                Paragraph(Text("For a nontrivial zero with real part β greater than one half, use the "
                    + "positive-ordinate member of its conjugate pair. A compact probability filter "
                    + "retains the pair and suppresses the other zeros to the right of a cutoff "
                    + "strictly between one half and β. The negative filtered tail has a leading "
                    + "cosine at scale exp((β−1)t). The ratio of the error bound to that scale "
                    + "is eventually at most one quarter of the cosine amplitude.")),
                Paragraph(Text("Every two-period log window contains a subinterval of fixed positive "
                    + "length on which the cosine is at least one half. Fubini exchanges the "
                    + "interval integral and the probability average. Every translate of this "
                    + "subinterval lies in the log window enlarged by the filter support. Its "
                    + "signed integral is bounded by the integral of the positive part of the "
                    + "unaveraged negative tail over the enlarged window.")),
                Paragraph(Text("On the enlarged window [T,T+W], the substitution x=exp(t) "
                    + "turns the weight dx/√x into exp(t/2) dt. The signed prime-power comparison "
                    + "gives Qθ≤Q, so the resulting prime-only mass is at least a positive constant "
                    + "times exp((β−1/2)T). Taking T=log B−W and κ=exp W places the window "
                    + "[B/κ,B] inside every admissible [A,B]. The factor from shifting the "
                    + "logarithmic endpoint enters the constant and leaves the exponent β−1/2."))),
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
        var re = Call("Re", rho);
        var half = new Formula.Fraction(F.D(1), F.D(2));
        var a = F.Id("A");
        var b = F.Id("B");
        var ratio = F.Id("kappa");
        var c = F.Id("c");
        var threshold = F.Id("S");
        var real = Field("R");
        var estimate = Le(Multiply(c, new Formula.Power(b, Subtract(re, half))), Call("N", a, b));
        var endpoints = Bind(FormulaQuantifier.ForAll, "B", real, Implies(Le(threshold, b),
            Bind(FormulaQuantifier.ForAll, "A", real, Implies(Le(F.D(2), a),
                Implies(Le(Multiply(ratio, a), b), estimate)))));
        var constants = Bind(FormulaQuantifier.Exists, "kappa", real,
            Bind(FormulaQuantifier.Exists, "c", real,
                Bind(FormulaQuantifier.Exists, "S", real,
                    And(Lt(F.D(1), ratio), And(Lt(F.D(0), c), endpoints)))));
        return Bind(FormulaQuantifier.ForAll, "rho", Field("C"),
            Implies(Call("NontrivialZero", rho), Implies(Lt(half, re), constants)));
    }
}

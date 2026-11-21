using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class PrimeAttainedMassNonconvergenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nonconvergence of normalized prime-tail mass",
        H("Fixed-ratio windows at an attained zeta abscissa"),
        Blocks(Describe.Lean(
            DescribeId.Create("prime-tail-mass-no-finite-limit-of-attained-zero"),
            DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/"
                + "PrimeAttainedMassNonconvergence.prime_tail_mass_no_finite_limit_of_attained_zero"),
            H("Exclusion of every finite limit"),
            StatementSource.FromAuthor(F.Disp(Claim())),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/zhao2025mertensmeans")),
            Blocks(
                Paragraph(Text("Let Qθ(x) integrate (θ(u)−u)/u² over u>x, where θ sums log p "
                    + "once per prime p≤u. This prime-only tail appears in Zhao's equation (14). "
                    + "Define N(A,B) by integrating max(−Qθ(x),0)/√x from A to B. "
                    + "For β=Re ρ and p=β−1/2, put Mκ(B)=N(B/κ,B)/B^p with B real.")),
                Paragraph(Text("Assume Mκ tends to L. The recurring positive-tail windows give "
                    + "a ratio R>1. Take λ=min(κ,R), q=κ^(−p), and r=λ^(−p). "
                    + "The nonnegative density gives 0≤Mλ≤Mκ for sufficiently large B. "
                    + "Splitting [B/(κλ),B] at B/κ and at B/λ gives "
                    + "Mλ(B)−q Mλ(B/κ)=Mκ(B)−r Mκ(B/λ). "
                    + "The right-hand side tends to (1−r)L.")),
                Paragraph(Text("Set C=(1−r)L/(1−q) and e=Mλ−C. The residual "
                    + "e(B)−q e(B/κ) tends to zero, and |e| is eventually bounded by some M. "
                    + "Given ε>0, the residual is eventually bounded in absolute value by "
                    + "ε(1−q)/2. Since B/κ tends to infinity with B, induction gives, "
                    + "for each fixed n and all sufficiently large B, "
                    + "|e(B)|≤q^n M+(ε/2)(1−q^n). Choosing n with q^n M<ε/2 gives Mλ→C.")),
                Paragraph(Text("The recurring zero-mass windows have right endpoints B=λA "
                    + "arbitrarily far out. Thus C=0 and, since r<1, L=0. The lower bound "
                    + "from the supplied zero gives a ratio k and a constant c>0. Choose m "
                    + "with κ^m≥k. Repeated splitting expresses M at ratio κ^m as a sum of "
                    + "the m terms q^j Mκ(B/κ^j) for 0≤j<m, each tending to zero. The lower "
                    + "bound gives M at ratio κ^m at least c for every sufficiently large B, "
                    + "a contradiction.")),
                Paragraph(Text("Bingham and Gashi use a geometric expansion for discrete "
                    + "logarithmic means in Theorem 1 and equations (2.3)–(2.4) of "
                    + "Logarithmic moving averages (arXiv:1408.1301). Here the recurrence "
                    + "comes from interval additivity of the continuous prime-tail mass."))),
            DescribeRole.Theorem))));

    private static Formula Field(string name) => F.Seq(F.Mathbb, F.Grp(F.Id(name)));

    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Implies(Formula p, Formula q) =>
        new Formula.Logic(p, FormulaLogicOperator.Implies, q);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula Claim()
    {
        var real = Field("R");
        var complex = Field("C");
        var rho = F.Id("rho");
        var z = F.Id("z");
        var kappa = F.Id("kappa");
        var limit = F.Id("L");
        var endpoint = F.Id("B");
        var beta = Call("Re", rho);
        var half = new Formula.Fraction(F.D(1), F.D(2));
        var offLine = new Formula.Relation(half, FormulaRelationOperator.LessThan, beta);
        var maximal = ForAll("z", complex, Implies(Call("NontrivialZero", z),
            new Formula.Relation(Call("Re", z), FormulaRelationOperator.LessThanOrEqual, beta)));
        var ratio = new Formula.Relation(F.D(1), FormulaRelationOperator.LessThan, kappa);
        var mass = new Formula.Fraction(
            Call("N", new Formula.Fraction(endpoint, kappa), endpoint),
            new Formula.Power(endpoint, Subtract(beta, half)));
        var function = F.Seq(F.Open, F.LambdaLower, F.Sp, endpoint, F.Colon, real, F.Sp,
            F.Mapsto, F.Sp, mass, F.Close);
        var excluded = F.Seq(F.Neg, F.Sp, Call("Tendsto", function, F.Id("atTop"), Call("nhds", limit)));
        return ForAll("rho", complex, Implies(Call("NontrivialZero", rho),
            Implies(offLine, Implies(maximal,
                ForAll("kappa", real, ForAll("L", real, Implies(ratio, excluded)))))));
    }
}

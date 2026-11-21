using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class PrimeUnattainedEndpointMassDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime-tail negative mass at an unattained zeta abscissa",
        H("The endpoint-scale upper bound"),
        Blocks(Describe.Lean(
            DescribeId.Create("prime-tail-endpoint-mass-tendsto-zero"),
            DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/"
                + "PrimeUnattainedEndpointMass.prime_tail_endpoint_mass_tendsto_zero"),
            H("Vanishing normalized mass over all real windows"),
            StatementSource.FromAuthor(F.Disp(Claim())),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/zhao2025mertensmeans")),
            Blocks(
                Paragraph(Text("Let Θ be the supremum of the real parts of the nontrivial zeta "
                    + "zeros. Write Qθ(x) for the integral of (θ(u)−u)/u² over u>x, the tail "
                    + "in Zhao’s equation (14), where θ sums log p once per prime p≤u. "
                    + "Write N(A,B) for the integral of max(−Qθ(x),0)/√x from A to B.")),
                Paragraph(Text("The real part of each actual zero is bounded above by Θ. The "
                    + "normalized complete Chebyshev tail differs from the negative real part "
                    + "of the maximal-line series by a quantity tending to zero. Absolute "
                    + "summability controls the lower terms even when their real parts approach Θ. "
                    + "Strict unattainment makes every maximal-line term zero. The prime-power "
                    + "correction vanishes under the same "
                    + "normalization since Θ>1/2. Substituting t=log x yields "
                    + "x^(1−Θ) Qθ(x)→0 for real x→+∞. This includes Θ=1.")),
                Paragraph(Text("Set p=Θ−1/2>0. For any ε>0, choose X≥2 such that the mass "
                    + "integrand is at most (ε/2)p x^(p−1) for x≥X. For B≥X, integrating this "
                    + "power bounds N(X,B) by (ε/2)(B^p−X^p). The fixed initial mass N(2,X) "
                    + "divided by B^p tends to zero. Nonnegativity then gives the limit.")),
                Paragraph(Text("For each B≥2, nonnegativity also makes N(2,B)/B^p the maximum "
                    + "of N(A,B)/B^p over all real A with 2≤A≤B. The same cutoff in B controls "
                    + "all such A, including every window ratio."))),
            DescribeRole.Theorem))));

    private static Formula Field(string name) => F.Seq(F.Mathbb, F.Grp(F.Id(name)));

    private static Formula Lt(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThan, y);

    private static Formula Implies(Formula p, Formula q) =>
        new Formula.Logic(p, FormulaLogicOperator.Implies, q);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula Claim()
    {
        var rho = F.Id("rho");
        var theta = F.Id("Theta");
        var right = F.Id("B");
        var two = F.D(2);
        var half = new Formula.Fraction(F.D(1), two);
        var unattained = new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("rho"),
            Field("C"), Implies(Call("NontrivialZero", rho), Lt(Call("Re", rho), theta)));
        var ratio = new Formula.Fraction(Call("N", two, right),
            new Formula.Power(right, Subtract(theta, half)));
        var normalizedMass = F.Seq(F.Open, F.LambdaLower, F.Sp, right, F.Colon, Field("R"),
            F.Sp, F.Mapsto, F.Sp, ratio, F.Close);
        var limit = Call("Tendsto", normalizedMass, F.Id("atTop"), Call("nhds", F.D(0)));
        return Implies(Lt(half, theta), Implies(unattained, limit));
    }
}

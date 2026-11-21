using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class RHPrimeWindowMeanDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The logarithmic main term of the prime-only window mass under RH",
        H("The contribution from prime powers"),
        Blocks(Describe.Lean(
            DescribeId.Create("prime-tail-logarithmic-mass-of-rh"),
            DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/"
                + "RHPrimeWindowMean.prime_tail_logarithmic_mass_of_rh"),
            H("A bounded remainder for all real cutoffs"),
            StatementSource.FromAuthor(F.Disp(Claim())), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Write Q for the complete Chebyshev tail and Qθ for the prime-only tail "
                    + "with integrand (θ(t)−t)/t². Write N(a,b) for the integral of "
                    + "max(−Qθ(x),0)/√x on [a,b].")),
                Paragraph(Text("The prime-power bounds compare ψ(x)−θ(x) with ψ(√x). "
                    + "Schoenfeld's estimate under RH, applied at √x, yields a bound O(x^(5/12)) "
                    + "for ψ(x)−θ(x)−√x. Tail integration therefore gives "
                    + "√x(Q(x)−Qθ(x))=2+O(x^(−1/12)). The error is integrable with respect to dx/x.")),
                Paragraph(Text("In logarithmic coordinates the complete normalized remainder is the real "
                    + "part of the normalized zero series plus an exponentially damped correction. "
                    + "All zeros contributing to that series lie on the critical line under RH. "
                    + "The phases have absolute ordinates greater than ten, so the integral of each mode "
                    + "over any interval is bounded by its coefficient modulus divided by five. "
                    + "Absolute summability gives a bound common to all endpoints.")),
                Paragraph(Text("The normalized zero series has modulus at most two, so adding two "
                    + "keeps its real part nonnegative. The positive-part map is one-Lipschitz. "
                    + "It preserves the integrable error estimate after adding the prime-power bias. "
                    + "Integration leaves the term 2 log(b/a) and a bounded remainder."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula Le(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);

    private static Formula Imp(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.Implies, y);

    private static Formula Claim()
    {
        var a = F.Id("a");
        var b = F.Id("b");
        var c = F.Id("C");
        var real = F.Seq(F.Mathbb, F.Grp(F.Id("R")));
        var mainTerm = Multiply(F.D(2), Call("log", new Formula.Fraction(b, a)));
        var estimate = Le(new Formula.Absolute(Subtract(Call("N", a, b), mainTerm)), c);
        var bounds = new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("a"), real,
            new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("b"), real,
                Imp(Le(F.D(2), a), Imp(Le(a, b), estimate))));
        var existence = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("C"),
            real, new Formula.Logic(Le(F.D(0), c), FormulaLogicOperator.And, bounds));
        return Imp(F.Id("RH"), existence);
    }
}

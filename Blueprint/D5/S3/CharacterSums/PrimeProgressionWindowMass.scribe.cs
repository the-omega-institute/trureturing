using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CharacterSums;

internal sealed class PrimeProgressionWindowMassDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A lower bound for the logarithmic prime mass in every sufficiently large real window",
        H("Prime mass in power windows of a fixed arithmetic progression"),
        Blocks(
            Paragraph(Text("Fix a positive integer m and an invertible residue a modulo m. "
                + "Write W(m,a,T) for the sum of (log p)/p over primes p congruent to a modulo m "
                + "in the interval exp(T/2) < p ≤ exp(T). Write φ(m) for Euler's totient.")),
            Describe.Lean(DescribeId.Create("progression-window-mass"),
                DeclarationHandle.Create("D5/S3/CharacterSums/PrimeProgressionWindowMass.prime_progression_window_mass"),
                H("Lower bound on each sufficiently large real window"),
                StatementSource.FromAuthor(Claim()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every positive integer j, multiply the sum of (log p)/p times "
                        + "p raised to −jh over all primes p congruent to a by h. As h tends to zero "
                        + "from above the result approaches 1/(jφ(m)). This follows from the continuous "
                        + "regular part of the progression's Mangoldt series at one. Higher prime powers "
                        + "have summable total logarithmic weight, so their scaled contribution tends to zero.")),
                    Paragraph(Text("Set t = exp(−log p/T). The polynomial t¹²(1−t)¹²(t−3/8)(3/5−t) "
                        + "is bounded above by the indicator of the window. It is positive only for "
                        + "3/8 < t < 3/5, inside exp(−1) < t < exp(−1/2), and there it is at most one.")),
                    Paragraph(Text("Combining the scaled moments at h = 1/T for degrees 12 through 26 gives "
                        + "the limit 1/(10816624000 φ(m)) for the normalized polynomial sum. The normalized "
                        + "window mass is at least that sum and hence eventually exceeds half its limit. "
                        + "For m = 8 the resulting lower bound is T/86532992000."))), DescribeRole.Theorem))));

    private static Formula Claim()
    {
        var t = F.Id("T");
        var threshold = F.Id("U");
        var reals = F.Seq(F.Mathbb, F.Grp(F.Id("R")));
        var totient = F.Seq(F.Phi, F.Open, F.Id("m"), F.Close);
        var lower = F.Seq(F.Frac, F.Grp(t), F.Grp(Num(21633248000), F.Sp, totient));
        var mass = new Formula.FunctionCall(FormulaIdentifier.Create("W"), [F.Id("m"), F.Id("a"), t]);
        var comparison = new Formula.Relation(lower, FormulaRelationOperator.LessThanOrEqual, mass);
        var large = new Formula.Relation(threshold, FormulaRelationOperator.LessThanOrEqual, t);
        return F.Disp(new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("U"), reals,
            new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("T"), reals,
                new Formula.Logic(large, FormulaLogicOperator.Implies, comparison))));
    }
}

using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens;

internal sealed class MobiusDyadicGrowthLimitDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/Mertens/MobiusDyadicGrowthLimit.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The cumulative limit and individual limsup for the signed Möbius shell energies.",
        H("Logarithmic growth of the signed Möbius shell energies"),
        Blocks(
            Paragraph(Text(
                "In MobiusPartialSumL2Divergence, mobiusPartialSum(x) is the real sum of "
                + "μ(n)/n over the natural numbers from 1 through the natural floor of x, inclusive. "
                + "The function MobiusDyadicEnergy.mobiusDyadicDifference(x) is mobiusPartialSum(x) minus "
                + "mobiusPartialSum(2x). For each natural k, write E(k) for mobiusDyadicShellEnergy(k), "
                + "the real integral of the square of that difference against Lebesgue measure "
                + "on (2^k, 2^(k+1)].")),
            Paragraph(Text(
                "Write θ for KappaGap.zeroAbscissa, the real supremum of the real parts of "
                + "the complex ρ satisfying riemannZeta(ρ) = 0 and 0 < Re(ρ) < 1. "
                + "These are exactly the zeros selected by ZeroSum.IsNontrivialZero. The logarithms "
                + "are natural logarithms. Both sequences are defined on all natural indices, "
                + "and Nat.cast sends the index to ℝ in the denominator. At index zero the quotient "
                + "equals zero by Lean's real division convention.")),
            Describe.Lean(
                DescribeId.Create("cumulative-shell-growth-limit"),
                DeclarationHandle.Create(Prefix + "tendsto_log_one_add_sum_mobiusDyadicShellEnergy"),
                H("Cumulative shell growth limit"),
                StatementSource.FromAuthor(F.Disp(CumulativeStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The prefix sum ranges over exactly the natural indices k with 0 ≤ k < N. "
                        + "The displayed convergence means that for every real ε > 0 there is "
                        + "a natural N₀ such that for every natural N ≥ N₀ the absolute difference "
                        + "between the quotient and 2θ − 1 is less than ε.")),
                    Paragraph(Text(
                        "Every nontrivial zero with real part above 1/2 gives an eventual exponential "
                        + "lower bound for the finite shell sum via the signed energy theorem. For θ < 1, "
                        + "the normalized shell convergence for any exponent between 2θ − 1 and 1 bounds "
                        + "each shell by a geometric sequence. At θ = 1 the elementary bound E(k) ≤ 4·2^k "
                        + "gives the upper exponent. The two estimates give the cumulative limit."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("individual-shell-growth-limsup"),
                DeclarationHandle.Create(Prefix + "limsup_log_one_add_mobiusDyadicShellEnergy"),
                H("Individual shell growth limsup"),
                StatementSource.FromAuthor(F.Disp(IndividualStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every real ε > 0 the individual quotient is less than 2θ − 1 + ε "
                        + "at all sufficiently large natural k. For every real ε > 0 and every "
                        + "natural K there is a natural k ≥ K where it exceeds 2θ − 1 − ε.")),
                    Paragraph(Text(
                        "The nonnegative shells bound the individual numerator by the prefix "
                        + "numerator through k, using the same denominator at k. An eventual "
                        + "upper bound for the individual quotient strictly below 2θ − 1 would "
                        + "give a geometric bound for the prefix sum and contradict the cumulative limit."))),
                DescribeRole.Theorem))));

    private static Formula Natural => F.Seq(F.Mathbb, F.Grp(F.Id("N")));
    private static Formula AtTop => F.Seq(Op("Filter.atTop"), F.Underscore, F.Grp(Natural));
    private static Formula Exponent => new Formula.Binary(
        new Formula.Binary(Num(2), FormulaBinaryOperator.Multiply, F.Theta),
        FormulaBinaryOperator.Subtract, Num(1));

    private static Formula CumulativeStatement()
    {
        var cutoff = F.Id("N");
        var shell = F.Id("k");
        var prefix = F.Seq(F.Sum, F.Underscore,
            F.Grp(shell, F.Sp, F.InMacro, F.Sp, Call("Finset.range", cutoff)),
            F.Sp, Shell(shell));
        return Call("Filter.Tendsto", Sequence(cutoff, Quotient(cutoff, prefix)),
            AtTop, Call("nhds", Exponent));
    }

    private static Formula IndividualStatement()
    {
        var shell = F.Id("k");
        var limsup = Call("Filter.limsup", Sequence(shell, Quotient(shell, Shell(shell))), AtTop);
        return new Formula.Relation(limsup, FormulaRelationOperator.Equal, Exponent);
    }

    private static Formula Sequence(Formula index, Formula body) =>
        F.Seq(F.Open, F.LambdaLower, F.Sp, index, F.Colon, F.Sp, Natural,
            F.Sp, F.Mapsto, F.Sp, body, F.Close);

    private static Formula Quotient(Formula index, Formula energy) => new Formula.Fraction(
        Call("log", new Formula.Binary(Num(1), FormulaBinaryOperator.Add, energy)),
        new Formula.Binary(Call("Nat.cast", index), FormulaBinaryOperator.Multiply, Call("log", Num(2))));

    private static Formula Shell(Formula index) => new Formula.Apply(F.Id("E"), [index]);
    private static Formula Num(long value) => new Formula.Number(value);
    private static Formula Op(string name) => F.Seq(F.Operatorname,
        F.Grp(name.Split('.').SelectMany((part, index) =>
            index == 0 ? new[] { F.Id(part) } : new[] { F.Dot, F.Id(part) }).ToArray()));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Op(name), [.. arguments]);
}

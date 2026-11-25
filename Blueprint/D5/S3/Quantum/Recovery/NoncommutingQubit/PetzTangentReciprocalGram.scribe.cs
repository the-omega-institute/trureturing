using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery.NoncommutingQubit;

internal sealed class PetzTangentReciprocalGramDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two parity sectors of the qubit tangent residual obey the common marginal-dependent reciprocal Gram bound.",
        H("Paired reciprocal Gram bounds for the Petz tangent"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("petztangentreciprocalgram-paired-parity-bound"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/NoncommutingQubit/PetzTangentReciprocalGram.paired_parity_bound"),
                H("Combined reciprocal parity estimate"),
                StatementSource.FromAuthor(ParityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive g, 0<δ≤1, and real β satisfying g²+β²≤1, the displayed estimate holds for arbitrary complex coefficients. For the arcsine functionals, the even coefficients are normalized by 1/x and the odd coefficients by 1/(x(x+g)), for nodes x in {1,δ}. At δ=1, the multiplier equals the sharp uniform value one.")),
                    Paragraph(Text("The unweighted odd Gram splits into a common even lower Gram and a positive correction with unsquared reciprocal nodes. The even estimate uses the square-root chord bound. At coincident nodes, the even diagonal equals one and the unweighted odd diagonal is at least one. Both sector estimates retain the two-node cross terms.")),
                    Paragraph(Text("The physical common-reference tangent application requires the arcsine evaluations and substitution back to the affine spectral variable, followed by identification with the actual arithmetic BKM residual and ordinary Petz sandwich."))),
                DescribeRole.Theorem))));

    private static Formula ParityFormula()
    {
        Formula g = F.Id("g"), delta = F.DeltaLower, beta = F.Beta;
        Formula a = F.Id("a"), b = F.Id("b");
        Formula c = F.Id("c"), d = F.Id("d"), t = F.Id("t");
        Formula one = F.D(1), two = F.D(2);

        Formula Add(Formula x, Formula y) => F.Seq(x, F.Plus, y);
        Formula Mul(Formula x, Formula y) => F.Seq(x, y);
        Formula Par(Formula x) => F.Seq(F.Open, x, F.Close);
        Formula Sq(Formula x) => new Formula.Power(x, two);
        Formula Rat(Formula x, Formula y) => new Formula.Fraction(x, y);
        Formula NormSq(Formula x) => Sq(new Formula.Norm(x));

        Formula weight = F.Seq(F.Sqrt, F.Grp(Add(one, t)));
        Formula left = NormSq(Add(Mul(g, Par(Add(a, b))),
            Mul(beta, Par(Add(c, d)))));
        Formula even = NormSq(Add(Rat(a, Add(one, t)),
            Rat(Mul(b, delta), Add(Sq(delta), t))));
        Formula odd = NormSq(Add(
            Rat(Mul(c, Par(Add(g, one))), Add(one, t)),
            Rat(Mul(Mul(d, delta), Par(Add(g, delta))), Add(Sq(delta), t))));

        Formula Integral(Formula numerator, Formula denominator) =>
            F.Seq(F.Int, F.Underscore, F.Grp(F.D(0)),
                F.Caret, F.Grp(F.Infty),
                Rat(Mul(weight, numerator), denominator),
                F.Thin, F.Mathrm, F.Grp(F.Id("d")), t);

        Formula k = F.Seq(F.Id("K"), Par(delta));
        Formula cases = F.Seq(F.Begin, F.Grp(F.Id("cases")),
            one, F.Amp, delta, F.Eq, one, F.RowBreak,
            Add(one, Rat(two, Add(one, Sq(delta)))),
            F.Amp, delta, F.Neq, one,
            F.End, F.Grp(F.Id("cases")));

        return F.Disp(F.Seq(F.Begin, F.Grp(F.Id("aligned")),
            F.Amp, F.Forall, F.Sp, g, F.Comma, beta, F.Comma, delta,
            F.InMacro, F.Mathbb, F.Grp(F.Id("R")), F.Comma,
            a, F.Comma, b, F.Comma, c, F.Comma, d,
            F.InMacro, F.Mathbb, F.Grp(F.Id("C")), F.RowBreak,
            F.Amp, F.D(0), F.Lt, g, F.Land, F.Sp,
            F.D(0), F.Lt, delta, F.Le, one, F.Land, F.Sp,
            Add(Sq(g), Sq(beta)), F.Le, one,
            F.Rightarrow, F.RowBreak,
            left, F.Amp, F.Le, F.Sp, k, F.OpenBracket,
            Integral(even, two), F.RowBreak,
            F.Amp, F.Quad, F.Plus,
            Integral(odd, Mul(two, Par(Add(Sq(g), t)))),
            F.CloseBracket, F.RowBreak,
            k, F.Amp, F.Eq, cases,
            F.End, F.Grp(F.Id("aligned"))));
    }
}

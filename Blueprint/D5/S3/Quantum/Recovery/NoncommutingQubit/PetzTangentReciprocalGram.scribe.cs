using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery.NoncommutingQubit;

internal sealed class PetzTangentReciprocalGramDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized even and odd scalar reciprocal profiles obey a common node-dependent Gram bound.",
        H("Paired reciprocal Gram bounds for the Petz tangent"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("petztangentreciprocalgram-paired-parity-bound"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/NoncommutingQubit/PetzTangentReciprocalGram.paired_parity_bound"),
                H("Combined reciprocal parity estimate"),
                StatementSource.FromAuthor(ParityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The coefficients are arbitrary complex numbers. For the arcsine functionals, the even coefficients are normalized by 1/x and the odd coefficients by 1/(x(x+g)), for nodes x in {1,δ}. Positivity of g and δ keeps the reciprocal nodes positive for the integral identities and makes both coefficient normalizations invertible. The physical range δ≤1 corresponds to taking the positive ratio of the smaller node to the larger one. In the proof this ordering bounds the cross-entry denominators and gives the square-root chord estimate. The disk condition g²+β²≤1 makes the final linear combination a contraction and gives g≤1 for comparison of the odd kernels.")),
                    Paragraph(Text("The unweighted odd Gram splits into a common even lower Gram and a positive correction with unsquared reciprocal nodes. The cross entries are bounded below by δ in the weighted even and unweighted odd Grams. For real coefficients of the same sign, completing the square gives the rational factor in the displayed maximum. For coefficients of opposite signs, the common even lower Gram gives the factor two. The real estimates apply to the real and imaginary parts of each profile. At δ=1 the even diagonal equals one and the unweighted odd diagonal is at least one. The multiplier one is sharp there.")),
                    Paragraph(
                        Text("The physical entry theorem "),
                        Ref("D5/S3/Quantum/Recovery/NoncommutingQubit/PetzTangentPhysical.physical_entry_arcsine_and_bound"),
                        Text(" uses this bound for a positive joint spectral pair and a faithful qubit marginal. It identifies the entry of the ordinary Petz residual with an arcsine average of the arithmetic BKM residual at the same reference and tangent. "),
                        Ref("D5/S3/Quantum/Recovery/NoncommutingQubit/PetzTangentTraceNorm.faithful_traceNorm_tangent"),
                        Text(" uses the resulting weighted sum to bound the squared full trace norm by the same multiplier times the conditional BKM form for a positive definite joint reference of trace one. The aggregate estimate at a singular reference, including the support and kernel cross terms, and the recovery bound with this multiplier in terms of finite Umegaki entropy loss remain open in this formalization."))),
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
            F.Max, Par(F.Seq(two, F.Comma,
                Rat(F.Seq(F.D(3), F.Minus, delta), Add(one, delta)))),
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

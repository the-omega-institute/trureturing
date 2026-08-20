using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Naturality;

internal sealed class ApproximateSemiconjugacyErrorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A uniform semiconjugacy defect controls finite-time orbit error by geometric sums.",
        H("Approximate Semiconjugacy Error"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("approximate-semiconjugacy-finite-time-error"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Naturality/ApproximateSemiconjugacyError."
                        + "approximate_semiconjugacy_error"),
                H("Approximate semiconjugacy error"),
                StatementSource.FromAuthor(StatementFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let tau update the concrete state space Y, let sigma update the "
                            + "pseudometric space Z, and let pi project concrete states into Z. "
                            + "The nonnegative number L is a Lipschitz constant for sigma, and "
                            + "every one-step semiconjugacy defect is at most delta.")),
                    Paragraph(Text(
                        "For every natural k and state y, the orbit discrepancy is bounded by "
                            + "delta times the finite geometric sum through exponent k minus one. "
                            + "When k is zero, the range and its sum are empty.")),
                    Paragraph(Text(
                        "The same declaration also states both requested specializations. If L "
                            + "is less than one, the error is bounded by delta divided by one "
                            + "minus L. If L equals one, it is bounded by k times delta.")),
                    Paragraph(Text(
                        "The proof applies the frozen uniform output-trajectory theorem with "
                            + "identity readout and zero readout error. Mathlib's nonnegative-real "
                            + "geometric-series sum and the finite sum at L equal to one give the "
                            + "two corollaries."))),
                DescribeRole.Theorem))));

    private static Formula Iterate(Formula map, Formula exponent, Formula state) =>
        Seq(map, Caret, Grp(exponent), Open, state, Close);

    private static Formula Apply(Formula map, Formula state) =>
        Seq(map, Open, state, Close);

    private static Formula Distance(Formula left, Formula right) =>
        Seq(F.Id("d"), Underscore, Grp(F.Id("Z")), Open, left, Comma, Sp, right, Close);

    private static Formula OrbitDistance(Formula k, Formula y) =>
        Distance(
            Apply(Pi, Iterate(Tau, k, y)),
            Iterate(SigmaLower, k, Apply(Pi, y)));

    private static Formula QuantifiedBound(Formula rhs)
    {
        Formula k = F.Id("k");
        Formula y = F.Id("y");
        return Seq(
            Forall, Sp, k, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            Forall, Sp, y, Sp, InMacro, Sp, F.Id("Y"), Comma, Esc,
            OrbitDistance(k, y), Sp, Leq, Sp, rhs);
    }

    private static Formula StatementFormula()
    {
        Formula k = F.Id("k");
        Formula j = F.Id("j");
        Formula y = F.Id("y");
        Formula l = F.Id("L");
        Formula delta = Delta;
        Formula finiteSum = Seq(
            delta, Sp, Sum, Underscore, Grp(Seq(j, Eq, D(0))), Caret,
            Grp(Seq(k, Minus, D(1))), Sp, l, Caret, j);
        Formula mainBound = QuantifiedBound(finiteSum);
        Formula contractiveBound = QuantifiedBound(
            Seq(Frac, Grp(delta), Grp(Seq(D(1), Minus, l))));
        Formula linearBound = QuantifiedBound(Seq(k, Sp, delta));
        Formula oneStepDefect = Distance(
            Apply(Pi, Apply(Tau, y)),
            Apply(SigmaLower, Apply(Pi, y)));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, F.Id("Y"), Comma, Sp, F.Id("Z"), Colon, Sp,
            F.Id("Type"), Comma, RowBreak, Grp(),
            OpenBracket, Operatorname, Grp(F.Id("PseudoMetricSpace")), Sp,
            F.Id("Z"), CloseBracket, Comma, RowBreak,
            Forall, Sp, Tau, Colon, Sp, F.Id("Y"), To, Sp, F.Id("Y"), Comma, Sp,
            SigmaLower, Colon, Sp, F.Id("Z"), To, Sp, F.Id("Z"), Comma, Sp,
            Pi, Colon, Sp, F.Id("Y"), To, Sp, F.Id("Z"), Comma, RowBreak,
            Forall, Sp, l, Comma, Sp, delta, Colon, Sp,
            Operatorname, Grp(F.Id("NNReal")), Comma, RowBreak,
            Open,
            Operatorname, Grp(F.Id("LipschitzWith")), Open, l, Comma, Sp,
            SigmaLower, Close, Sp, Land, Sp,
            Forall, Sp, y, Sp, InMacro, Sp, F.Id("Y"), Comma, Sp,
            oneStepDefect, Sp, Leq, Sp, delta,
            Close, Sp, Rightarrow, RowBreak,
            Open, mainBound, Close, Sp, Land, Sp, RowBreak,
            Open, l, Sp, Lt, Sp, D(1), Sp, Rightarrow, Sp,
            contractiveBound, Close, Sp, Land, Sp, RowBreak,
            Open, l, Sp, Eq, Sp, D(1), Sp, Rightarrow, Sp,
            linearBound, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.AgencyHolonomy;

internal sealed class PrimeSwapCurvatureDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/AgencyHolonomy/PrimeSwapCurvature.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Stable prime-memory swap curvature is gauge invariant.",
        H("Prime Swap Curvature"),
        Blocks(Describe.Lean(
            DescribeId.Create("stable-prime-swap-curvature-specification"),
            DeclarationHandle.Create(Prefix + "prime_swap_curvature_spec"),
            H("Stable prime swap curvature specification"),
            StatementSource.FromAuthor(CurvatureFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Exchanging two lifted prime updates produces a memory defect equal to "
                        + "the swap curvature times the scalar state, while the scalar output "
                        + "is unchanged. Reversing the exchange negates the curvature, and a "
                        + "common shift of memory origin leaves it invariant.")),
                Paragraph(Text(
                    "Under the two stated nonresonance hypotheses, the curvature factors "
                        + "through the difference of the observer-origin estimates. Its "
                        + "vanishing is therefore equivalent to agreement of those estimates; "
                        + "no analytic or zero-location conclusion is asserted."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Update(
        Formula a, Formula injection, Formula localFactor, Formula state) =>
        Call("stablePrimeUpdate", a, injection, localFactor, state);

    private static Formula Curvature(
        Formula a,
        Formula firstInjection,
        Formula firstFactor,
        Formula secondInjection,
        Formula secondFactor) =>
        Call(
            "primeSwapCurvature",
            a,
            firstInjection,
            firstFactor,
            secondInjection,
            secondFactor);

    private static Formula GaugeShift(
        Formula a, Formula localFactor, Formula originShift, Formula injection) =>
        Call("memoryGaugeShift", a, localFactor, originShift, injection);

    private static Formula ObserverOrigin(
        Formula a, Formula localFactor, Formula injection) =>
        Call("observerOrigin", a, localFactor, injection);

    private static Formula CurvatureFormula()
    {
        Formula field = F.Id("K");
        Formula a = F.Id("a");
        Formula bP = new Formula.Subscript(F.Id("b"), F.Id("P"));
        Formula bQ = new Formula.Subscript(F.Id("b"), F.Id("Q"));
        Formula lambdaP = Seq(LambdaLower, Underscore, Grp(F.Id("P")));
        Formula lambdaQ = Seq(LambdaLower, Underscore, Grp(F.Id("Q")));
        Formula originShift = Xi;
        Formula state = F.Id("s");
        Formula pairType = Seq(field, Sp, Times, Sp, field);

        Formula pThenQ = Update(
            a, bQ, lambdaQ, Update(a, bP, lambdaP, state));
        Formula qThenP = Update(
            a, bP, lambdaP, Update(a, bQ, lambdaQ, state));
        Formula curvature = Curvature(a, bP, lambdaP, bQ, lambdaQ);
        Formula swappedCurvature = Curvature(a, bQ, lambdaQ, bP, lambdaP);
        Formula gaugeCurvature = Curvature(
            a,
            GaugeShift(a, lambdaP, originShift, bP),
            lambdaP,
            GaugeShift(a, lambdaQ, originShift, bQ),
            lambdaQ);
        Formula pGap = Seq(a, Sp, Minus, Sp, lambdaP);
        Formula qGap = Seq(a, Sp, Minus, Sp, lambdaQ);
        Formula pOrigin = ObserverOrigin(a, lambdaP, bP);
        Formula qOrigin = ObserverOrigin(a, lambdaQ, bQ);

        Formula premises = Seq(
            Open, pGap, Sp, Neq, Sp, D(0), Close,
            Sp, Land, Sp,
            Open, qGap, Sp, Neq, Sp, D(0), Close);
        Formula conclusions = Seq(
            Open,
            Open,
            Call("fst", pThenQ), Sp, Minus, Sp, Call("fst", qThenP),
            Sp, Eq, Sp, curvature, Sp, Times, Sp, Call("snd", state),
            Close,
            Sp, Land, RowBreak, Grp(),
            Open, Call("snd", pThenQ), Sp, Eq, Sp, Call("snd", qThenP), Close,
            Sp, Land, RowBreak, Grp(),
            Open, swappedCurvature, Sp, Eq, Sp, Minus, curvature, Close,
            Sp, Land, RowBreak, Grp(),
            Open, gaugeCurvature, Sp, Eq, Sp, curvature, Close,
            Sp, Land, RowBreak, Grp(),
            Open,
            curvature, Sp, Eq, Sp,
            Open, pGap, Close, Sp, Times, Sp,
            Open, qGap, Close, Sp, Times, Sp,
            Open, pOrigin, Sp, Minus, Sp, qOrigin, Close,
            Close,
            Sp, Land, RowBreak, Grp(),
            Open,
            Open, curvature, Sp, Eq, Sp, D(0), Close,
            Sp, Leftrightarrow, Sp,
            Open, pOrigin, Sp, Eq, Sp, qOrigin, Close,
            Close,
            Close);

        return Disp(Seq(
            Forall, Sp, field, Colon, Sp, F.Id("Type"), Comma, Sp,
            OpenBracket, Call("Field", field), CloseBracket, Comma, RowBreak, Grp(),
            a, Comma, Sp, bP, Comma, Sp, lambdaP, Comma, Sp,
            bQ, Comma, Sp, lambdaQ, Comma, Sp, originShift,
            Colon, Sp, field, Comma, RowBreak, Grp(),
            state, Colon, Sp, pairType, Comma, RowBreak, Grp(),
            premises, Sp, Rightarrow, RowBreak, Grp(),
            conclusions, Dot));
    }
}

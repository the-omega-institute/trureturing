using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ReflectedSpectrum;

internal sealed class FiniteMirrorCumulantOddOrderInvisibilityDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/ReflectedSpectrum/FiniteMirrorCumulantOddOrderInvisibility.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite mirror-closed zero window loses every odd transverse order while its even "
            + "orders add across each reflected pair.",
        H("Odd-Order Invisibility in a Finite Mirror Window"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("transverse-moment-generating-function"),
                DeclarationHandle.Create(Prefix + "transverseMomentGeneratingFunction"),
                H("The finite transverse moment-generating function"),
                StatementSource.FromAuthor(GeneratingFunctionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a finite set of right representatives, the function sums multiplicity "
                        + "times positive weight times the reflected exponential pair "
                        + "exp(u delta)+exp(-u delta). This is exactly the section-local Z_T "
                        + "formula, represented through the previously formalized reflected pair."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-mirror-cumulant-odd-order-invisibility"),
                DeclarationHandle.Create(Prefix
                    + "finite_mirror_cumulant_odd_order_invisibility"),
                H("Finite mirror symmetry hides precisely the odd transverse orders"),
                StatementSource.FromAuthor(OddOrderLawFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The public statement retains the finite representative set, natural "
                            + "multiplicities, strictly positive weights, and nonnegative right "
                            + "displacements from the source window.")),
                    Paragraph(Text(
                        "Its first conjunct says that for every natural r, the (2r+1)-st "
                            + "iterated derivative of that concrete Z_T at zero is zero. Its "
                            + "second conjunct states pairwise cancellation of delta^(2r+1) "
                            + "with (-delta)^(2r+1). Its third conjunct states that the two "
                            + "even powers instead sum to 2 delta^(2r), so the narrative does "
                            + "not strengthen the Lean theorem into strict nonvanishing.")),
                    Paragraph(Text(
                        "The proof differentiates the finite sum using pinned Mathlib and applies "
                            + "the imported arbitrary-order derivative formula for the reflected "
                            + "exponential pair. The positive-weight and nonnegative-displacement "
                            + "hypotheses are carried because the source states them as window "
                            + "conditions, but the derivation does not use either one: the odd-order "
                            + "cancellation holds for arbitrary real weights and arbitrary real "
                            + "displacements, and the underscore prefixes on both binders record "
                            + "that fact mechanically. No conjectural premise such as the Riemann "
                            + "hypothesis occurs."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/Adelic/ReflectedGrowthPairSecondOrderSpectrum")),
        ]));

    private static Formula GeneratingFunctionFormula()
    {
        Formula iota = F.Id("iota");
        Formula representatives = F.Id("A");
        Formula multiplicity = F.Id("m");
        Formula weight = F.Id("w");
        Formula displacement = F.Id("delta");
        Formula u = F.Id("u");
        Formula a = F.Id("a");
        Formula deltaA = Apply(displacement, a);
        Formula reflectedPair = Grp(
            Exponential(Seq(u, Sp, Cdot, Sp, deltaA)), Sp, Plus, Sp,
            Exponential(Seq(Minus, u, Sp, Cdot, Sp, deltaA)));
        Formula summand = Seq(
            Apply(multiplicity, a), Sp, Cdot, Sp,
            Apply(weight, a), Sp, Cdot, Sp, reflectedPair);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Parameters(iota, representatives, multiplicity, weight, displacement),
            u, Colon, Sp, Reals(), Comma, RowBreak,
            Call("transverseMomentGeneratingFunction", representatives, multiplicity,
                weight, displacement, u), Sp, Eq, Sp,
            FiniteSum(a, representatives, summand), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula OddOrderLawFormula()
    {
        Formula iota = F.Id("iota");
        Formula representatives = F.Id("A");
        Formula multiplicity = F.Id("m");
        Formula weight = F.Id("w");
        Formula displacement = F.Id("delta");
        Formula a = F.Id("a");
        Formula r = F.Id("r");
        Formula deltaA = Apply(displacement, a);
        Formula oddOrder = Seq(D(2), Sp, Cdot, Sp, r, Sp, Plus, Sp, D(1));
        Formula evenOrder = Seq(D(2), Sp, Cdot, Sp, r);
        Formula windowFunction = Call(
            "transverseMomentGeneratingFunction", representatives, multiplicity,
            weight, displacement);
        Formula oddDerivative = Seq(
            Forall, Sp, r, Colon, Sp, Naturals(), Comma, Sp,
            Call("iteratedDeriv", oddOrder, windowFunction, D(0)), Sp, Eq, Sp, D(0));
        Formula oddCancellation = Seq(
            Forall, Sp, a, Sp, InMacro, Sp, representatives, Comma, Sp,
            Forall, Sp, r, Colon, Sp, Naturals(), Comma, Sp,
            Power(deltaA, oddOrder), Sp, Plus, Sp,
            Power(Grp(Minus, deltaA), oddOrder), Sp, Eq, Sp, D(0));
        Formula evenAddition = Seq(
            Forall, Sp, a, Sp, InMacro, Sp, representatives, Comma, Sp,
            Forall, Sp, r, Colon, Sp, Naturals(), Comma, Sp,
            Power(deltaA, evenOrder), Sp, Plus, Sp,
            Power(Grp(Minus, deltaA), evenOrder), Sp, Eq, Sp,
            D(2), Sp, Cdot, Sp, Power(deltaA, evenOrder));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Parameters(iota, representatives, multiplicity, weight, displacement),
            PositiveWeights(a, representatives, weight), Sp, Rightarrow, RowBreak,
            NonnegativeDisplacements(a, representatives, displacement),
            Sp, Rightarrow, RowBreak,
            Open, oddDerivative, Close, Sp, Land, RowBreak,
            Open, oddCancellation, Close, Sp, Land, RowBreak,
            Open, evenAddition, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Parameters(
        Formula iota,
        Formula representatives,
        Formula multiplicity,
        Formula weight,
        Formula displacement) =>
        Seq(
            Forall, Sp, iota, Colon, Sp, F.Id("Type"), Comma, RowBreak,
            representatives, Colon, Sp, Call("Finset", iota), Comma, Sp,
            multiplicity, Colon, Sp, iota, Sp, To, Sp, Naturals(), Comma, RowBreak,
            weight, Colon, Sp, iota, Sp, To, Sp, Reals(), Comma, Sp,
            displacement, Colon, Sp, iota, Sp, To, Sp, Reals(), Comma, RowBreak);

    private static Formula PositiveWeights(
        Formula a,
        Formula representatives,
        Formula weight) =>
        Seq(
            Open, Forall, Sp, a, Sp, InMacro, Sp, representatives, Comma, Sp,
            D(0), Sp, Lt, Sp, Apply(weight, a), Close);

    private static Formula NonnegativeDisplacements(
        Formula a,
        Formula representatives,
        Formula displacement) =>
        Seq(
            Open, Forall, Sp, a, Sp, InMacro, Sp, representatives, Comma, Sp,
            D(0), Sp, Leq, Sp, Apply(displacement, a), Close);

    private static Formula FiniteSum(Formula index, Formula set, Formula term) =>
        Seq(Sum, Underscore, Grp(index, Sp, InMacro, Sp, set), Sp, term);

    private static Formula Power(Formula value, Formula exponent) =>
        Seq(value, Caret, Grp(exponent));

    private static Formula Exponential(Formula exponent) =>
        Seq(F.Id("e"), Caret, Grp(exponent));

    private static Formula Naturals() =>
        Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Reals() =>
        Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurements;

internal sealed class HorizontalCasimirDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Measurements/HorizontalCasimir.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive multiplicity-weighted sum of local transverse squares cannot vanish by cancellation.",
        H("Horizontal Casimir Noncancellation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("horizontal-casimir"),
                DeclarationHandle.Create(Prefix + "horizontalCasimir"),
                H("The finite-window horizontal Casimir"),
                StatementSource.FromAuthor(DefinitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a finite orbit window T, the horizontal Casimir is the sum over T of "
                        + "the natural multiplicity, the real weight, and the squared real "
                        + "transverse displacement."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("horizontal-casimir-eq-zero-iff"),
                DeclarationHandle.Create(Prefix + "horizontal_casimir_eq_zero_iff"),
                H("The horizontal Casimir vanishes exactly coordinatewise"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The public statement retains the finite window and requires every "
                            + "selected multiplicity and every selected weight to be strictly positive.")),
                    Paragraph(Text(
                        "Its forward implication says that zero Casimir forces every selected "
                            + "transverse displacement to vanish. Its reverse implication says "
                            + "that pointwise vanishing makes the same source-defined sum zero. "
                            + "Thus phases, signs, or correlations cannot cancel these local squares.")),
                    Paragraph(Text(
                        "The result is finite-dimensional and algebraic. It uses no Riemann-hypothesis "
                            + "premise or unformalized section-level bridge."))),
                DescribeRole.Theorem))));

    private static Formula DefinitionFormula()
    {
        Formula orbit = F.Id("O");
        Formula window = F.Id("T");
        Formula multiplicity = F.Id("m");
        Formula weight = F.Id("w");
        Formula displacement = F.Id("delta");
        Formula o = F.Id("o");
        Formula summand = Seq(
            Apply(multiplicity, o), Sp, Cdot, Sp,
            Apply(weight, o), Sp, Cdot, Sp,
            Power(Apply(displacement, o), D(2)));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Parameters(orbit, window, multiplicity, weight, displacement),
            Call("horizontalCasimir", window, multiplicity, weight, displacement),
            Sp, Eq, Sp, FiniteSum(o, window, summand), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula TheoremFormula()
    {
        Formula orbit = F.Id("O");
        Formula window = F.Id("T");
        Formula multiplicity = F.Id("m");
        Formula weight = F.Id("w");
        Formula displacement = F.Id("delta");
        Formula o = F.Id("o");
        Formula casimir = Call(
            "horizontalCasimir", window, multiplicity, weight, displacement);
        Formula multiplicityPositive = PositiveOnWindow(o, window, multiplicity);
        Formula weightPositive = PositiveOnWindow(o, window, weight);
        Formula displacementZero = Seq(
            Forall, Sp, o, Sp, InMacro, Sp, window, Comma, Sp,
            Apply(displacement, o), Sp, Eq, Sp, D(0));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Parameters(orbit, window, multiplicity, weight, displacement),
            multiplicityPositive, Sp, Rightarrow, RowBreak,
            weightPositive, Sp, Rightarrow, RowBreak,
            Open, casimir, Sp, Eq, Sp, D(0), Close, Sp, Iff, Sp,
            Open, displacementZero, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Parameters(
        Formula orbit,
        Formula window,
        Formula multiplicity,
        Formula weight,
        Formula displacement) =>
        Seq(
            Forall, Sp, orbit, Colon, Sp, F.Id("Type"), Comma, RowBreak,
            window, Colon, Sp, Call("Finset", orbit), Comma, Sp,
            multiplicity, Colon, Sp, orbit, Sp, To, Sp, Naturals(), Comma, RowBreak,
            weight, Colon, Sp, orbit, Sp, To, Sp, Reals(), Comma, Sp,
            displacement, Colon, Sp, orbit, Sp, To, Sp, Reals(), Comma, RowBreak);

    private static Formula PositiveOnWindow(
        Formula index,
        Formula window,
        Formula value) =>
        Seq(
            Open, Forall, Sp, index, Sp, InMacro, Sp, window, Comma, Sp,
            D(0), Sp, Lt, Sp, Apply(value, index), Close);

    private static Formula FiniteSum(Formula index, Formula set, Formula term) =>
        Seq(Sum, Underscore, Grp(index, Sp, InMacro, Sp, set), Sp, term);

    private static Formula Power(Formula value, Formula exponent) =>
        Seq(value, Caret, Grp(exponent));

    private static Formula Naturals() =>
        Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Reals() =>
        Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
}

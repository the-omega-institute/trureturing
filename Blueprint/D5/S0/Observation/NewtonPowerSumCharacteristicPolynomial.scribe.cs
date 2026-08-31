using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Observation;

internal sealed class NewtonPowerSumCharacteristicPolynomialDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S0/Observation/NewtonPowerSumCharacteristicPolynomial."
            + "matrix_charpoly_eq_of_spectral_power_sums_eq";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Newton identities recover a split characteristic polynomial from its bounded power sums.",
        H("Newton Power Sums Determine the Characteristic Polynomial"),
        Blocks(Describe.Lean(
            DescribeId.Create("newton-power-sums-determine-characteristic-polynomial"),
            DeclarationHandle.Create(Declaration),
            H("The first dimension-many spectral power sums determine the charpoly"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let two n-by-n matrices over a characteristic-zero field have enumerated "
                        + "split spectra. If the first n positive power sums of those spectra "
                        + "agree, then their characteristic polynomials agree.")),
                Paragraph(Text(
                    "Pinned Mathlib's Newton identity recursively recovers each elementary "
                        + "symmetric polynomial because every positive natural number is "
                        + "nonzero in the field. Mathlib's Vieta expansion then identifies the "
                        + "two products of linear factors.")),
                Paragraph(Text(
                    "Characteristic zero is explicit: without it, the natural-number factor "
                        + "in the Newton recurrence cannot always be cancelled. The split "
                        + "factorization hypotheses expose the spectral witnesses used by the "
                        + "source argument rather than assuming an unavailable trace-to-root "
                        + "bridge."))),
            DescribeRole.Theorem))));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula MatrixSpace(Formula dimension, Formula field) =>
        Call("Matrix", Call("Fin", dimension), Call("Fin", dimension), field);

    private static Formula SpectrumSpace(Formula dimension, Formula field) =>
        Seq(Call("Fin", dimension), Sp, To, Sp, field);

    private static Formula CharacteristicPolynomial(Formula matrix) =>
        Call("charpoly", matrix);

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula SplitPolynomial(
        Formula spectrum,
        Formula dimension,
        Formula variable,
        Formula index) =>
        Seq(
            Prod, Underscore, Grp(index, Sp, InMacro, Sp, Call("Fin", dimension)), Sp,
            Open, variable, Sp, Minus, Sp, Apply(spectrum, index), Close);

    private static Formula PowerSum(
        Formula spectrum,
        Formula dimension,
        Formula exponent,
        Formula index) =>
        Seq(
            Sum, Underscore, Grp(index, Sp, InMacro, Sp, Call("Fin", dimension)), Sp,
            Apply(spectrum, index), Caret, Grp(exponent));

    private static Formula TheoremFormula()
    {
        Formula field = F.Id("K");
        Formula dimension = F.Id("n");
        Formula matrix = F.Id("A");
        Formula other = F.Id("B");
        Formula spectrum = F.Id("lambda");
        Formula otherSpectrum = F.Id("mu");
        Formula index = F.Id("i");
        Formula exponent = F.Id("k");
        Formula variable = F.Id("t");
        Formula matrices = MatrixSpace(dimension, field);
        Formula spectra = SpectrumSpace(dimension, field);

        Formula matrixSplits = Seq(
            CharacteristicPolynomial(matrix), Sp, Eq, Sp,
            SplitPolynomial(spectrum, dimension, variable, index));

        Formula otherSplits = Seq(
            CharacteristicPolynomial(other), Sp, Eq, Sp,
            SplitPolynomial(otherSpectrum, dimension, variable, index));

        Formula boundedPowerSumsAgree = Seq(
            Forall, Sp, exponent, Sp, InMacro, Sp, Naturals(), Comma, Sp,
            exponent, Sp, Lt, Sp, dimension, Sp, Rightarrow, Sp,
            PowerSum(spectrum, dimension, Seq(exponent, Sp, Plus, Sp, D(1)), index),
            Sp, Eq, Sp,
            PowerSum(otherSpectrum, dimension, Seq(exponent, Sp, Plus, Sp, D(1)), index));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, field, Colon, Sp, TypeUniverse(), Comma, Sp,
                Call("Field", field), Comma, Sp, Call("CharZero", field), Comma, Sp,
                dimension, Sp, InMacro, Sp, Naturals(), Comma),
            Seq(
                Forall, Sp, matrix, Comma, Sp, other, Sp, InMacro, Sp, matrices, Comma, Sp,
                spectrum, Comma, Sp, otherSpectrum, Sp, InMacro, Sp, spectra, Comma),
            Seq(
                Open, matrixSplits, Sp, Land, Sp, otherSplits, Sp, Land, Sp,
                boundedPowerSumsAgree, Close, Sp, Rightarrow),
            Seq(
                CharacteristicPolynomial(matrix), Sp, Eq, Sp,
                CharacteristicPolynomial(other), Dot),
        ]));
    }
}

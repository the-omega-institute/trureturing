using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Deficit.Beatty;

internal sealed class GoldenSpectralCoordinateDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Deficit/Beatty/GoldenSpectralCoordinate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden-square scaling sends the structural zero to one half, and the centered "
            + "spectral coordinate is real exactly on the structural line.",
        H("Golden Spectral Coordinate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-eigenvalue"),
                DeclarationHandle.Create(Prefix + "phi"),
                H("Golden eigenvalue"),
                StatementSource.FromAuthor(PhiFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The value phi=(1+sqrt(5))/2 is transcribed verbatim from "
                        + "D5/X_Frontier/Hearts.lean. This module does not import that frozen "
                        + "frontier owner."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("structural-pole"),
                DeclarationHandle.Create(Prefix + "structuralPole"),
                H("Structural pole"),
                StatementSource.FromAuthor(StructuralPoleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The structural pole 1/phi^3 is transcribed with the same bytes of "
                        + "mathematical content as the frontier route, without importing it."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("structural-zero"),
                DeclarationHandle.Create(Prefix + "structuralZero"),
                H("Structural zero"),
                StatementSource.FromAuthor(StructuralZeroFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The structural zero is the reciprocal of twice phi squared, again "
                        + "transcribed verbatim from the route's frozen frontier constants."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("golden-natural-scale"),
                DeclarationHandle.Create(Prefix + "goldenNaturalScale"),
                H("Golden natural scale"),
                StatementSource.FromAuthor(GoldenNaturalScaleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The natural scale multiplies a complex variable by the real scalar phi "
                        + "squared. Its named one-half instantiation below makes this definition "
                        + "earn its freeze."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("golden-spectral-parameter"),
                DeclarationHandle.Create(Prefix + "goldenSpectralParameter"),
                H("Golden spectral parameter"),
                StatementSource.FromAuthor(GoldenSpectralParameterFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The spectral parameter rotates the centered natural scale by minus i. "
                        + "The independent real-spectrum equivalence below makes this definition "
                        + "earn its freeze."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("golden-natural-scale-hits-half"),
                DeclarationHandle.Create(Prefix + "golden_natural_scale_hits_half"),
                H("Golden natural scaling hits one half"),
                StatementSource.FromAuthor(GoldenNaturalScaleHitsHalfFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At the structural zero, multiplication by phi squared cancels the "
                        + "reciprocal phi square and leaves exactly one half. This is route "
                        + "obligation R-A."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-spectral-imaginary-part-zero-iff-structural-line"),
                DeclarationHandle.Create(Prefix + "golden_spectral_im_eq_zero_iff"),
                H("The golden spectral parameter is real exactly on the structural line"),
                StatementSource.FromAuthor(GoldenSpectralIffFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every complex s, expanding complex multiplication gives imaginary "
                            + "part minus (phi squared times Re(s) minus one half). Positivity of "
                            + "phi permits cancellation, so it vanishes exactly at structuralZero.")),
                    Paragraph(Text(
                        "This iff is route obligation R-C. Together with the R-A instantiation, "
                            + "it is the freeze-earning content for the two new coordinate "
                            + "definitions; neither theorem is a definitional tautology.")),
                    Paragraph(Text(
                        "The consumer transports the O-5 line into the existing CriticalLine and "
                            + "off-line orbit language. The classical analogue is "
                            + "D5/S3/Weil/ZetaBridge/ConvolutionSquareCriticalLine; it is named "
                            + "here for comparison and is deliberately not imported.")),
                    Paragraph(Text(
                        "Exact repository and pinned-Mathlib searches found no whole target. "
                            + "Mathlib supplies the golden-ratio bound, complex component laws, "
                            + "and nonzero cancellation used in the proof."))),
                DescribeRole.Theorem))));

    private static Formula PhiFormula() =>
        Disp(Equal(Varphi, Fraction(
            Seq(D(1), Sp, Plus, Sp, Seq(Sqrt, Grp(D(5)))),
            D(2))));

    private static Formula StructuralPoleFormula() =>
        Disp(Equal(Constant(F.Id("structuralPole")), Fraction(
            D(1), new Formula.Power(Varphi, D(3)))));

    private static Formula StructuralZeroFormula() =>
        Disp(Equal(Constant(F.Id("structuralZero")), Fraction(
            D(1), Seq(D(2), Sp, Cdot, Sp, new Formula.Power(Varphi, D(2))))));

    private static Formula GoldenNaturalScaleFormula()
    {
        Formula s = F.Id("s");
        Formula value = Seq(new Formula.Power(Varphi, D(2)), Sp, Cdot, Sp, s);
        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", Complexes())],
            Equal(Call("goldenNaturalScale", s), value)));
    }

    private static Formula GoldenSpectralParameterFormula()
    {
        Formula s = F.Id("s");
        Formula centered = Seq(
            Call("goldenNaturalScale", s), Sp, Minus, Sp, Fraction(D(1), D(2)));
        Formula value = Seq(Minus, F.Id("i"), Sp, Cdot, Sp, Grp(centered));
        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", Complexes())],
            Equal(Call("goldenSpectralParameter", s), value)));
    }

    private static Formula GoldenNaturalScaleHitsHalfFormula() =>
        Disp(Equal(
            Call("goldenNaturalScale", Constant(F.Id("structuralZero"))),
            Fraction(D(1), D(2))));

    private static Formula GoldenSpectralIffFormula()
    {
        Formula s = F.Id("s");
        Formula spectral = Call("goldenSpectralParameter", s);
        Formula left = Equal(ImaginaryPart(spectral), D(0));
        Formula right = Equal(RealPart(s), Constant(F.Id("structuralZero")));
        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", Complexes())],
            new Formula.Logic(left, FormulaLogicOperator.Iff, right)));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula Call(string name, Formula argument) =>
        Seq(Operatorname, Grp(F.Id(name)), Open, argument, Close);

    private static Formula Constant(Formula name) =>
        Seq(Operatorname, Grp(name));

    private static Formula RealPart(Formula value) =>
        Seq(Operatorname, Grp(F.Id("Re")), Open, value, Close);

    private static Formula ImaginaryPart(Formula value) =>
        Seq(Operatorname, Grp(F.Id("Im")), Open, value, Close);

    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
}

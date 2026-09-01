using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Symmetry;

internal sealed class CriticalCenterCoordinateDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Zeros/Symmetry/CriticalCenterCoordinate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Critical-center coordinates identify the critical line with the real axis "
            + "and transport same-height reflection to complex conjugation.",
        H("Critical Center Coordinate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("critical-center-coordinate"),
                DeclarationHandle.Create(Prefix + "centralCoord"),
                H("Critical-center coordinate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This name reuses the frozen spectral parameter minus i times rho "
                        + "minus one half; it does not introduce a second coordinate source."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("inverse-critical-center-coordinate"),
                DeclarationHandle.Create(Prefix + "invCentralCoord"),
                H("Inverse critical-center coordinate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The inverse affine map sends z to one half plus i times z."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("critical-center-coordinate-equivalence"),
                DeclarationHandle.Create(Prefix + "centralCoordEquiv"),
                H("Critical-center coordinate equivalence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The two explicit inverse laws package the coordinate map as an "
                        + "equivalence of the complex plane, so no information is lost."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("critical-center-coordinate-specification"),
                DeclarationHandle.Create(Prefix + "critical_center_coordinate_spec"),
                H("Critical-center coordinate specification"),
                StatementSource.FromAuthor(CriticalCenterCoordinateSpecFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The real and imaginary component formulas identify the critical "
                            + "line with the real coordinate axis. Both affine inverse laws "
                            + "hold for arbitrary complex points.")),
                    Paragraph(Text(
                        "Functional reflection acts by negation, conjugation acts by negative "
                            + "conjugation, and their same-height composite acts by ordinary "
                            + "complex conjugation in the new coordinate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("critical-line-coordinate-witness"),
                DeclarationHandle.Create(Prefix + "critical_line_coordinate_witness"),
                H("One half plus three i has coordinate three"),
                StatementSource.FromAuthor(CriticalLineWitnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The on-line witness evaluates the coordinate exactly and has zero "
                        + "coordinate imaginary part."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("off-line-coordinate-witness"),
                DeclarationHandle.Create(Prefix + "off_line_coordinate_witness"),
                H("Three quarters plus three i has negative quarter imaginary coordinate"),
                StatementSource.FromAuthor(OffLineWitnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The off-line witness evaluates to three minus one quarter i, verifying "
                        + "the sign and a nonzero coordinate imaginary part."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Zeros/Symmetry/FiniteShiftedBlaschkeSymmetry")),
        ]));

    private static Formula CriticalCenterCoordinateSpecFormula()
    {
        Formula rho = F.Rho;
        Formula z = F.Id("z");
        Formula center = Call("centralCoord", rho);
        Formula inverse = Call("invCentralCoord", center);
        Formula half = Fraction(D(1), D(2));
        Formula realFormula = Seq(RealPart(center), Sp, Eq, Sp, ImaginaryPart(rho));
        Formula imaginaryFormula = Seq(
            ImaginaryPart(center), Sp, Eq, Sp, Minus,
            Grp(Seq(RealPart(rho), Sp, Minus, Sp, half)));
        Formula criticalCriterion = Seq(
            Open, RealPart(rho), Sp, Eq, Sp, half, Close,
            Sp, Leftrightarrow, Sp,
            Open, ImaginaryPart(center), Sp, Eq, Sp, D(0), Close);
        Formula rightInverse = Seq(
            Forall, Sp, z, Colon, Sp, Complexes(), Comma, Sp,
            Call("centralCoord", Call("invCentralCoord", z)), Sp, Eq, Sp, z);
        Formula functionalReflection = Seq(
            Call("centralCoord", Seq(D(1), Sp, Minus, Sp, rho)),
            Sp, Eq, Sp, Minus, center);
        Formula conjugation = Seq(
            Call("centralCoord", Conjugate(rho)), Sp, Eq, Sp,
            Minus, Conjugate(center));
        Formula reflected = Seq(
            Call("centralCoord", Call("reflect", rho)), Sp, Eq, Sp,
            Conjugate(center));

        return Disp(Seq(
            Forall, Sp, rho, Colon, Sp, Complexes(), Comma, RowBreak, Grp(),
            realFormula, Sp, Land, Sp, imaginaryFormula, Sp, Land, RowBreak, Grp(),
            Open, criticalCriterion, Close, Sp, Land, Sp,
            inverse, Sp, Eq, Sp, rho, Sp, Land, RowBreak, Grp(),
            Open, rightInverse, Close, Sp, Land, Sp,
            functionalReflection, Sp, Land, RowBreak, Grp(),
            conjugation, Sp, Land, Sp, reflected, Dot));
    }

    private static Formula CriticalLineWitnessFormula()
    {
        Formula rho = Seq(Fraction(D(1), D(2)), Sp, Plus, Sp, D(3), F.Id("i"));
        Formula center = Call("centralCoord", rho);
        return Disp(Seq(
            center, Sp, Eq, Sp, D(3), Sp, Land, Sp,
            RealPart(rho), Sp, Eq, Sp, Fraction(D(1), D(2)), Sp, Land, Sp,
            ImaginaryPart(center), Sp, Eq, Sp, D(0), Dot));
    }

    private static Formula OffLineWitnessFormula()
    {
        Formula rho = Seq(Fraction(D(3), D(4)), Sp, Plus, Sp, D(3), F.Id("i"));
        Formula center = Call("centralCoord", rho);
        return Disp(Seq(
            center, Sp, Eq, Sp, D(3), Sp, Minus, Sp,
            Fraction(D(1), D(4)), F.Id("i"), Sp, Land, RowBreak, Grp(),
            RealPart(rho), Sp, Neq, Sp, Fraction(D(1), D(2)), Sp, Land, Sp,
            ImaginaryPart(center), Sp, Eq, Sp, Minus, Fraction(D(1), D(4)),
            Sp, Land, Sp, ImaginaryPart(center), Sp, Neq, Sp, D(0), Dot));
    }

    private static Formula Call(string name, Formula argument) =>
        Seq(Operatorname, Grp(F.Id(name)), Open, argument, Close);

    private static Formula RealPart(Formula value) =>
        Seq(Operatorname, Grp(F.Id("Re")), Open, value, Close);

    private static Formula ImaginaryPart(Formula value) =>
        Seq(Operatorname, Grp(F.Id("Im")), Open, value, Close);

    private static Formula Conjugate(Formula value) => OverlineFormula(value);

    private static Formula OverlineFormula(Formula value) =>
        Seq(Overline, Grp(value));

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
}

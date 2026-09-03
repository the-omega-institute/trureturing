using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics;

internal sealed class UniversalSolenoidCoordinateDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S1/Dynamics/UniversalSolenoidCoordinate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A coordinate scaled by its index recovers the visible solenoid projection.",
        H("Universal Solenoid Coordinate Scaling"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nsmul-coordinate-eq-projection"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "nsmul_coordinate_eq_projection"),
                H("Scaling any coordinate by its index gives the projection"),
                StatementSource.FromAuthor(CoordinateProjectionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A point theta of the universal solenoid is a family of circle "
                            + "coordinates, one for each positive integer index, compatible "
                            + "under divisibility. Reading that compatibility at index 1 says "
                            + "exactly that multiplying the index-m coordinate by m lands on "
                            + "the visible projection. This holds for every theta and every "
                            + "positive m, with no hypothesis on theta or its projection.")),
                    Paragraph(Text(
                        "The value is an API one, not mathematical novelty. The proof is the "
                            + "defining compatibility field instantiated at index 1; nothing "
                            + "is discovered.")),
                    Paragraph(Text(
                        "Three modules elsewhere in the repository each carry a private "
                            + "declaration of the projection theta = 0 special case; one of "
                            + "them packages theta as a point of the projection kernel. Those "
                            + "three modules are frozen and therefore cannot import this "
                            + "module. Naming the fact here removes none of those declarations; "
                            + "it stops the next private copy from being written.")),
                    Paragraph(Text(
                        "All three private copies assume that the projection vanishes, while "
                            + "this identity needs no such hypothesis. The unconditional form "
                            + "is the primary theorem here, and those copies are its instances."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nsmul-coordinate-eq-zero"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "nsmul_coordinate_eq_zero"),
                H("A zero projection makes each coordinate index-torsion"),
                StatementSource.FromAuthor(CoordinateZeroFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every solenoid point theta whose visible projection is zero, and "
                            + "for every positive integer m, multiplying the index-m circle "
                            + "coordinate by m gives zero. This is the special case used by the "
                            + "three private declarations.")),
                    Paragraph(Text(
                        "The proof applies the unconditional coordinate-projection identity "
                            + "and then rewrites with the supplied vanishing hypothesis. It "
                            + "adds a public API name for the specialization, not a new "
                            + "mathematical argument."))),
                DescribeRole.Theorem))));

    private static Formula PositiveIntegers() =>
        Seq(Mathbb, Grp(F.Id("N")), Underscore, Grp(Gt, Num(0)));

    private static Formula Coordinate(Formula point, Formula index) =>
        Seq(point, Underscore, Grp(index));

    private static Formula Projection(Formula point) =>
        Call("projection", point);

    private static Formula CoordinateProjectionFormula()
    {
        Formula point = F.Id("theta");
        Formula index = F.Id("m");

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, point, Colon, Sp, F.Id("UniversalSolenoid"), Comma),
            Seq(
                Forall, Sp, index, Colon, Sp, PositiveIntegers(), Comma),
            Seq(
                index, Sp, Cdot, Sp, Coordinate(point, index), Sp, Eq, Sp,
                Projection(point), Dot),
        ]));
    }

    private static Formula CoordinateZeroFormula()
    {
        Formula point = F.Id("theta");
        Formula index = F.Id("m");

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, point, Colon, Sp, F.Id("UniversalSolenoid"), Comma),
            Seq(
                Projection(point), Sp, Eq, Sp, Num(0), Sp, Rightarrow),
            Seq(
                Forall, Sp, index, Colon, Sp, PositiveIntegers(), Comma),
            Seq(
                index, Sp, Cdot, Sp, Coordinate(point, index), Sp, Eq, Sp,
                Num(0), Dot),
        ]));
    }
}

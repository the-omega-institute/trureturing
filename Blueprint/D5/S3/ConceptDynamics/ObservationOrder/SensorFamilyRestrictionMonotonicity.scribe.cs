using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ObservationOrder;

internal sealed class SensorFamilyRestrictionMonotonicityDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/ObservationOrder/SensorFamilyRestrictionMonotonicity."
            + "restricting_sensor_family_enlarges_kernel";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Restricting a sensor family can only enlarge its equality kernel.",
        H("Sensor Family Restriction Monotonicity"),
        Blocks(Describe.Lean(
            DescribeId.Create("sensor-family-restriction-enlarges-the-kernel"),
            DeclarationHandle.Create(Declaration),
            H("Sensor family restriction enlarges the kernel"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A selector reindexes an original sensor family by any second index type. "
                        + "It may delete coordinates or repeat them.")),
                Paragraph(Text(
                    "States equal at every original coordinate remain equal at each selected "
                        + "coordinate. The complete-family kernel is therefore contained in the "
                        + "restricted-family kernel.")),
                Paragraph(Text(
                    "No injectivity or surjectivity condition is imposed on the selector."))),
            DescribeRole.Theorem))));

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula TheoremFormula()
    {
        Formula indexType = F.Id("I");
        Formula selectedType = F.Id("J");
        Formula source = F.Id("X");
        Formula output = F.Id("O");
        Formula sensor = F.Id("q");
        Formula select = F.Id("s");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(Seq(indexType, Comma, Sp, selectedType, Comma, Sp, source,
                Comma, Sp, output), TypeUniverse()),
            Comma, RowBreak, Grp(),
            Typed(sensor, Seq(indexType, Sp, To, Sp, source, Sp, To, Sp, output)),
            Comma, Sp,
            Typed(select, Seq(selectedType, Sp, To, Sp, indexType)),
            Comma, RowBreak, Grp(),
            Call("K", Call("jointReadout", sensor)), Sp, Subseteq, Sp,
            Call("K", Call("restrictedReadout", sensor, select)), Dot,
            End, Grp(F.Id("gathered"))));
    }
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.SensorFamilies;

internal sealed class SensorFamilyRestrictionMonotonicityDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/SensorFamilies/SensorFamilyRestrictionMonotonicity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Restricting a sensor family can only enlarge its equality kernel.",
        H("Sensor Family Restriction Monotonicity"),
        Blocks(Describe.Lean(
            DescribeId.Create("reindexing-a-subfamily-only-enlarges-the-kernel"),
            DeclarationHandle.Create(
                Prefix + "restricting_sensor_family_enlarges_kernel"),
            H("Reindexing a subfamily only enlarges the kernel"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let select choose original sensor indices for a reindexed family. It may "
                        + "delete or repeat coordinates.")),
                Paragraph(Text(
                    "Agreement at every original coordinate implies agreement at each selected "
                        + "coordinate by evaluation through select.")),
                Paragraph(Text(
                    "Therefore the complete-family kernel is contained in the selected-family "
                        + "kernel; no injectivity or surjectivity of select is assumed."))),
            DescribeRole.Theorem))));

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula Statement()
    {
        Formula sensor = F.Id("sensor");
        Formula select = F.Id("select");
        Formula all = Seq(F.Id("x"), Sp, Mapsto, Sp,
            Open, F.Id("i"), Sp, Mapsto, Sp, Call("sensor", F.Id("i"), F.Id("x")), Close);
        Formula restricted = Seq(F.Id("x"), Sp, Mapsto, Sp,
            Open, F.Id("j"), Sp, Mapsto, Sp,
            Call("sensor", Call("select", F.Id("j")), F.Id("x")), Close);
        return Disp(Seq(
            Forall, Sp, sensor, Colon, Sp,
            Arrow(F.Id("I"), Arrow(F.Id("X"), F.Id("O"))), Comma, Sp,
            select, Colon, Sp, Arrow(F.Id("J"), F.Id("I")), Comma, Sp,
            Call("ker", all), Sp, Subseteq, Sp, Call("ker", restricted), Dot));
    }
}

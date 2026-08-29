using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.SensorFamilies;

internal sealed class SurjectiveSensorReindexKernelEqualityDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/SensorFamilies/SurjectiveSensorReindexKernelEquality.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Surjective reindexing preserves the joint sensor kernel.",
        H("Surjective Sensor Reindex Kernel Equality"),
        Blocks(Describe.Lean(
            DescribeId.Create("surjective-reindexing-preserves-family-kernel-membership"),
            DeclarationHandle.Create(
                Prefix + "surjective_reindex_preserves_family_kernel"),
            H("Surjective reindexing preserves family-kernel membership"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let select map new sensor indices onto every original sensor index, and "
                        + "fix source states x and y.")),
                Paragraph(Text(
                    "Original-family agreement immediately gives reindexed agreement. For the "
                        + "reverse direction, surjectivity supplies a new index above each old "
                        + "coordinate.")),
                Paragraph(Text(
                    "The theorem preserves pointwise family-kernel membership; select need not "
                        + "be injective."))),
            DescribeRole.Theorem))));

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula Statement()
    {
        Formula sensor = F.Id("sensor");
        Formula select = F.Id("select");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula reindexed = Seq(F.Id("j"), Sp, Mapsto, Sp,
            Call("sensor", Call("select", F.Id("j"))));
        Formula conclusion = Seq(
            Call("FamilyKernel", sensor, x, y), Sp, Iff, Sp,
            Call("FamilyKernel", reindexed, x, y));
        return Disp(Seq(
            Forall, Sp, sensor, Colon, Sp,
            Arrow(F.Id("I"), Arrow(F.Id("X"), F.Id("O"))), Comma, Sp,
            select, Colon, Sp, Arrow(F.Id("J"), F.Id("I")), Comma, Sp,
            x, Comma, Sp, y, Colon, Sp, F.Id("X"), Comma, RowBreak, Grp(),
            Call("Surjective", select), Sp, Rightarrow, Sp,
            Open, conclusion, Close, Dot));
    }
}

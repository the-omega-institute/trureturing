using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Faithfulness;

internal sealed class InjectiveSensorFamilyFaithfulnessDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/Faithfulness/InjectiveSensorFamilyFaithfulness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One injective sensor makes the complete sensor family faithful.",
        H("Injective Sensor Family Faithfulness"),
        Blocks(Describe.Lean(
            DescribeId.Create("an-injective-member-makes-the-joint-readout-injective"),
            DeclarationHandle.Create(
                Prefix + "injective_member_makes_joint_readout_injective"),
            H("An injective member makes the joint readout injective"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Fix an indexed sensor family and select one sensor whose state readout "
                        + "is injective.")),
                Paragraph(Text(
                    "Equality of the complete function-valued readouts gives equality at the "
                        + "selected coordinate by evaluation.")),
                Paragraph(Text(
                    "Injectivity of that coordinate then identifies the source states. No "
                        + "condition is imposed on the other sensors or on the index type."))),
            DescribeRole.Theorem))));

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula Statement()
    {
        Formula sensor = F.Id("sensor");
        Formula index = F.Id("i0");
        Formula sensorType = Arrow(F.Id("I"), Arrow(F.Id("X"), F.Id("O")));
        Formula joint = Seq(F.Id("x"), Sp, Mapsto, Sp,
            Open, F.Id("i"), Sp, Mapsto, Sp, Call("sensor", F.Id("i"), F.Id("x")), Close);
        return Disp(Seq(
            Forall, Sp, sensor, Colon, Sp, sensorType, Comma, Sp,
            index, Colon, Sp, F.Id("I"), Comma, Sp,
            Call("Injective", Call("sensor", index)), Sp, Rightarrow, Sp,
            Call("Injective", joint), Dot));
    }
}

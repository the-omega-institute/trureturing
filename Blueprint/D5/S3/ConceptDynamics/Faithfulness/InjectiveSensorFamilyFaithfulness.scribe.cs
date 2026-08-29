using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Faithfulness;

internal sealed class InjectiveSensorFamilyFaithfulnessDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Faithfulness/InjectiveSensorFamilyFaithfulness."
            + "injective_member_makes_joint_readout_injective";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One injective sensor makes the complete sensor family faithful.",
        H("Injective Sensor Family Faithfulness"),
        Blocks(Describe.Lean(
            DescribeId.Create("one-injective-sensor-makes-the-family-faithful"),
            DeclarationHandle.Create(Declaration),
            H("One injective sensor makes the family faithful"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The joint readout records every coordinate of an indexed sensor family. "
                        + "One distinguished coordinate is assumed injective.")),
                Paragraph(Text(
                    "Equality of joint readouts may be evaluated at that coordinate. "
                        + "Injectivity of the selected sensor then recovers equality of the "
                        + "underlying source states.")),
                Paragraph(Text(
                    "No assumption is placed on the remaining sensors, the size of the index "
                        + "type, or any algebraic structure on the source and output types."))),
            DescribeRole.Theorem))));

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula TheoremFormula()
    {
        Formula indexType = F.Id("I");
        Formula source = F.Id("X");
        Formula output = F.Id("O");
        Formula sensor = F.Id("q");
        Formula index = F.Id("i");
        Formula familyType = Seq(
            indexType, Sp, To, Sp, source, Sp, To, Sp, output);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(Seq(indexType, Comma, Sp, source, Comma, Sp, output),
                TypeUniverse()),
            Comma, RowBreak, Grp(),
            Typed(sensor, familyType), Comma, Sp,
            Typed(index, indexType), Comma, RowBreak, Grp(),
            Call("Injective", Call("q", index)), Sp, Rightarrow, Sp,
            Call("Injective", Call("jointReadout", sensor)), Dot,
            End, Grp(F.Id("gathered"))));
    }
}

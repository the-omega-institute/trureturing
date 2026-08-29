using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Faithfulness;

internal sealed class PairSensorStrictRefinementDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/Faithfulness/PairSensorStrictRefinement.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A second sensor strictly refines the first kernel when it resolves a collision.",
        H("Pair Sensor Strict Refinement"),
        Blocks(Describe.Lean(
            DescribeId.Create("a-resolved-collision-makes-pairing-strictly-finer"),
            DeclarationHandle.Create(Prefix + "pair_sensor_strictly_refines_first_kernel"),
            H("A resolved collision makes the paired kernel strictly finer"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Pairing two sensors can only refine the first sensor's equality kernel, "
                        + "because equality of pairs implies equality of first components.")),
                Paragraph(Text(
                    "Assume x and y collide under the first sensor but are separated by the "
                        + "second. Their collision belongs to the first kernel and not the "
                        + "paired kernel.")),
                Paragraph(Text(
                    "That explicit witness proves strict inclusion; no global injectivity of "
                        + "the second sensor is required."))),
            DescribeRole.Theorem))));

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula Statement()
    {
        Formula first = F.Id("first");
        Formula second = F.Id("second");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula pair = Seq(F.Id("state"), Sp, Mapsto, Sp,
            Open, Call("first", F.Id("state")), Comma, Sp,
            Call("second", F.Id("state")), Close);
        Formula antecedent = Seq(
            Call("first", x), Sp, Eq, Sp, Call("first", y), Sp, Land, Sp,
            Call("second", x), Sp, Neq, Sp, Call("second", y));
        return Disp(Seq(
            Forall, Sp, first, Colon, Sp, Arrow(F.Id("X"), F.Id("Y")), Comma, Sp,
            second, Colon, Sp, Arrow(F.Id("X"), F.Id("Z")), Comma, Sp,
            x, Comma, Sp, y, Colon, Sp, F.Id("X"), Comma, RowBreak, Grp(),
            Open, antecedent, Close, Sp, Rightarrow, Sp,
            Call("ker", pair), Sp, Lt, Sp, Call("ker", first), Dot));
    }
}

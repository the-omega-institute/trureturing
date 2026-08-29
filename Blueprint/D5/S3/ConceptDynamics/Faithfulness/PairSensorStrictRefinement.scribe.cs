using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Faithfulness;

internal sealed class PairSensorStrictRefinementDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Faithfulness/PairSensorStrictRefinement."
            + "pair_sensor_strictly_refines_first_kernel";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A second sensor strictly refines the first kernel when it resolves a collision.",
        H("Pair Sensor Strict Refinement"),
        Blocks(Describe.Lean(
            DescribeId.Create("second-sensor-strictly-refines-a-witnessed-collision"),
            DeclarationHandle.Create(Declaration),
            H("A second sensor strictly refines a witnessed collision"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The first readout identifies a supplied pair of source states, while the "
                        + "second readout distinguishes that same pair.")),
                Paragraph(Text(
                    "Equality of paired readouts always projects to equality of the first "
                        + "coordinate, giving kernel inclusion. The supplied collision lies in "
                        + "the first kernel and outside the paired kernel, making it strict.")),
                Paragraph(Text(
                    "The result is a witness-level criterion. It requires no finiteness, "
                        + "decidable equality, topology, or probability structure."))),
            DescribeRole.Theorem))));

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula TheoremFormula()
    {
        Formula source = F.Id("X");
        Formula firstOutput = F.Id("Y");
        Formula secondOutput = F.Id("Z");
        Formula first = F.Id("q");
        Formula second = F.Id("r");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula pairReadout = Call("pairReadout", first, second);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(Seq(source, Comma, Sp, firstOutput, Comma, Sp, secondOutput),
                TypeUniverse()),
            Comma, RowBreak, Grp(),
            Typed(first, Seq(source, Sp, To, Sp, firstOutput)), Comma, Sp,
            Typed(second, Seq(source, Sp, To, Sp, secondOutput)),
            Comma, RowBreak, Grp(),
            Typed(Seq(left, Comma, Sp, right), source), Comma, RowBreak, Grp(),
            Call("q", left), Sp, Eq, Sp, Call("q", right), Sp, Land, Sp,
            Call("SeparatedBy", second, left, right), Sp, Rightarrow, RowBreak, Grp(),
            Call("StrictSubset", Call("K", pairReadout), Call("K", first)), Dot,
            End, Grp(F.Id("gathered"))));
    }
}

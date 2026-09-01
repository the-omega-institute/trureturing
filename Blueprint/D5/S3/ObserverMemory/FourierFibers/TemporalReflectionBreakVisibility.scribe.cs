using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.FourierFibers;

internal sealed class TemporalReflectionBreakVisibilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A static scalar readout identifies reflected modal branches, while one "
            + "nondegenerate time step separates them.",
        H("Temporal Reflection-Break Visibility"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("reflected-branches-time-one-separation"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/FourierFibers/TemporalReflectionBreakVisibility.reflected_branches_time_one_separation"),
                H("Time reveals a nondegenerate reflected split"),
                StatementSource.FromAuthor(SeparationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The two reflected branch states collide at time zero. If their modal multipliers differ, the first time step produces different scalar readings.")),
                    Paragraph(Text(
                        "The result formalizes temporal revelation of a pre-existing hidden distinction. It does not claim that the underlying difference is created by observation."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula SeparationFormula() => Disp(Seq(
        Forall, Sp, F.Id("z"), Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))),
        Comma, Sp,
        F.Id("z"), Sp, Neq, Sp,
        F.Id("z"), Caret, Grp(Seq(Minus, D(1))), Sp, Rightarrow, Sp,
        Call("crystalTimeSample", Call("reflectedModes", F.Id("z")),
            Call("firstBranch"), D(1)), Sp, Neq, Sp,
        Call("crystalTimeSample", Call("reflectedModes", F.Id("z")),
            Call("secondBranch"), D(1)), Dot));

}

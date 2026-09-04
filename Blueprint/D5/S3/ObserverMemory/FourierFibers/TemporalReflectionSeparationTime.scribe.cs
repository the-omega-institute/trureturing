using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.FourierFibers;

internal sealed class TemporalReflectionSeparationTimeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nondegenerate reflected spectral pair has canonical first-separation "
            + "time one.",
        H("Temporal Reflection Separation Time"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("reflected-branch-separation-time-eq-one"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/FourierFibers/TemporalReflectionSeparationTime.reflected_branch_separation_time_eq_one"),
                H("Reflected branches first separate at time one"),
                StatementSource.FromAuthor(SeparationTimeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The reflected branch states collide at time zero and, when their reciprocal multipliers differ, separate at the first subsequent observation.")),
                    Paragraph(Text(
                        "The proof instantiates the repository's canonical separationTime and observedAt APIs; it does not introduce another break-depth definition."))),
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

    private static Formula SeparationTimeFormula() => Disp(Seq(
        Begin, Grp(F.Id("gathered")),
        Forall, Sp, F.Id("z"), Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))),
        Comma, Sp,
        F.Id("z"), Sp, Neq, Sp,
        F.Id("z"), Caret, Grp(Seq(Minus, D(1))), Sp, Rightarrow,
        RowBreak, Grp(),
        Call("separationTime",
            Call("oneStepSpectralUpdate",
                Call("reflectedModes", F.Id("z"))),
            Call("modalSumReadout"),
            Seq(Open, Call("firstBranch"), Comma, Sp,
                Call("secondBranch"), Close)),
        Sp, Eq, Sp, D(1), Dot,
        End, Grp(F.Id("gathered"))));

}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.FourierFibers;

internal sealed class TemporalFiberObserverUpgradeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Enlarging a time window shrinks observation fibers, and a separated "
            + "finite mode family is resolved by its first full window.",
        H("Temporal Fiber Observer Upgrade"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("same-temporal-fiber-antitone"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/FourierFibers/TemporalFiberObserverUpgrade.same_temporal_fiber_antitone"),
                H("Temporal fibers are antitone in the observation window"),
                StatementSource.FromAuthor(AntitoneFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Every equality witnessed on a larger finite time window restricts to equality on any smaller window, so adding observation times can only refine the observer kernel.")),
                    Paragraph(Text(
                        "Under separated finite modes, the first full time window has subsingleton fibers. This records observation-depth refinement without asserting thermodynamic irreversibility."))),
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

    private static Formula AntitoneFormula() => Disp(Seq(
        Begin, Grp(F.Id("gathered")),
        Forall, Sp, F.Id("m"), Comma, Sp, F.Id("E"), Comma, Sp, F.Id("F"),
        Comma, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Colon, Sp,
        F.Id("E"), Sp, Subseteq, Sp, F.Id("F"), Sp, Land, Sp,
        Call("SameTemporalFiber", F.Id("m"), F.Id("F"), F.Id("x"),
            F.Id("y")),
        RowBreak, Grp(),
        Rightarrow, Sp,
        Call("SameTemporalFiber", F.Id("m"), F.Id("E"), F.Id("x"),
            F.Id("y")), Dot,
        End, Grp(F.Id("gathered"))));

}

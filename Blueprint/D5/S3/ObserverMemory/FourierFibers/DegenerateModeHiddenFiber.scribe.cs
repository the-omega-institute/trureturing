using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.FourierFibers;

internal sealed class DegenerateModeHiddenFiberDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equal modal multipliers leave an antisymmetric amplitude invisible at "
            + "every observation time.",
        H("Degenerate-Mode Hidden Fiber"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("all-time-trace-not-injective"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/FourierFibers/DegenerateModeHiddenFiber.all_time_trace_not_injective"),
                H("Exact degeneracy defeats the full scalar time trace"),
                StatementSource.FromAuthor(HiddenFiberFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Two equal modal multipliers make the antisymmetric amplitude invisible for every natural observation time, so even the complete scalar time trace is noninjective.")),
                    Paragraph(Text(
                        "This is a constructive hidden-fiber certificate. It isolates spectral degeneracy as an obstruction that time stacking alone cannot remove."))),
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

    private static Formula HiddenFiberFormula() => Disp(Seq(
        Forall, Sp, F.Id("z"), Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))),
        Comma, Sp,
        Neg, Sp, Call("Injective",
            Seq(F.Id("a"), Sp, Mapsto, Sp,
                Call("crystalTimeSample",
                    Call("degenerateModes", F.Id("z")), F.Id("a")))), Dot));

}

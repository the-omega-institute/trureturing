using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.FourierFibers;

internal sealed class SymmetryBreakingObservabilityGainDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Splitting an exact two-mode degeneracy turns a persistent hidden fiber "
            + "into a faithful two-sample time readout.",
        H("Symmetry-Breaking Observability Gain"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("symmetry-breaking-observability-gain"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/FourierFibers/SymmetryBreakingObservabilityGain.symmetry_breaking_observability_gain"),
                H("Mode splitting increases observability"),
                StatementSource.FromAuthor(GainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "An exactly degenerate two-mode system has a nontrivial all-time hidden direction, whereas distinct split multipliers make the first two time samples injective.")),
                    Paragraph(Text(
                        "The theorem captures an information gain caused by lifting spectral degeneracy. It is a finite observer statement and does not assign a physical mechanism to the split."))),
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

    private static Formula GainFormula() => Disp(Seq(
        Begin, Grp(F.Id("gathered")),
        Forall, Sp, F.Id("u"), Comma, Sp, F.Id("v"), Colon, Sp,
        Seq(Mathbb, Grp(F.Id("C"))), Comma, Sp,
        F.Id("u"), Sp, Neq, Sp, F.Id("v"), Sp, Rightarrow,
        RowBreak, Grp(),
        Neg, Sp, Call("Injective",
            Seq(F.Id("a"), Sp, Mapsto, Sp,
                Call("crystalTimeSample",
                    Call("degenerateModes", F.Id("u")), F.Id("a")))),
        Sp, Land,
        RowBreak, Grp(),
        Call("Injective",
            Call("firstCrystalTimeWindow",
                Call("splitModes", F.Id("u"), F.Id("v")))), Dot,
        End, Grp(F.Id("gathered"))));

}

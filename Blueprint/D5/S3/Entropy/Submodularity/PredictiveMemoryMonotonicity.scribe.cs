using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.Submodularity;

internal sealed class PredictiveMemoryMonotonicityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Predictive memory is monotone under deterministic readout refinement.",
        H("Predictive Memory Monotonicity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("predictive-memory-monotone-under-refinement"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/Submodularity/PredictiveMemoryMonotonicity."
                        + "predictive_memory_monotone_under_refinement"),
                H("Refinement cannot increase residual predictive memory"),
                StatementSource.FromAuthor(MonotonicityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let p be a normalized nonnegative joint mass function on a finite past "
                            + "P and future F. Let qf and qc be deterministic readouts of the "
                            + "same past into finite fine and coarse carriers.")),
                    Paragraph(Text(
                        "The canonical refinement premise says that qc factors through qf. Thus "
                            + "the coarse readout is obtained from the fine one by a deterministic "
                            + "forgetting map.")),
                    Paragraph(Text(
                        "The imported refinement decomposition identifies the coarse-minus-fine "
                            + "predictive memory with a nonnegative conditional-information gain. "
                            + "The displayed inequality is its direct monotonicity consequence."))),
                DescribeRole.Theorem))));

    private static Formula MonotonicityFormula()
    {
        Formula past = F.Id("P");
        Formula future = F.Id("F");
        Formula fineCarrier = F.Id("Fine");
        Formula coarseCarrier = F.Id("Coarse");
        Formula p = F.Id("p");
        Formula z = F.Id("z");
        Formula fine = F.Id("qf");
        Formula coarse = F.Id("qc");
        Formula pz = Seq(p, Open, z, Close);
        Formula law = Seq(
            Open, Forall, Sp, z, Comma, Sp, D(0), Sp, Leq, Sp, pz, Close,
            Sp, Land, Sp, Sum, Underscore, Grp(z), Sp, pz, Sp, Eq, Sp, D(1));
        Formula refines = Seq(
            Operatorname, Grp(F.Id("Refines")), Open, coarse, Comma, Sp, fine, Close);
        Formula fineMemory = Seq(
            Operatorname, Grp(F.Id("predictiveMemory")),
            Open, p, Comma, Sp, fine, Close);
        Formula coarseMemory = Seq(
            Operatorname, Grp(F.Id("predictiveMemory")),
            Open, p, Comma, Sp, coarse, Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, past, Comma, Sp, future, Comma, Sp,
            fineCarrier, Comma, Sp, coarseCarrier, Comma, RowBreak, Grp(),
            OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, past, Close,
            CloseBracket, Sp,
            OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, future, Close,
            CloseBracket, Sp,
            OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, fineCarrier, Close,
            CloseBracket, Sp,
            OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, coarseCarrier, Close,
            CloseBracket, Comma, RowBreak, Grp(),
            p, Colon, Sp, past, Sp, Times, Sp, future, Sp, To, Sp,
            Mathbb, Grp(F.Id("R")), Comma, RowBreak, Grp(),
            law, Sp, Rightarrow, RowBreak, Grp(),
            Forall, Sp, fine, Colon, Sp, past, Sp, To, Sp, fineCarrier,
            Comma, Sp, coarse, Colon, Sp, past, Sp, To, Sp, coarseCarrier,
            Comma, RowBreak, Grp(),
            refines, Sp, Rightarrow, RowBreak, Grp(),
            fineMemory, Sp, Leq, Sp, coarseMemory, Dot,
            End, Grp(F.Id("gathered"))));
    }
}

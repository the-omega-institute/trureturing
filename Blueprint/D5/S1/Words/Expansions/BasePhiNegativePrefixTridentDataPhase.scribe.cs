using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Expansions;

internal sealed class BasePhiNegativePrefixTridentDataPhaseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact core-gap data corrects the recursive-state projection and isolates the remaining global recurrence obligation.",
        H("Data-Derived Frontier Gap Phases"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("data-frontier-gap-selector-prefix010-zero"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Expansions/BasePhiNegativePrefixTridentDataPhase.dataFrontierGapSelector_prefix010_zero"),
                H("The corrected selector returns eleven for prefix 010"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("dataFrontierGapSelector")), Open,
                    F.Id("c"), Comma, D(0), Close, Eq, D(1, 1)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The executable prefix certificate for 010 is the recursive state G0o with return values "
                    + "eleven and seven. The data-derived projection sends G0o to family F, whose first letter "
                    + "therefore selects the observed first core gap eleven."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("data-phase-enriched-core-trace-iff-gap-phase"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Expansions/BasePhiNegativePrefixTridentDataPhase.data_phase_enriched_core_trace_iff_gap_phase"),
                H("Data-labeled traces are equivalent to the corrected gap phase"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("w"), Comma, F.Id("c"), Comma, Esc,
                    Operatorname, Grp(F.Id("FrontierReturnWordFor")), Open,
                    F.Id("w"), Comma, F.Id("c"), Close, Sp, Rightarrow, Sp,
                    Open,
                    Operatorname, Grp(F.Id("DataPhaseEnrichedCoreTrace")), Open,
                    F.Id("w"), Comma, F.Id("c"), Close, Sp, Leftrightarrow, Sp,
                    Operatorname, Grp(F.Id("DataFrontierGapPhase")), Open,
                    F.Id("c"), Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A corrected data-labeled adjacent-core trace exists exactly when the return-word certificate "
                    + "satisfies the data-derived selector at every index. The theorem supplies the reconstruction "
                    + "interface without claiming the still-open global trace existence result."))),
                DescribeRole.Theorem))));
}

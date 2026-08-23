using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Expansions;

internal sealed class BasePhiNegativePrefixTridentEdgeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict core enumerations have unique adjacent successors, while phase enrichment isolates the remaining gap-phase obligation.",
        H("Phase-Enriched Adjacent Core Edges"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("frontier-consecutive-core-adjacent"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Expansions/BasePhiNegativePrefixTridentEdge.frontier_consecutive_core_adjacent"),
                H("Consecutive frontier values form adjacent core edges"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("w"), Comma, F.Id("c"), Comma, F.Id("n"), Comma, Esc,
                    Operatorname, Grp(F.Id("FrontierReturnWordFor")), Open,
                    F.Id("w"), Comma, F.Id("c"), Close, Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("AdjacentCorePoint")), Open,
                    F.Id("w"), Comma,
                    F.Id("c"), Dot, Operatorname, Grp(F.Id("enumerate")), Open,
                    F.Id("n"), Close, Comma,
                    F.Id("c"), Dot, Operatorname, Grp(F.Id("enumerate")), Open,
                    F.Id("n"), Plus, D(1), Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every pair of consecutive values in a complete strict core enumeration is an adjacent core pair. "
                    + "The accompanying endpoint-uniqueness theorem forces every other locally adjacent candidate "
                    + "to equal the enumerated successor."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("phase-enriched-core-trace-iff-gap-phase"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Expansions/BasePhiNegativePrefixTridentEdge.phase_enriched_core_trace_iff_gap_phase"),
                H("Phase-enriched traces are equivalent to the exact gap phase"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("w"), Comma, F.Id("c"), Comma, Esc,
                    Operatorname, Grp(F.Id("FrontierReturnWordFor")), Open,
                    F.Id("w"), Comma, F.Id("c"), Close, Sp, Rightarrow, Sp,
                    Open,
                    Operatorname, Grp(F.Id("PhaseEnrichedCoreTrace")), Open,
                    F.Id("w"), Comma, F.Id("c"), Close, Sp, Leftrightarrow, Sp,
                    Operatorname, Grp(F.Id("FrontierGapPhase")), Open,
                    F.Id("c"), Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A phase-enriched adjacent-core trace exists exactly when the certificate satisfies its "
                    + "phase-selected additive gap equation. This equivalence preserves the six-state label "
                    + "without manufacturing the missing enriched-edge existence witness."))),
                DescribeRole.Theorem))));
}

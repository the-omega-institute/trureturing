using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233255RecurrenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original seven-column individual-array count satisfies Hardin's five-step recurrence.",
        H("Literal positive-height recurrence"),
        Blocks(
            Paragraph(Text("The count is the original function count in HardinA233255PairTransfer.a: "
                + "seven columns, six colours, first cell zero, horizontal and upper-right/lower-left "
                + "antidiagonal exclusions, and the strict row-major earlier-occurrence conditions. "
                + "Missing colours are allowed. There is no vertical, main-diagonal or wrap constraint, "
                + "and no quotient by a symmetry group.")),
            Paragraph(Text("The canonical count bridge gives 16 times 128 to the power m plus 32 times "
                + "the sum of the sixteen completed-state coordinates at continuation height m. The "
                + "matrix certificate first checks every entry against the actual compatible proper "
                + "seven-cell row fibres. An extra coordinate retains the exponential correction. "
                + "The six explicit vectors are checked powers of this actual seventeen-coordinate "
                + "transfer on the all-ones vector. Their exact degree-five vector identity propagates "
                + "to every height by multiplication with arbitrary further matrix powers.")),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(
                "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255Recurrence.result"),
                H("The all-height five-step recurrence"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Automata/hardin2013a233255")),
                Blocks(Paragraph(Text("For every natural n at least six, "
                    + "a(n) equals 5504 a(n-1) minus 6438912 a(n-2) plus 2774532096 a(n-3) minus "
                    + "478351982592 a(n-4) plus 27831388078080 a(n-5), in the integers. All six "
                    + "heights belong to the positive source domain. The onset n at least six is the "
                    + "all-positive-predecessors explication; the source labels its recurrence Empirical "
                    + "without an explicit onset. No count at height zero is introduced."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin233255"), ResolutionKind.Proved)),
            Paragraph(Text("Source: R. H. Hardin, OEIS A233255, The On-Line Encyclopedia of Integer "
                + "Sequences, OEIS Foundation Inc., https://oeis.org/A233255; source licensing: "
                + "https://oeis.org/LICENSE. The source statement is a conjectural input, and the "
                + "formal certificate and literal bridge supply the proof.")),
            Paragraph(Text("Problems/hardin233255.md states the complete original recurrence event, "
                + "its clause correspondence, proof mechanism, literature boundaries and follow-up questions. "
                + "Library/Automata/hardin2013a233255.md records the source locators and quotation licence. "
                + "The resolution concerns the entire literal count at every n at least six.")),
            Paragraph(Text("Information-escape registration remains declared_unresolved for "
                + "LiteralBridge.scanner_fibres (IE-C050 ClosedTruthReadout reason=unclassified_form "
                + "rule=source.params), PairTransfer.continuation_pair_bridge and Recurrence.result "
                + "(each IE-C050 ClosedTruthReadout reason=unclassified_form rule=source.state_binder). "
                + "The original source-binding certificates are missing. The disclosures are "
                + "https://github.com/the-omega-institute/trureturing/issues/28328#issuecomment-6732072411 "
                + "and https://github.com/the-omega-institute/trureturing/issues/28328#issuecomment-6732792448. "
                + "These three audits are unfinished; they are not validated registrations.")))));
}

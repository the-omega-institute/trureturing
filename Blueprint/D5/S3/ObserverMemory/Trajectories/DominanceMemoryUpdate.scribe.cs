using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Trajectories;

internal sealed class DominanceMemoryUpdateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact dominance memory updates and original readout for every binary window.",
        H("Dominance Memory for Actual Binary Windows"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-complete-runs-shift"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Trajectories/DominanceMemoryUpdate.actual_complete_runs_shift"),
                H("Complete runs, suffix closure, and actual transport"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix a positive window length R. Positions are numbered from zero to R-1; position "
                            + "i corresponds to relative coordinate i-R. A finite set s of positions less than R "
                            + "specifies exactly the observed one bits. A complete positive zero run has two "
                            + "observed one endpoints a and b, at least one position between them, and no "
                            + "interior one. Thus truncated boundary runs are excluded.")),
                    Paragraph(Text(
                        "The number pastLast s is one past the latest observed one, or zero when s is empty. "
                            + "Consequently ell=R-pastLast s is the full trailing zero length, truncated at R. "
                            + "After the oldest bit is removed and x is appended, a complete run ending before "
                            + "R-1 corresponds exactly to the old run with both endpoints increased by one. "
                            + "A run closing at R-1 exists exactly when x is one, ell is positive, and ell+2 "
                            + "does not exceed R; its new endpoints are R-ell-2 and R-1.")),
                    Paragraph(Text(
                        "The trailing length becomes zero for a new one, and min(R,ell+1) for a new zero. "
                            + "For every surviving closing position b, the parity of all actual zero bits "
                            + "strictly after b becomes its old parity XOR the complement of x. The proof "
                            + "reindexes the actual zero positions and accounts separately for the new last "
                            + "position. It includes zeros in runs that a dominance filter subsequently discards."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-window-update"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Trajectories/DominanceMemoryUpdate.actual_window_update"),
                H("Canonical memory commutes with the actual shift"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every binary window of every positive length R, retain precisely the complete "
                            + "runs for which every later closing run is strictly shorter. Each retained record "
                            + "stores its two endpoints and the actual transport parity after its closing one. "
                            + "The memory consists only of this finite record set and ell; it has no window "
                            + "or history field.")),
                    Paragraph(Text(
                        "The update first removes records with left endpoint zero. It subtracts one from "
                            + "both endpoints of each survivor and XORs its phase with the complement of x. "
                            + "When x is one and 1 <= ell with ell+2 <= R, it deletes survivors of length at "
                            + "most ell and inserts the record (R-ell-2,R-1,false). Otherwise it inserts no "
                            + "record. It updates the trailing length as above. This state-only result equals "
                            + "the canonical memory freshly calculated from the shifted actual window.")),
                    Paragraph(Text(
                        "The essential deletion argument uses the actual endpoint geometry. If a complete "
                            + "run closes before another, its closing endpoint is at or before the other's "
                            + "left endpoint. A later dominator therefore survives whenever the dominated run "
                            + "survives; deleting expired candidates cannot revive a discarded run. A newly "
                            + "closed run dominates exactly the surviving runs no longer than itself.")),
                    Paragraph(Text(
                        "The same readout returns the endpoints chosen by the original longest-run selector, "
                            + "the following vertex as anchor, and the Boolean value of sharedRule. It maximizes "
                            + "length first and closing "
                            + "endpoint second, preserving the latest-endpoint tie-break. The returned closing "
                            + "endpoint b determines the anchor b+1, or relative coordinate b+1-R. Empty "
                            + "memory returns no selected candidate and direction false. All binary inputs "
                            + "are covered, including short windows, empty candidate sets, and simultaneous "
                            + "expiry and closure. No legality counter or state-count estimate is asserted."))),
                DescribeRole.Theorem))));
}

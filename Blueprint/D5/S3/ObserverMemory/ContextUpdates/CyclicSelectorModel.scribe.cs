using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.ContextUpdates;

internal sealed class CyclicSelectorModelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The cyclic selector model keeps every labelled source coordinate and the complete observation trace.",
        H("Cyclic Selector Model"),
        Blocks(
            Paragraph(
                Ref("D5/S3/ObserverMemory/ContextUpdates/CyclicSelectorModel"),
                Text(" defines G = ZMod 2 times ZMod m. A source consists of one receiver, "
                    + "r-1 labelled senders and the second coordinate of a kernel offset h. "
                    + "Its clock is the receiver plus the sender sum plus h. "
                    + "An observation keeps the receiver, this clock and every sender reply; "
                    + "the reply subtracts the selected element exactly for a nonzero binary coordinate.")),
            Paragraph(Text(
                "The selector is (1,0) or (1,m/2), chosen by f at the receiver phase. "
                + "After j natural repetitions, the receiver gains (0,j), the first labelled sender "
                + "loses (0,j), and all other coordinates stay fixed. The trace of horizon n records "
                + "the observations at every time from zero through n. The recovery function takes "
                + "two snapshots and their known times. Its arithmetic companion returns the same "
                + "coordinate construction together with a specified group-operation and comparison ledger.")),
            Paragraph(Text(
                "Forward and backward first-change distances use the least positive index at which "
                + "f differs from its initial value, with zero reserved for absence of a change. "
                + "A run start has f(s-1) different from f(s), and a run position is a start paired "
                + "with an index below its forward distance. Constant windows include both endpoints. "
                + "Their phase count and the quotient count of sources with equal complete traces "
                + "are definitions on the actual source and phase spaces.")),
            Describe.Lean(
                DescribeId.Create("cyclic-selector-source-geometry"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/ContextUpdates/CyclicSelectorModel."
                    + "cyclic_selector_source_geometry"),
                H("Cyclic run geometry and actual source fibers"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For natural m and r, with m nonzero, even and at least two, r at least "
                        + "three, and any fixed f from ZMod m to ZMod 2, the theorem constructs "
                        + "the actual run geometry, recovers labelled sources, characterizes trace "
                        + "fibers and realizes every H-valued snapshot.")),
                    Paragraph(Text(
                        "If f is nonconstant, there is an equivalence from phases to actual run "
                        + "positions. Its inverse sends a start s and position k to s+k; the phase "
                        + "z maps to start z-(beta(z)-1) and position beta(z)-1. The remaining "
                        + "first-change distance is delta(s)-k. Every delta is between one and "
                        + "m-1, and for every natural horizon n the number of constant windows "
                        + "is the sum over starts s of max(delta(s)-n,0). There is a longest run "
                        + "length L between one and m-1: all distances are at most L, every "
                        + "depth from one through L occurs, and all constant windows disappear "
                        + "exactly at horizons n at least L.")),
                    Paragraph(Text(
                        "For every original source and every natural time j, the clock is "
                        + "unchanged. At any two supplied natural times p and q from that same "
                        + "source, different selector labels suffice for the recovery function "
                        + "to return the entire original source, including sender 2 and h, "
                        + "after undoing the known endpoint translations. For any two fixed "
                        + "sources with the same initial snapshot and any natural horizon n, "
                        + "their complete traces agree exactly when the sources are equal or "
                        + "f remains constant on the first source's phase window from zero "
                        + "through n. The horizon includes n+1 observations.")),
                    Paragraph(Text(
                        "Whenever the selector label at time j equals its initial label, "
                        + "the snapshot is computable from the initial one by translating the "
                        + "receiver by (0,j), keeping the clock, and subtracting (0,j) from "
                        + "sender 2's reply alone. At every phase the base source and the source "
                        + "with exactly senders 2 and 3 flipped are distinct and share the "
                        + "initial snapshot; their traces agree exactly on constant windows. "
                        + "For every j and source, j iterations of the sole unit update equal "
                        + "the defined advance by j.")),
                    Paragraph(Text(
                        "For every receiver a, clock t and H-valued reply tuple u, each "
                        + "binary bitstring with sum chi(t)-chi(a) realizes the snapshot "
                        + "through x_i=u_i+epsilon_i c and h=t-a-sum_i x_i. Conversely every "
                        + "source with that snapshot satisfies this parity equation and is "
                        + "exactly its fiberSource reconstruction. Such a source exists for "
                        + "every proposed snapshot, including r=3. Only the run-geometry "
                        + "clause assumes nonconstant f; all the source, trace and realization "
                        + "clauses also hold for constant f, without a positive first-change "
                        + "boundary.")),
                    Paragraph(
                        Text("The theorem in "),
                        Ref("D5/S3/ObserverMemory/ContextUpdates/CyclicSelectorRecovery"),
                        Text(" consumes this construction to prove the exact source and trace "
                            + "cardinalities and the arithmetic operation ledger. The construction "
                            + "here makes no bit-time, communication or physical-time cost claim."))),
                DescribeRole.Theorem))));
}

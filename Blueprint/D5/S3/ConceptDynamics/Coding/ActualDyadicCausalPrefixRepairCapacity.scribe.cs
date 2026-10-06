using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class ActualDyadicCausalPrefixRepairCapacityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual acquired prefixes support causal fixed labels and uniform closed-error recovery.",
        H("Actual Causal Prefix Recovery"),
        Blocks(Describe.Lean(
            DescribeId.Create("actual-acquired-prefix-and-final-query"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/Coding/ActualDyadicCausalPrefixRepairCapacity."
                    + "actual_acquired_prefix_and_final_query"),
            H("Successful actual schedules acquire the prefix before the final query"),
            StatementSource.FromAuthor(Disp(Seq(
                F.Id("AllSourceActualSuccess"), Sp, Implies, Sp,
                F.Id("ReachedChronologicalPrefixAndPairLocalFinalQuery")))),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Fix P=2^(d+1), the known initial bit and one deterministic policy. "
                    + "Every source has a finite successful actual execution identifying "
                    + "it using at most d+1 new reads. Every such execution has exactly "
                    + "d+1 reads. Sources with the same quotient by two have a common "
                    + "pre-final history of d reads and a common literal final query N.")),
                Paragraph(Text(
                    "The pre-final history is reached by the primitive forward and read "
                    + "actions. Each acquired raw bit is normalized modulo two using "
                    + "the known initial bit and its recorded event quotient. Starting "
                    + "at v=0, the chronological update v=2v+e returns floor(r/2) on "
                    + "that history, before the last raw bit or any clock noise exists. "
                    + "Thus any chosen mathematical prefix label factors through this record.")),
                Paragraph(Text(
                    "Capacity and interval inputs are derived from all-source success. "
                    + "The forced midpoint trace is derived for each actual execution. "
                    + "Induction over that trace proves the chronological fold law. "
                    + "A separate physical execution split locates the record preceding "
                    + "the last read. Silent reporting advances preserve the read list.")),
                Paragraph(Text(
                    "N mod P=P-1-2 floor(r/2), and the final raw bit is "
                    + "(b+floor(N/P)+(r mod 2)) mod 2. Whole-period waits are retained "
                    + "in the quotient. Common N is asserted only within a source pair. "
                    + "This statement does not establish noisy circle geometry, a "
                    + "uniform all-error decoder, or the complete label minima."))),
            DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("actual-causal-closed-error-recovery"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/Coding/ActualDyadicCausalPrefixRepairCapacity."
                    + "actual_causal_closed_error_recovery"),
            H("Actual causal labels separate closed phase overlaps exactly"),
            StatementSource.FromAuthor(Disp(Seq(
                F.Id("AllSourceActualSuccess"), Sp, Implies, Sp,
                F.Id("OperationalMinimumAndUniformCausalDecoderCriterion")))),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "All-source finite successful executions supply a history and literal "
                    + "last query for each source. Every actual bounded successful execution "
                    + "has that final read record. The chronological normalized prefix is "
                    + "floor(r/2). History equality holds exactly within each source pair, "
                    + "and its last query is common within that pair.")),
                Paragraph(Text(
                    "The real-circle distance between actual final phases equals twice "
                    + "the integer circular distance between prefixes. The proof handles "
                    + "both the direct arc and the arc crossing the seam, including equality "
                    + "and antipodal points. Two closed phase balls overlap exactly when "
                    + "the center distance is at most twice the nonnegative error bound. "
                    + "The overlap witness is a midpoint in a real lift, then quotiented.")),
                Paragraph(Text(
                    "One prefix label is realized by a writer on the reached pre-final "
                    + "record. It precedes the final bit and every clock error. A single "
                    + "receiver works for all actual sources and all admissible errors "
                    + "exactly when equal labels never occur on overlapping distinct "
                    + "prefixes. Necessity selects two actual source bits yielding Y=0 "
                    + "and one shared admissible phase; these are two source realizations.")),
                Paragraph(Text(
                    "For sufficiency, the mathematical receiver selects a prefix using "
                    + "the phase and label alone. The fixed known policy determines its "
                    + "event quotient. Subtracting b and that quotient from Y in ZMod 2 "
                    + "recovers the last source bit. The arbitrary default is used only "
                    + "outside the admissible actual image. Retaining the full prefix "
                    + "proves feasibility and existence of the least operational alphabet, "
                    + "defined by receiver feasibility. This is an existence result for "
                    + "fixed known b and policy; no executable replay or running-time "
                    + "bound is asserted.")),
                Paragraph(Text(
                    "The result does not give the complete numerical label regimes or "
                    + "their supplementary-bit costs. Alphabet compression measures "
                    + "supplementary terminal information; it does not measure all memory "
                    + "used by the acquisition controller or the known policy."))),
            DescribeRole.Theorem))));
}

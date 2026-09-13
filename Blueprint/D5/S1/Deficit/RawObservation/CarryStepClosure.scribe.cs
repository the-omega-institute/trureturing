using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Deficit.RawObservation;

internal sealed class CarryStepClosureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An unbounded raw-input family defeats next-step recovery even after adding current canonicality to every shift reading.",
        H("Shift Observations Do Not Close Actual Carry Dynamics"),
        Blocks(
            Paragraph(Text("The carrier, evaluator, shift probes, signed normalization charge and deterministic carryPass are the existing ones. The operation is a genuine local carry, not the raw-position shift used by the earlier reconstruction theorem. No stochastic game kernel is assumed.")),
            Describe.Lean(
                DescribeId.Create("actual-carry-closure-failure"),
                DeclarationHandle.Create("D5/S1/Deficit/RawObservation/CarryStepClosure.actual_carry_closure_failure"),
                H("A same-observation pair with distinct actual next golden values"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each natural k, the two raw inputs have multiplicities (2,2,0,0,k) and (0,0,2,0,k). Both display 6+8k, have the same golden value and therefore equal all-shift readings and total normalization charge. Both are noncanonical. The least repeated slot is respectively zero or two, so carryPass performs different real constructors. The next golden values differ by exactly one ordinary integer. This is an unbounded family, not a sampled collision."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("no-shift-and-canonicality-next-map"),
                DeclarationHandle.Create("D5/S1/Deficit/RawObservation/CarryStepClosure.no_shift_and_canonicality_next_map"),
                H("The complete shift datum plus a Boolean guard is still insufficient"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("No function of the entire shift-readout sequence and the current canonicality flag can recover the next golden value under carryPass. The proof applies the concrete pair above and cancels the identical input data. The conclusion concerns this specified observation and update, not the impossibility of finding any more informative state. It strengthens the earlier failure of shift-only canonicality recovery: even supplying that missing Boolean value does not close the transition."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Deficit/RawObservation/NormalizationResidual")),
        ]));
}

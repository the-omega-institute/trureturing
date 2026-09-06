using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class SkeletonSlotGapConstraintTransportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/SkeletonSlotGapConstraintTransport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual slot runs induce the original finite shared-selection constraints and their terminal observation domains.",
        H("Slot Gap Constraint Transport"),
        Blocks(
            Describe.Lean(DescribeId.Create("slot-gap-blocks"), DeclarationHandle.Create(Prefix + "gapBlocks"), H("Gap blocks"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("A gap index k expands to oneZero followed by k zero return blocks."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("slot-gap-code"), DeclarationHandle.Create(Prefix + "gapCode"), H("Gap code"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The two original terminal channels end in one or in one followed by zero."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("slot-gap-readout"), DeclarationHandle.Create(Prefix + "slotReadout"), H("Slot readout"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Both readouts come from the original slot and return fields."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("slot-gap-trace"), DeclarationHandle.Create(Prefix + "traceFrom"), H("Gap trace"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("A finite fold of the already derived gap maps."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("slot-gap-eval"), DeclarationHandle.Create(Prefix + "eval_gapCode"), H("Original evaluation agrees with the gap trace"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Induction proves the equation for arbitrary gap lists and both terminal channels."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("slot-gap-index"), DeclarationHandle.Create(Prefix + "variableIndex"), H("Variable indexing"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Standard finite sum and product equivalences assign table and trace coordinates."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("slot-gap-selection"), DeclarationHandle.Create(Prefix + "gapSelection"), H("Selection constraint"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The existing finite-domain Selection type owns the local equation."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("slot-gap-color"), DeclarationHandle.Create(Prefix + "traceColor"), H("Actual trace color"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The color is computed from the actual slot witness."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("slot-gap-assignment"), DeclarationHandle.Create(Prefix + "inducedAssignment"), H("Induced assignment"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Actual table entries and actual prefix states fill the finite variables."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("slot-gap-equation"), DeclarationHandle.Create(Prefix + "induced_selection_holds"), H("Incidence gives the selection equation"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("A syntactic prefix-append identity yields the same deterministic local equation used by the checker."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("slot-gap-domains"), DeclarationHandle.Create(Prefix + "observationDomains"), H("Observation domains"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Only the stated terminal observations restrict trace domains. Unobserved outputs are not copied from the reference machine."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("slot-gap-domain-proof"), DeclarationHandle.Create(Prefix + "induced_assignment_in_domains"), H("Fitted observations give domain membership"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The original evaluation equation proves membership without an assumed replacement-machine correctness field."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("slot-gap-solution"), DeclarationHandle.Create(Prefix + "fitted_slots_induce_selection_solution"), H("Every fitted slot witness induces a solution"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("This is the slot-to-CSP transport. Concrete parsing, anchor normalization and evaluation of an external refutation remain separate obligations."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Certificates/SkeletonSlotZeroResponse")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Certificates/FiniteDomainSelectionRefutation"))]));
}

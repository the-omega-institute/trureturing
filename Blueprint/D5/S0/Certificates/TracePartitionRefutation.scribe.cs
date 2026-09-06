using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class TracePartitionRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/TracePartitionRefutation.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Congruence and complete reuse-or-fresh branching refute the existing bounded FitsTrace problem, with exact recurrent and signature costs.",
        H("Trace Partition Refutation"),
        Blocks(
            Describe.Lean(DescribeId.Create("trace-partition-Respects"), DeclarationHandle.Create(Prefix + "Respects"), H("Respects"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Branch equalities constrain the actual trace colors."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("trace-partition-Equality"), DeclarationHandle.Create(Prefix + "Equality"), H("Equality"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("A finite congruence derivation uses original trace roots and same-symbol edges."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("trace-partition-equality-sound"), DeclarationHandle.Create(Prefix + "equality_sound"), H("equality sound"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Every derived equality holds in each fitted existing skeleton that respects the branch equalities."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("trace-partition-Refutation"), DeclarationHandle.Create(Prefix + "Refutation"), H("Refutation"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Each split keeps every reuse case and a fresh-state case whenever the cardinal budget permits it."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("trace-partition-refutation-sound"), DeclarationHandle.Create(Prefix + "refutation_sound"), H("refutation sound"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("A hypothetical fitted machine follows one retained branch until a proved observation or distinguished-state conflict."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("trace-partition-refutation-excludes-fitted-skeleton"), DeclarationHandle.Create(Prefix + "refutation_excludes_fitted_skeleton"), H("refutation excludes fitted skeleton"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("This consumes the original FitsTrace, including partial Option-valued transitions. No new machine semantics is supplied."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("trace-partition-signature-clique-card-le"), DeclarationHandle.Create(Prefix + "signature_clique_card_le"), H("signature clique card le"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Distinct actual output-return pairs inject into the existing ReturnPairFiber. Merely different variable names do not suffice."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("trace-partition-simultaneous-state-signature-cost"), DeclarationHandle.Create(Prefix + "simultaneous_state_signature_cost"), H("simultaneous state signature cost"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The recurrent representatives and signature witnesses bound the same canonical state cost. The external checker must establish the pairwise separation premises."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Certificates/SkeletonSlotCNF"))]));
}

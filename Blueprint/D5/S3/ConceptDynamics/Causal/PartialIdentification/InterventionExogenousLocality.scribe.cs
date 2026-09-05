using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Causal.PartialIdentification;

internal sealed class InterventionExogenousLocalityDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/Causal/PartialIdentification/InterventionExogenousLocality.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Parent-indexed evaluation traces induce conservative source supports for finite counterfactual queries. Constant interventions remove dependencies, and source restriction preserves each certified query.",
        H("Intervention-specific exogenous locality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exogenous-locality"),
                DeclarationHandle.Create(Prefix + "ExogenousLocality"),
                H("Local exogenous-coordinate contract"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For fixed parent values, each equation satisfies the pinned Mathlib DependsOn predicate on its declared source set. No distributional independence is assumed."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("equation-support"),
                DeclarationHandle.Create(Prefix + "equationSupport"),
                H("Dependency transfer at one equation"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A constant intervention has empty incoming support. Otherwise the transfer unions local exogenous coordinates with current supports of declared parents."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("step-support"),
                DeclarationHandle.Create(Prefix + "stepSupport"),
                H("Coordinatewise support update"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The support map changes at exactly the coordinate changed by the canonical structural evaluation step."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("trace-support"),
                DeclarationHandle.Create(Prefix + "traceSupport"),
                H("Support propagation along the trace"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The transfer follows the supplied finite evaluation list. The result is a sound upper approximation, rather than a minimal essential-variable set."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("evaluated-response"),
                DeclarationHandle.Create(Prefix + "evaluatedResponse"),
                H("Reuse the unique structural response"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The response is selected from the existing parent-ordered evaluation theorem. No alternative evaluator is introduced."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("evaluated-response-spec"),
                DeclarationHandle.Create(Prefix + "evaluatedResponse_spec"),
                H("Bind the readout to canonical semantics"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The selected response satisfies the existing EvaluationWitness relation at the original initial state."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("compiled-support"),
                DeclarationHandle.Create(Prefix + "compiledSupport"),
                H("Account for all initial-state dependencies"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Initialization starts with all source coordinates admitted. Consequently arbitrary exogenous dependence in model.initial is included in the soundness argument."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("evaluated-response-depends-on"),
                DeclarationHandle.Create(Prefix + "evaluatedResponse_dependsOn"),
                H("Soundness on the full exogenous assignment space"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Trace induction proves that agreeing on the compiled coordinates forces agreement of the evaluated intervention response."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("compiled-support-antitone-intervention"),
                DeclarationHandle.Create(Prefix + "compiledSupport_antitone_intervention"),
                H("Added constant interventions shrink supports"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Enlarging the intervention set can only remove compiled dependencies. Query values and identified intervals are not asserted to be monotone."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("counterfactual-support"),
                DeclarationHandle.Create(Prefix + "counterfactualSupport"),
                H("Union supports across queried worlds"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A finite family of intervention queries reads the union of its intervention-specific supports."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("counterfactual-readout"),
                DeclarationHandle.Create(Prefix + "counterfactualReadout"),
                H("One source assignment for all worlds"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("All potential outcomes are evaluated from the same exogenous assignment. Cross-world coupling is preserved."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("counterfactual-readout-depends-on"),
                DeclarationHandle.Create(Prefix + "counterfactualReadout_dependsOn"),
                H("Joint counterfactual locality"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every coordinate of the finite readout is constant on fibers of the union-support restriction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("counterfactual-event-factors-through"),
                DeclarationHandle.Create(Prefix + "counterfactualEvent_factorsThrough"),
                H("Query-preserving source restriction"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Any Boolean event on the readout factors through coordinate restriction using Mathlib FactorsThrough. This is a semantic descent theorem, not a finite novelty score or catalog-admission claim."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fork-support-cut-certificate"),
                DeclarationHandle.Create(Prefix + "fork_support_cut_certificate"),
                H("Remove a shared root by intervention"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In the four-node fork, fixing treatment leaves a common-root source in both outcome supports. Fixing the common root as well leaves the two separate local outcome sources."))),
                DescribeRole.Theorem))));
}

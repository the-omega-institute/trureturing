using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Spacetime;

internal sealed class InteriorArchiveTimeInvisibilityDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/Spacetime/InteriorArchiveTimeInvisibility.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Current-region correspondences preserve temporal-free observations.",
        H("Current Regions and Synchronized Prefixes"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("current-correspondence"),
                DeclarationHandle.Create(Prefix + "CurrentIsoData"),
                H("Current attributes, order and selection"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A current correspondence is a bijection of current events preserving attributes, the induced causal relation and selection. Inactive archive events need not have matching attributes. Temporal-free operations retain such correspondences: parallel composition uses a disjoint sum, while generated product uses a product of current parents. Generated current events form a causal antichain."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("temporal-free-reification"),
                DeclarationHandle.Create(Prefix + "reify_temporal_free"),
                H("Both binary slots have an exact execution sequence"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every finite native word without temporal composition has a sequence of unary, parallel and product steps with exactly its Option denotation on every balanced input. Both slots are retained, and every fixed balanced parameter is allowed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prefix-saturation"),
                DeclarationHandle.Create(Prefix + "saturated_runSteps"),
                H("Saturated prefixes have equal final charge"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Two current regions differ only in the time of one corresponding event with no incoming causal edge; position, sign, source and all selection bits agree. Collect the causal predicates before the first product and pull each back through preceding time shifts. Suppose every nonempty predicate is reached from the exceptional event on both sides, and both exceptional times lie below the first product threshold.")),
                    Paragraph(Text("Unary filters then preserve matching selection bits. Parallel steps add identical disjoint components and cannot create new incoming edges. At the first product, the exceptional time is below every current parent time in the fixed factor, so corresponding generated attributes agree. This also covers an empty current factor. Every remaining temporal-free step preserves the current correspondence. Without any product, equal signs and selection already give equal charge."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S3/ConceptDynamics/Spacetime/TotalCopyNormalization")),
         DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S3/ConceptDynamics/Spacetime/CoarseObservation"))]));
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Spacetime;

internal sealed class NativeTimeProfileDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite signed time profiles and exact native primitive updates.",
        H("Native Time Profiles"),
        Blocks(
            Describe.Lean(DescribeId.Create("successors"), DeclarationHandle.Create(Prefix + "successors"),
                H("Reflexive current successors"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite set retains complete timed attributes of the current event itself and all its current causal successors, including unselected targets."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cell"), DeclarationHandle.Create(Prefix + "cell"),
                H("Native event cell"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A current event determines its timed attribute, selected Boolean bit, and finite successor attribute set."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gamma"), DeclarationHandle.Create(Prefix + "gamma"),
                H("Signed finite time profile"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Sum signed singleton cell measures over every current event. Noncurrent archive events contribute no cells. Events in the same cell add their integer coefficients."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("push"), DeclarationHandle.Create(Prefix + "push"),
                H("Linear cell transport"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Transport a finitely supported integer profile along a cell map, adding coefficients when cells merge."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("readout"), DeclarationHandle.Create(Prefix + "readout"),
                H("Terminal selected charge"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This integer linear functional weights selected cells by one and unselected cells by zero."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("readout-gamma"), DeclarationHandle.Create(Prefix + "readout_gamma"),
                H("Terminal readout equals native charge"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every rich native history, applying the selected-cell functional to its complete time profile gives precisely its native q readout."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("shift-attribute"), DeclarationHandle.Create(Prefix + "shiftAttribute"),
                H("Integer attribute shift"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Add an arbitrary integer to time while preserving position, sign and source."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("unary-cell"), DeclarationHandle.Create(Prefix + "unaryCell"),
                H("All five unary updates"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complement flips selection. Spatial and source filters conjoin their predicate with selection. Causal filtering tests whether the successor set hits the fixed timed-attribute predicate. Shifting changes both the own attribute and every successor attribute."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gamma-unary"), DeclarationHandle.Create(Prefix + "gamma_unary"),
                H("Native unary operations are linear pushes"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every balanced history and every native unary primitive, the actual output time profile equals the corresponding linear push of the input profile."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gamma-parallel"), DeclarationHandle.Create(Prefix + "gamma_parallel"),
                H("Parallel profiles add"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every pair of balanced histories, the complete profile of their tagged parallel composite is the sum of the two profiles. Actual current events are reindexed; each component retains its successor set."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("product-attribute"), DeclarationHandle.Create(Prefix + "productAttribute"),
                H("Generated product attribute"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Generated time is the maximum parent time plus one. Positions add, signs multiply via Boolean equality, and sources form the ordered tree product."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("product-cell"), DeclarationHandle.Create(Prefix + "productCell"),
                H("Generated product cell"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Parent selection bits conjoin. The successor set of a newly generated current event is the singleton containing its own generated attribute."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("product-push"), DeclarationHandle.Create(Prefix + "productPush"),
                H("Bilinear cell push"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Extend the generated cell operation by integer bilinearity in the two finitely supported profiles."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gamma-product"), DeclarationHandle.Create(Prefix + "gamma_product"),
                H("Native product equals the bilinear push"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every pair of balanced histories, the actual generated-product profile equals the bilinear push of the two parent profiles. The proof uses the exact parent-pair current equivalence and absence of paths out of generated nodes."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pack"), DeclarationHandle.Create(Prefix + "pack"),
                H("Homogenized native profile"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A balanced native history is embedded as the pair consisting of the integer one and its complete time profile. The extra coordinate represents constants in the multilinear syntax interpretation."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("model"), DeclarationHandle.Create(Prefix + "model"),
                H("Multilinear interpretation of the copy syntax"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each input occurrence occupies a distinct multilinear coordinate. Constants use the empty coordinate family. Unary nodes use linear profile pushes. Binary nodes combine disjoint leaf families using bilinear homogenized parallel or product maps. Temporal nodes are assigned parallel semantics here; the correctness theorem explicitly requires temporal freedom."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("model-eval"), DeclarationHandle.Create(Prefix + "model_eval"),
                H("The multilinear model computes native evaluation"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every arity, temporal-free copy term, independent balanced leaf assignment and successful native result, applying the multilinear model to the packed leaves gives exactly the packed result. Structural induction consumes the native unary, parallel and product profile updates. This connects the formal multilinear interpretation to the actual finite native histories."))), DescribeRole.Theorem)
        ),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ConceptDynamics/Spacetime/CoarseObservation")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ConceptDynamics/Spacetime/TotalCopyNormalization"))
        ]));
}

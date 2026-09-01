using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Sheaf;

internal sealed class FiniteObserverSheafDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Sheaf/FiniteObserverSheaf.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite observer restrictions form a cellular zero-to-one coboundary whose kernel is the compatible-section space.",
        H("Finite Observer Sheaf Cochains"),
        Blocks(
            Def("network", "ObserverNetwork", "Finite observer network",
                "Vertex observations and edge overlaps are connected by linear endpoint restriction maps."),
            Def("coboundary", "observerCoboundary", "Observer coboundary",
                "The edge defect is target restriction minus source restriction."),
            Def("compatible", "Compatible", "Compatible local observer family",
                "Every pair of endpoint restrictions agrees on its overlap edge."),
            Def("sections", "compatibleSections", "Compatible-section submodule",
                "The global compatible families form the kernel of the observer coboundary."),
            Thm("zero", "compatible_iff_coboundary_eq_zero", "Compatibility is zero coboundary",
                "A local observer family is pairwise compatible exactly when every edge defect vanishes."),
            Thm("kernel", "mem_compatibleSections_iff", "Kernel membership is compatibility",
                "Membership in the compatible-section submodule is equivalent to the pairwise overlap condition."),
            Thm("add", "compatible_add", "Compatibility is additive",
                "The sum of two compatible local observer families remains compatible."),
            Thm("smul", "compatible_smul", "Compatibility is stable under scaling",
                "Scalar multiplication preserves compatible local observer families."),
            Thm("constant", "constant_compatible_of_same_restriction", "Equal restrictions admit constant sections",
                "When both endpoint restrictions coincide, every constant vertex family is compatible.")),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/ConceptDynamics/Gluing/SheafPairwiseEqualizer")),
        ]));

    private static DocumentBlock.Describe Def(
        string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))), DescribeRole.Definition);

    private static DocumentBlock.Describe Thm(
        string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))), DescribeRole.Theorem);
}

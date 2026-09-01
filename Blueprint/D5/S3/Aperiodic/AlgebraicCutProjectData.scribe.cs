using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Aperiodic;

internal sealed class AlgebraicCutProjectDataDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Aperiodic/AlgebraicCutProjectData.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Additive physical and internal projections define reusable model sets with exact window translation laws.",
        H("Algebraic Cut-and-Project Data"),
        Blocks(
            Def("data", "CutProjectData", "Cut-and-project projection data",
                "An additive lattice carrier is equipped with physical and internal additive projections."),
            Def("translate", "translateSet", "Internal window translation",
                "A translated window contains a point when shifting it back reaches the original window."),
            Def("model-set", "modelSet", "Window-selected model set",
                "Physical projections are selected by membership of the corresponding internal projections in a window."),
            Thm("mono", "modelSet_mono", "Window monotonicity",
                "Enlarging the internal window enlarges the physical model set."),
            Thm("union", "modelSet_iUnion", "Model sets preserve window unions",
                "An arbitrary union of internal windows becomes the union of their model sets."),
            Thm("translation", "modelSet_translate_lattice", "Exact lattice translation law",
                "Translation of a window by an internal lattice image translates the model set by the corresponding physical image."),
            Thm("intersection", "modelSet_inter_of_physical_injective", "Injective physical projection preserves intersections",
                "When physical projection is injective, one physical point cannot hide distinct lattice witnesses, so binary intersections are exact."),
            Thm("univ", "modelSet_univ", "Full window gives the physical range",
                "Selecting every internal point leaves exactly the range of the physical projection.")),
        []));

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

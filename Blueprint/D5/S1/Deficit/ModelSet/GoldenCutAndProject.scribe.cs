using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Deficit.ModelSet;

internal sealed class GoldenCutAndProjectDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The physical golden beta range lies in the golden-lattice cut-and-project set.",
        H("Golden Cut-and-Project Inclusion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-model-set-lies-in-cut-and-project-set"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/ModelSet/GoldenCutAndProject.golden_model_set_subset_cut_and_project"),
                H("The physical golden model set lies in the cut-and-project set"),
                StatementSource.FromAuthor(GoldenCutAndProjectInclusionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Each point of the golden model set is a canonical natural-number golden "
                            + "beta value. Its Minkowski embedding is a point of the golden lattice, "
                            + "and its physical coordinate is the original real embedding.")),
                    Paragraph(Text(
                        "The internal coordinate of that lattice point is the beta contraction. "
                            + "The public contraction bound places it in the closed golden window, "
                            + "so the physical value is selected by the cut-and-project construction. "
                            + "This proves only the displayed inclusion, not the reverse one."))),
                DescribeRole.Theorem))));

    private static Formula GoldenCutAndProjectInclusionFormula()
    {
        Formula point = F.Id("x");
        Formula physicalRange = new Formula.SetBuilder(
            Call("embedding", point),
            point,
            F.Id("goldenModelSet"));

        return F.Disp(new Formula.Relation(
            physicalRange,
            FormulaRelationOperator.SubsetOf,
            F.Id("goldenCutAndProjectSet")));
    }
}

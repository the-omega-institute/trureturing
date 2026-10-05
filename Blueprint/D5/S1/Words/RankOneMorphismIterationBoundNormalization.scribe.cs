using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class RankOneMorphismIterationBoundNormalizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "This source module supplies the machine-checked supporting declarations for the effective iteration bound formalization.",
        H("Morphism Iteration Bound Normalization"),
        Blocks(
            Describe.Remark(
                DescribeId.Create("module-overview"),
                DeclarationHandle.Create("D5/S1/Words/RankOneMorphismIterationBoundNormalization.charge_rotation_before"),
                H("Machine-checked supporting module"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This module is a repository-derived supporting slice for the effective "
                        + "iteration bound. Its declarations are checked by Lean in the actual "
                        + "binary rank-one morphism setting."))))));
}

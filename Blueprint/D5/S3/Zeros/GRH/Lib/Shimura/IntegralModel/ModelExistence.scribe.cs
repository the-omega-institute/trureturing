using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.IntegralModel;

internal sealed class ModelExistenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Model Existence", H("Model Existence"),
        Blocks(
            Paragraph(Text("Integral Kuga-Sato model with Hecke covers and congruence relation exists.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/IntegralModel/ModelExistence.exists_model"),
                H("exists_model"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Given a universal family for D over R (UniversalFamily), if the level 𝔑 is neat, β = (1 + √−d₀)/2 and every safe place is good for D, then for any positive finite number of marked points there is a model of level 𝔑 over R (Model).")))))));
}

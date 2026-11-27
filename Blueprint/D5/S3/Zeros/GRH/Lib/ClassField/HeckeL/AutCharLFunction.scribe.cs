using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.HeckeL;

internal sealed class AutCharLFunctionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Aut Char L Function", H("Aut Char L Function"),
        Blocks(
            Paragraph(Text("L-function of a base-changed U(1) character: type, symmetry, non-vanishing for s ≥ 1.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/HeckeL/AutCharLFunction.atUnif_star"),
                H("atUnif_star"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let ν have weight e and tame part ψ, with ψ_w and ψ_w̄ trivial. Then the Hecke character x ↦ ν(x/x̄) takes mutually inverse values at the chosen uniformisers at w̄ and at w.")))))));
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.LocalGL.Iwahori;

internal sealed class HeckeOnLineStabiliserDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hecke On Line Stabiliser", H("Hecke On Line Stabiliser"),
        Blocks(
            Paragraph(Text("U operator preserves character eigenspaces of the parahoric stabilising a line.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/LocalGL/Iwahori/HeckeOnLineStabiliser.heckeCoset_mem_parahoricEigenspace"),
                H("heckeCoset_mem_parahoricEigenspace"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For smooth ρ, a uniformiser ϖ and any function χ, the pro-p Iwahori Hecke operator of diag(ϖ,1,…,1) preserves the pro-p Iwahori fixed vectors on which each integral k fixing the first coordinate line modulo ϖ acts by χ of its top left entry.")))))));
}

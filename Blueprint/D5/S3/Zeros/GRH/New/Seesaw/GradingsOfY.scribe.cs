using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Seesaw;

internal sealed class GradingsOfYDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gradings Of Y", H("Gradings Of Y"),
        Blocks(
            Paragraph(Text("Levels, finite data, Weil actions and tame characters of the row lifts. Defines the indefinite chain of theta lifts, its levels, character and equivariance law. Gradings of the spaces Y_k and evaluated finite data for each pair.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Seesaw/GradingsOfY.iota_principalRep"),
                H("iota_principalRep"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The chain of lifts ι_μ commutes with the group 𝖦: ι_μ(s·y) is the right translate of ι_μ(y) by the finite element Data.groupLift attached to s.")))))));
}

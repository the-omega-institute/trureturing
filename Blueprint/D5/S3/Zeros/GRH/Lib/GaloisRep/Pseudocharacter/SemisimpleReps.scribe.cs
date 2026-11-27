using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.GaloisRep.Pseudocharacter;

internal sealed class SemisimpleRepsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Semisimple Reps", H("Semisimple Reps"),
        Blocks(
            Paragraph(Text("Wedderburn tools, Brauer-Nesbitt, Clifford, representation from a trace, continuity from the trace.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/GaloisRep/Pseudocharacter/SemisimpleReps.continuous_of_trace"),
                H("continuous_of_trace"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("A representation r of a topological group into GL_n(k), k a field with a ring topology, with non-degenerate trace form on the span of its image, is continuous as soon as its trace is continuous.")))))));
}

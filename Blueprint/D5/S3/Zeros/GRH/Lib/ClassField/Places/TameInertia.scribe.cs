using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.Places;

internal sealed class TameInertiaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Tame Inertia", H("Tame Inertia"),
        Blocks(
            Paragraph(Text("Structure of tame inertia: acts through roots of uniformiser, Frobenius acts by q.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/Places/TameInertia.tame_inertia"),
                H("tame_inertia"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let n be a unit of A, yⁿ a uniformiser of k, f on inertia with open kernel and fⁿ = 1. Then f kills the stabiliser of y, f(s) generates the image if sy/y has order n, and f(φsφ⁻¹) = f(s)^q for a q-Frobenius φ.")))))));
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.Fock;

internal sealed class FockActionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fock Action", H("Fock Action"),
        Blocks(
            Paragraph(Text("Cocycle identity for U(p,q): oscillator representation splits, by a complex Gaussian determinant.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/Fock/FockAction.realAction"),
                H("realAction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The linear action of U(ε) on ℂ^ι, preserving β and the measure, with multiplier Δ(g) = conj(det d), d the negative–negative block of g, and trivial cocycle for the Gaussian.")))))));
}

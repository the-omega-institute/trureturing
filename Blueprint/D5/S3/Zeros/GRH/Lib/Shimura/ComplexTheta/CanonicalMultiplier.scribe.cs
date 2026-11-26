using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.ComplexTheta;

internal sealed class CanonicalMultiplierDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical Multiplier", H("Canonical Multiplier"),
        Blocks(
            Paragraph(Text("Canonical semicharacter from an endomorphism b with b + b* = 1 for the Riemann form; normalised translations and their cocycle.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/ComplexTheta/CanonicalMultiplier.normalizedShift_normalizedShift"),
                H("normalizedShift_normalizedShift"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The Heisenberg law: if b + b* = 1 for the Riemann form E of Appell–Humbert data, the normalised translations Ũ (normalizedShift) satisfy Ũ_x Ũ_y f = exp(2πi E(bx, y))·Ũ_{x+y} f for every function f.")))))));
}

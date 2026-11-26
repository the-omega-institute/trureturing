using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.Places;

internal sealed class GaloisDefsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Galois Defs", H("Galois Defs"),
        Blocks(
            Paragraph(Text("Profinite Galois groups, local fields, places, decomposition, inertia, Frobenius, cyclotomic character.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/Places/GaloisDefs.mul_iff"),
                H("mul_iff"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If σ is a Frobenius at A for the exponent q, then στ is a Frobenius for qq' exactly when τ is a Frobenius for q'.")))))));
}

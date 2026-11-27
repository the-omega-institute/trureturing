using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.Places;

internal sealed class ConjugationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conjugation", H("Conjugation"),
        Blocks(
            Paragraph(Text("Complex conjugation on Galois group, places, Frobenius, inertia; anticyclotomic characters locally.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/Places/Conjugation.eq_one_of_mem_inertiaAbove"),
                H("eq_one_of_mem_inertiaAbove"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If χ satisfies IsFromU1 for S and I (anticyclotomic of modulus I), then χ is unramified off I ∪ Ī: χ(g) = 1 for g in any inertia group above a finite place of E outside I and its conjugate.")))))));
}

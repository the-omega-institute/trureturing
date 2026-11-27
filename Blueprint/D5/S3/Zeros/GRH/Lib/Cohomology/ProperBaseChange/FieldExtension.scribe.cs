using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Cohomology.ProperBaseChange;

internal sealed class FieldExtensionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Field Extension", H("Field Extension"),
        Blocks(
            Paragraph(Text("Cohomology invariant under algebraically closed field extension; classes detected at points.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Cohomology/ProperBaseChange/FieldExtension.isOpen_zero_set_and_eq_zero"),
                H("isOpen_zero_set_and_eq_zero"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let W be proper over R, ℓ invertible in R, T a test R-algebra, x ∈ H^n(W_T, ℤ/ℓ). The primes P of T with x zero on the fibre over κ(P) form an open set; if it is all of Spec T, then x = 0.")))))));
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.GaloisRep.Main;

internal sealed class AttachedDeterminantDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Attached Determinant", H("Attached Determinant"),
        Blocks(
            Paragraph(Text("Field cut out by χχ^c is CM of prime degree, with norm-detecting character. CM extension of prime degree with prescribed tame completion at a split place. Auxiliary quadratic CM extension containing imaginary quadratic field, split at given places. Local properties descend from the base-changed form's representation to the original one. Determinant of an attached Galois representation is the avatar of the twisted central character.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/GaloisRep/Main/AttachedDeterminant.exists_det_eq_avatar"),
                H("exists_det_eq_avatar"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For r attached to a rank n eigenform f, det r is the avatar of an algebraic Hecke character θ of explicit type; at split w, θ_w gives eigenvalues of unit scalars on f, and (−1)^n Q(0) at uniformisers, Q a Hecke polynomial of f.")))))));
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.HeckeCharacter;

internal sealed class CharOfDetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Char Of Det", H("Char Of Det"),
        Blocks(
            Paragraph(Text("Tame Hecke character on determinants of integral adelic points is product of residue characters.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/HeckeCharacter/CharOfDet.apply_det_eq_prod"),
                H("apply_det_eq_prod"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let μ have weight e and tame part ψ, trivial outside finitely many distinct places w_i. For k in the stabiliser K₀ of the standard lattice, μ(det k) = ∏_i ψ_{w_i}(det(k mod w_i)).")))))));
}

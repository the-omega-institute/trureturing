using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.GaloisRep.BaseChange;

internal sealed class BaseChangeWeightDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Base Change Weight", H("Base Change Weight"),
        Blocks(
            Paragraph(Text("Matching of spherical Hecke functions at places splitting completely in the extension. Twisted character of base-changed weight equals character at the norm.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/GaloisRep/BaseChange/BaseChangeWeight.exists_twisted_weightRep_trace"),
                H("exists_twisted_weightRep_trace"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For E'/E Galois of prime degree p, σ ≠ 1, compatible CM types and ρ the pulled-back weight representation, some s has sρ(δ) = ρ(σδ)s, and tr(ρ(δ)s) is the character of weight κ at γ whenever δσ(δ)⋯σ^{p−1}(δ) = γ.")))))));
}

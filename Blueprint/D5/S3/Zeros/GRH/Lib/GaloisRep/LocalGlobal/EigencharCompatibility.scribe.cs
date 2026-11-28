using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.GaloisRep.LocalGlobal;

internal sealed class EigencharCompatibilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Eigenchar Compatibility", H("Eigenchar Compatibility"),
        Blocks(
            Paragraph(Text("Local-global compatibility for sorted tame Iwahori eigencharacters at split places.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/GaloisRep/LocalGlobal/EigencharCompatibility.local_global_of_eigencharacter"),
                H("local_global_of_eigencharacter"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let r be attached to an eigenform f (Weil data) with Iwahori eigencharacter ∏ ξ_i(t_i)|t_i|^{N−i} at split w, |ξ_1(ϖ)| ≥ … ≥ |ξ_N(ϖ)|. Above w, r has finite type and the jumps of κ, and ∏(X − ιξ_i(x)) kills each s of degree k ≥ 0 with Artin preimage x of order k.")))))));
}

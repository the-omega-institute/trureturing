using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.Uniformisation;

internal sealed class ModuliPointDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Moduli Point", H("Moduli Point"),
        Blocks(
            Paragraph(Text("Finite adelic vectors modulo integral ones give the torsion module (E/O)^n. Complex points of the unitary Shimura datum, lattices, periods, polarised tori, isomorphisms.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/Uniformisation/ModuliPoint.IsLevelIso"),
                H("IsLevelIso"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("z is an isomorphism from (x, ℓ, P) to (x', ℓ', P') at level K: x'⁻¹zx ∈ K, zℓz⁻¹ = ℓ' at v₀, zP_i ≡ P'_i modulo Eⁿ ∩ x'Ôⁿ."))),
                DescribeRole.Definition))));
}

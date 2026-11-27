using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.CongruenceRelation;

internal sealed class KernelReductionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Kernel Reduction", H("Kernel Reduction"),
        Blocks(
            Paragraph(Text("Cartier's theorem; finite flat kernel is closure of its generic points. Arithmetic consequences of a good prime: characteristic, uniformiser, coprimality. Reduced isogeny kernels on one-dimensional torsion are cut by powers of one parameter.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/CongruenceRelation/KernelReduction.exists_param_pow_card_eq_zero"),
                H("exists_param_pow_card_eq_zero"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let x over k reduce a full y, w = ker(O_E → k) good, T = (E/O_E)ⁿ[w]. Some non-zero t in T reduces to 0. For some additive ν: T → A_x[w](k), each z in A_x[w](B), B local, π: B → k, has τ in ker π with τ^{#ν⁻¹(πz)} = 0 and, if πz = 0, z ≡ 0 mod τ.")))))));
}

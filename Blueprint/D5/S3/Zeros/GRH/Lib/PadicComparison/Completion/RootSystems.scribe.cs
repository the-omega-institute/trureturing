using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicComparison.Completion;

internal sealed class RootSystemsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Root Systems", H("Root Systems"),
        Blocks(
            Paragraph(Text("Derived completeness: Nakayama, retracts, cohomology, comparison mod a, completed base change. Tilting preserves products of two p-adic tests; product-preserving functors keep bijective pairs. Period pairs; period sheaf on p-adic tests is additive; p♭ kills coefficients modulo p. Functor of root systems with generator acting through roots of unity.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicComparison/Completion/RootSystems.pFlat_smul_eq_zero"),
                H("pFlat_smul_eq_zero"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If IsPeriodRingPair holds for (S, K), in particular p divides ξ in S, then π = ξ mod p annihilates O^♭ ⊗ S, the tensor product over A_inf.")))))));
}

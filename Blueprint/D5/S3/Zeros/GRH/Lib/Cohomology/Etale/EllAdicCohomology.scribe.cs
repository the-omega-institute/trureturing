using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Cohomology.Etale;

internal sealed class EllAdicCohomologyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ell Adic Cohomology", H("Ell Adic Cohomology"),
        Blocks(
            Paragraph(Text("Geometric l-adic cohomology with Galois action; reduction from Z_l to F_l coefficients.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Cohomology/Etale/EllAdicCohomology.bijective_ellAdicPull"),
                H("bijective_ellAdicPull"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If α: M → N induces bijections on all Ext groups with coefficients the locally constant 𝔽_ℓ-valued functions on test rings, then the pull-back ℚ_ℓ ⊗ Ext^n(N, ℤ_ℓ) → ℚ_ℓ ⊗ Ext^n(M, ℤ_ℓ) is bijective for every n.")))))));
}

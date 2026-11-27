using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Cohomology.SmoothBaseChange;

internal sealed class SmoothBaseChangeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Smooth Base Change", H("Smooth Base Change"),
        Blocks(
            Paragraph(Text("Duality comparison globalised; smooth schemes over valuation rings keep cohomology on the generic fibre.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Cohomology/SmoothBaseChange/SmoothBaseChange.isCohomEquiv_generic_fibre"),
                H("isCohomEquiv_generic_fibre"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let A be a valuation subring of Ω and an R-algebra, with a prime p in its maximal ideal and ℓ invertible. If the R-scheme Y satisfies IsCharted over R, then pull-back Hⁿ(Y_A, ℤ/ℓ) → Hⁿ(Y_Ω, ℤ/ℓ) is bijective for all n.")))))));
}

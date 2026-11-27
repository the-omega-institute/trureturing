using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Combinatorics;

internal sealed class AverageDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Average", H("Average"),
        Blocks(
            Paragraph(Text("Localisation identity for Schur polynomials; extracting Schur weights by algebraic independence of embeddings. Means, inner product, characters, irreducible characters, group-algebra elements of a finite group. Elementary rules for means of complex functions over finite sets and groups.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Combinatorics/Average.map_prod_rootCoeffEval_eq_zero"),
                H("map_prod_rootCoeffEval_eq_zero"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let the functions c(i, σ) be algebraically independent, |ι| ≥ total degree of q σ, and each multiset x j σ have a elements. A linear form killing the families j ↦ ∏_{i,σ} ∏_{t ∈ x j σ} (1 − c(i, σ)(α) t) for all α kills j ↦ ∏_σ rootCoeffEval(x j σ)(q σ).")))))));
}

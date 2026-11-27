using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.TraceFormula;

internal sealed class DefiniteTraceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Definite Trace", H("Definite Trace"),
        Blocks(
            Paragraph(Text("Trace of a Hecke operator on definite algebraic modular forms as orbital sum.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/TraceFormula/DefiniteTrace.trace_definiteForms"),
                H("trace_definiteForms"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Trace formula, definite side: for E⁺ ≠ ℚ, 𝔑 neat, W finite-dimensional, the forms are finite-dimensional and finitely many orbits of definite triples count; if a is regular and tr ξ(y⁻¹) = ∑_μ w(P, μ) for separable P, then tr a is their orbit sum.")))))));
}

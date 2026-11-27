using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.CuspForms;

internal sealed class DeltaFormsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Delta Forms", H("Delta Forms"),
        Blocks(
            Paragraph(Text("Smooth vector-valued forms for a group pair and their right translation. Operator norm of a Schur functor bounded by powers of singular values. Algebraic modular forms: delta forms, values at class representatives, dimension at neat level.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/CuspForms/DeltaForms.classSum_deltaForm"),
                H("classSum_deltaForm"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let e be injective and HasFiniteType hold. If additive maps L(g): W → ℂ satisfy L(e(γ)xk)(χ(k)ρ(γ)v) = L(x)(v) for all γ, k, the class sum of g ↦ L(g)(δ(g)) is L(x)(v), where δ is deltaForm at x, v.")))))));
}

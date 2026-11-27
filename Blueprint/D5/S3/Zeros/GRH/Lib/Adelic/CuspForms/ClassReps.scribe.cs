using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.CuspForms;

internal sealed class ClassRepsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Class Reps", H("Class Reps"),
        Blocks(
            Paragraph(Text("p-adic gauge on algebraic forms: invariance, ultrametric, integral module, weak approximation. Norm bounded by dual functionals; triangle inequality for finite sums. Class sets, p-integral representatives, integrality of forms supported on one class.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/CuspForms/ClassReps.weylNormSq_deltaForm_le"),
                H("weylNormSq_deltaForm_le"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a level K with a character χ whose values have finite order and σ ∈ Aut ℂ, the value at any g of the delta form δ_x(v) on U(I_n) satisfies ‖σ δ_x(v)(g)‖² ≤ |Aut(x)|²·‖σ v‖² in the Gram norm.")))))));
}

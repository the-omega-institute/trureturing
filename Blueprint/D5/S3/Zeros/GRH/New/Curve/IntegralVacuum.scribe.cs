using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Curve;

internal sealed class IntegralVacuumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integral Vacuum", H("Integral Vacuum"),
        Blocks(
            Paragraph(Text("Function mod m names an admissible sum of vacuum translates, with explicit denominator. Integrally scaled vacuum and the module of standard data at p. Scaled vacuum has integral values with bounded conjugates; some value is non-zero.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Curve/IntegralVacuum.norm_intVacuum_le_one"),
                H("norm_intVacuum_le_one"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a standard space V of rank |n|, a finite adelic vector x and any ι: ℂ → ℂ_p, the number ι(κ₀^{|n|}·vac(x)), x read in V_𝔸 by finVec, has absolute value at most 1.")))))));
}

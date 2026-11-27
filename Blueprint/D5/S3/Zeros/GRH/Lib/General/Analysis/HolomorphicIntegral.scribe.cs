using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Analysis;

internal sealed class HolomorphicIntegralDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Holomorphic Integral", H("Holomorphic Integral"),
        Blocks(
            Paragraph(Text("Holomorphic implies analytic in several variables; analyticity of parameter integrals. Cauchy estimate, holomorphy of parametric integrals, Mellin integrals on a strip.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Analysis/HolomorphicIntegral.mellin_analytic_on_strip"),
                H("mellin_analytic_on_strip"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let N > 0 be measurable, T·N^t integrable and the integral of |T|·N^s finite. Then ∫ T·N^z dμ converges absolutely and is continuous for real z in [s, t], and is real-analytic on (s, t).")))))));
}

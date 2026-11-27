using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.HeckeL;

internal sealed class IdelicThetaSumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Idelic Theta Sum", H("Idelic Theta Sum"),
        Blocks(
            Paragraph(Text("Adelic theta sum of a tent; Riemann-sum estimate replacing Poisson summation.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/HeckeL/IdelicThetaSum.exists_abs_sub_thetaSum_le"),
                H("exists_abs_sub_thetaSum_le"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For 0 < r < 1 the principal ideles are discrete and, with Θ_r(b) = ∑_γ adelicTent r d (γb) over them, some δ > 0, C satisfy: each l > 0 has an i with |i − Θ_{r/3}(b)| ≤ C l^δ |Θ_r(b)| for all ideles b of module l.")))))));
}

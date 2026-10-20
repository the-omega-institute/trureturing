using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Schatten;

internal sealed class ExpandingAverageDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Schatten/ExpandingAverage";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Balanced inverse-adjoint averages are expanding.",
        H("Balanced inverse-adjoint averages are expanding"),
        Blocks(
            Paragraph(Text("The balanced diagonal-matrix and inverse average in Bhatia–Kittaneh–Li (1997), §4, is a related method; here the inverse adjoint permits arbitrary invertible complex W.")),
            Describe.Lean(
                DescribeId.Create("zhangli-expandingaverage-inverseadjointaverage"),
                DeclarationHandle.Create(Module + ".inverseAdjointAverage"),
                H("A balanced average"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a complex square matrix W and real t, inverseAdjointAverage W t is Tₜ=(tW+t⁻¹(W⁻¹)*)/2. Expansion is asserted when W is invertible and t is positive."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("zhangli-expandingaverage-inverseadjointaverage-expanding"),
                DeclarationHandle.Create(Module + ".inverseAdjointAverage_expanding"),
                H("Expansion of the balanced average"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For invertible W and positive t, Tₜ*Tₜ−I is positive semidefinite. Indeed, with Sₜ=tW−t⁻¹(W⁻¹)*, the identity Tₜ*Tₜ−I=Sₜ*Sₜ/4 follows because both mixed products are identities. Hence every singular value of Tₜ is at least one."))),
                DescribeRole.Theorem))));
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMDLipNomeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipNome.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original lattice nome on the D lip",
        H("Signed continuation at the D boundary"),
        Blocks(
            Describe.Lean(DescribeId.Create("original-fourm-d-tau"),
                DeclarationHandle.Create(Prefix + "dTau"),
                H("The continued period ratio"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let τ be the original slit-period ratio. For a Boolean upperA and complex t, "
                    + "set dTau(upperA,t) = −(τ(1−1/t) + s)⁻¹. When upperA is true, s = 1 and the selected D lip "
                    + "has Im t < 0. When upperA is false, s = −1 and the selected D lip has Im t > 0."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("original-fourm-d-nome"),
                DeclarationHandle.Create(Prefix + "dNome"),
                H("The continued lattice nome"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For either Boolean upperA and every complex t, "
                    + "dNome(upperA,t) = exp(iπ dTau(upperA,t))."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("original-fourm-d-tau-agreement"),
                DeclarationHandle.Create(Prefix + "dTau_eq_tau"),
                H("Ratio agreement on the open lip"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For either Boolean upperA and every complex t on the selected open D lip, "
                    + "dTau(upperA,t) = τ(t)."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-fourm-d-nome-agreement"),
                DeclarationHandle.Create(Prefix + "dNome_eq_exp"),
                H("Nome agreement on the open lip"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For either Boolean upperA and every complex t on the selected open D lip, "
                    + "dNome(upperA,t) equals the original lattice nome exp(iπ τ(t))."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-fourm-d-nome-analytic"),
                DeclarationHandle.Create(Prefix + "dNome_analyticAt"),
                H("Analyticity at the D boundary"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For either Boolean upperA and every real t > 1, the function "
                    + "u ↦ dNome(upperA,u) is complex analytic at t viewed in ℂ."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-fourm-d-nome-boundary-norm"),
                DeclarationHandle.Create(Prefix + "dNome_norm_lt_one"),
                H("Strict norm bound at the D boundary"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For either Boolean upperA and every real t > 1, "
                    + "‖dNome(upperA,t)‖ < 1 at the complex boundary point t."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-fourm-d-nome-neighborhood-norm"),
                DeclarationHandle.Create(Prefix + "dNome_subunit_near"),
                H("Strict norm bound in a complex neighborhood"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For either Boolean upperA and every real t > 1, "
                    + "‖dNome(upperA,u)‖ < 1 for all u in some complex neighborhood of t."))),
                DescribeRole.Theorem))));
}

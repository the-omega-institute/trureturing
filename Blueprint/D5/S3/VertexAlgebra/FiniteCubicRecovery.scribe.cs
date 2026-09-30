using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class FiniteCubicRecoveryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/FiniteCubicRecovery.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite cubic data recover the normalized product and its stabilizer.",
        H("Finite Cubic Recovery"),
        Blocks(
            Paragraph(Text("This document formalizes the finite algebra step behind the cubic "
                + "response interface. It uses Fin n coordinates for the unit complement and "
                + "does not construct a VOA, a Monster action, or the Griess tensor.")),
            Describe.Lean(
                DescribeId.Create("finite-cubic-full-multiplication-recovery"),
                DeclarationHandle.Create(Prefix + "mul_eq_recoveredMul"),
                H("Full multiplication recovery"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For x = ae + u and y = be + v, the product is recovered "
                    + "from the invariant form and the cubic sharp tensor as "
                    + "(ab + <u,v>/3)e + av + bu + T sharp(u,v). The normalization is "
                    + "the one used in the local completion discussion in M01."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-cubic-stabilizer-criterion"),
                DeclarationHandle.Create(Prefix + "extend_preserves_mul_iff"),
                H("Cubic stabilizer criterion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An orthogonal map on the unit complement, extended by "
                    + "fixing the unit, preserves the recovered product exactly when it "
                    + "preserves the cubic sharp tensor. The actual Monster identification "
                    + "is an external Griess-algebra input."))),
                DescribeRole.Theorem))));
}

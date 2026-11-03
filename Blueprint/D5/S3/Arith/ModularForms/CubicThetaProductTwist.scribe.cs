using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ModularForms;

internal sealed class CubicThetaProductTwistDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/ModularForms/CubicThetaProductTwist.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Fourier/huang2025signpatterns");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three genuine root-twisted Jacobi products are factored at finite cutoff, then passed to the coefficientwise limit.", H("CubicThetaProductTwist"), Blocks(
            Paragraph(Text("Three genuine root-twisted Jacobi products are factored at finite cutoff, then passed to the coefficientwise limit.")),
            Node("0", "finiteFactor", "The single finite product of shifted factors 1-C(z)X^(j+shift), for j below the cutoff.", DescribeRole.Definition),
            Node("1", "finiteEuler", "The finite product of actual Euler factors from one through the cutoff.", DescribeRole.Definition),
            Node("2", "finiteJacobi", "The finite Jacobi product with its degree-zero factor retained.", DescribeRole.Definition),
            Node("3", "jacobiEvaluation", "The genuine Jacobi series evaluated at a Laurent unit.", DescribeRole.Definition),
            Node("4", "finite_jacobi_eq", "The finite product agrees with evaluation of the existing genuine Jacobi construction.", DescribeRole.Theorem),
            Node("5", "three_finite_factors", "Finite factorization includes the zero-degree factor and both infinite-product directions.", DescribeRole.Theorem),
            Node("6", "finite_three_jacobi", "The product of the three finite root twists factors into the cube-variable Jacobi product and Euler factors.", DescribeRole.Theorem),
            Node("7", "tendsto_finite_jacobi_evaluation", "Finite Jacobi evaluations converge coefficientwise to evaluation of the actual Jacobi series.", DescribeRole.Theorem),
            Node("8", "three_jacobi_product", "The root-twisted product identity is obtained from finite factorizations without dividing.", DescribeRole.Theorem),
            Paragraph(Text("Statements and proof dependencies come from the exact scoped Lean report. Classical theta mathematics is attributed to Borwein and Cooper as quoted in Huang et al. arXiv:2507.16644v1. The repository InversionSeq207 triple-product supplier is reused. No literature priority, worldwide absence, journal-typeset inspection, CI or original-problem acceptance is certified by this document."))
        ), []));
    private static DocumentBlock Node(string id, string declaration, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("cubicthetaproducttwist-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(declaration), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(text))), role);
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.FourthTransfer;

internal sealed class MacroscopicEndpointGeometryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/MacroscopicEndpointGeometry.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Shared endpoint geometry for macroscopic freezing",
        H("Macroscopic endpoint geometry"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("macro-endpoint-geometry"),
                DeclarationHandle.Create(Prefix + "macro_endpoint_geometry"),
                H("Derivative and image bounds for moving endpoints"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let a be a nonnegative C1 function on [1,2], bounded by M with absolute derivative at most L. For X>0 and X<=l<=r<=2X, choose c in [0,M]. Assume M*X^theta<=X and L*X^theta/X<=1/2. On [l,r] the frozen endpoint p(x)=x+X^theta*c has derivative one, while the moving endpoint q(x)=x+X^theta*a(x/X) has derivative 1+X^theta*a'(x/X)/X, at least one half. Both endpoints are continuous and take values in [l,r+M*X^theta]. The derivatives are taken within the closed interval, so only regularity of a on [1,2] is needed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("macro-cell-gap-le"),
                DeclarationHandle.Create(Prefix + "macro_cell_gap_le"),
                H("The endpoint gap on one equal cell"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let a be a nonnegative C1 function on [1,2], bounded by M with absolute derivative at most L>=0. For X>0, n>0 and j<n, write u_j=1+j/n. Every x in [u_j*X,u_(j+1)*X] satisfies |X^theta*(a(x/X)-a(u_j))|<=X^theta*L/n. The mean value inequality applies within [1,2], and the macroscopic cell width is exactly 1/n."))),
                DescribeRole.Theorem))));
}

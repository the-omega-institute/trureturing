using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class PrincipalTermDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrincipalTerm.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The triangular principal coefficient gives the complete Mangoldt logarithmic derivative.",
        H("The signed principal Mellin kernel"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("principal-signed-tendsto"),
                DeclarationHandle.Create(Prefix + "principal_signed_tendsto"),
                H("The complete signed principal limit"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For Re(s)>1/2, take the sum of Lambda(n)*n^(-s-1/2)/2 "
                    + "over 0<=n<=floor(b), and subtract the integral of t^(-s-1/2)/2 "
                    + "from 1 to b. Its limit as b tends to infinity is "
                    + "-zeta'(s+1/2)/(2*zeta(s+1/2))-1/(2*(s-1/2)). "
                    + "Mathlib supplies absolute summability of the full von Mangoldt "
                    + "Dirichlet series and its equality with the negative logarithmic "
                    + "derivative. The ordinary complex-power integral supplies the "
                    + "subtracted density. All prime powers retain their full weights."))),
                DescribeRole.Theorem))));
}

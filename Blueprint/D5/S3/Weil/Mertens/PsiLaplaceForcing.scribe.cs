using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens;

internal sealed class PsiLaplaceForcingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact signed psi-tail substitution",
        H("PsiLaplaceForcing"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fpsi-eq-tail"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/PsiLaplaceForcing.fpsi_eq_tail"),
                H("Exact signed psi-tail substitution"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original fpsi(u)=-Jpsi(exp u) equals the negative integral of qpsi(v)*(v+1)/v^2 over v>u, by the exponential substitution with its Jacobian."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("boundary-analytic"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/PsiLaplaceForcing.boundary_analytic"),
                H("Entire positive cutoff boundary"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("boundary(U,s)=U^2*fpsi(U)*exp(-sU) is entire in s. It is consumed in the forcing pole proof."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-forcing-poles"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/PsiLaplaceForcing.actual_forcing_poles"),
                H("Full meromorphic Euler coefficient"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Phi(U,s)=-Mpsi prime(U,s)+Mpsi(U,s)+boundary(U,s). Every actual nontrivial strip zero gives the full complex double pole of order -2 and normalized coefficient -m/rho. Adding the entire positive boundary preserves this coefficient. The source simple pole and both full punctured limits are included. No radial replacement or negative-half-plane integral convergence assumption is used."))), DescribeRole.Theorem))));
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.CriticalPoints;

internal sealed class SchurStripFunctionsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Zeros/CriticalPoints/SchurStripFunctions.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Entire matrix interpolation functions with the left boundary estimate and a unitary right multiplier.",
        H("The Schur interpolation functions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("schur-strip-trace-function"),
                DeclarationHandle.Create(Prefix + "f"),
                H("The scalar trace family"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Given n, a complex matrix Q, complex families u,v, real families t,rho and real p, define F(z)=H(n,pz/2) diag(u_j positivePower(t_j,pz)) H(n,pz/2), K(z)=Q diag(conj(v_k) positivePower(rho_k,p(1−z))) Q*, and f(z)=Tr(K(z)F(z)). Each entry is built from explicit scalar exponentials and finite matrix products."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("schur-strip-trace-analytic"),
                DeclarationHandle.Create(Prefix + "f_strip"),
                H("Analyticity and boundedness on the closed strip"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For all supplied finite data, the scalar trace family f has StripData: it is entire and bounded on the closed strip. No positivity, phase normalization, unitary basis or triangularity assumption is needed for this analytic statement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("schur-strip-left-bound"),
                DeclarationHandle.Create(Prefix + "left_bound"),
                H("The normalized left boundary"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For n>0, unitary Q, unit phases u and v, positive rho and sum_k rho_k^p=1, the norm of f(iy) is at most one for every real y. The left F matrix is unitary; in the Q basis the absolute diagonal weights sum to one. On the right boundary, K is unitary whenever Q and v have these unitary and phase properties."))),
                DescribeRole.Theorem))));
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Reduction;

internal sealed class SingularPositiveRefinementDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Singular canonical filters reduce exactly to their support corners and obey scalar rigidity.",
        H("SingularPositiveRefinement"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("filter-support-reduction"),
                DeclarationHandle.Create("D5/S3/Quantum/Reduction/SingularPositiveRefinement.filter_support_reduction"),
                H("Exact reduction through a singular support"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let E be any PSD complex matrix on a finite decidable coordinate type n, and let Phi be a complex linear endomorphism positive on PSD inputs with Phi(X) at most sqrt(E) X sqrt(E) for every PSD X. Put R=sqrt(E), W equal to the spectral inverse square root, and P equal to the spectral support. Then Phi(P X P)=Phi(X) for all complex X; P Phi(X)=Phi(X)=Phi(X) P for all X; W Phi(X) W is PSD and at most P X P for PSD X; and R (W Phi(X) W) R=Phi(X) for all X. Singular and zero E remain in scope. The spectral square-root products and support domination are reused from the existing support perspective modules."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("filter-dominated-scalar"),
                DeclarationHandle.Create("D5/S3/Quantum/Reduction/SingularPositiveRefinement.filter_dominated_scalar"),
                H("Positivity-only scalar rigidity for singular filters"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("With exactly the same finite coordinate type, PSD E, complex linear Phi, positivity and domination assumptions, there is a real c between zero and one such that Phi(X)=c sqrt(E) X sqrt(E) for every complex matrix X. No invertibility is assumed. The supported inverse-square-root conjugation is dominated by projection compression; corner scalar rigidity and exact reconstruction give the formula, including a zero effect."))),
                DescribeRole.Theorem))));
}

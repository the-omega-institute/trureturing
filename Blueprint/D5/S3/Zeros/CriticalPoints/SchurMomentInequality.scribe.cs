using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.CriticalPoints;

internal sealed class SchurMomentInequalityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Zeros/CriticalPoints/SchurMomentInequality.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The real-order characteristic-root moment bound and its strict-order rigidity.",
        H("The sharp spectral moment inequality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("schur-spectral-bound-rigidity"),
                DeclarationHandle.Create(Prefix + "spectral_bound_and_rigidity"),
                H("The bound and necessary equality condition"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For n>0, nonzero complex b_j and every real p≥1, the sum of norm(mu)^p over characteristic roots of diag(b)(I+J), with multiplicity, is at most ((n+1)^p+n−1)/n times sum_j norm(b_j)^p. For p>1, equality implies b_i=b_j for every i,j. The endpoint uses the unitary rank-one trace bound; strict orders use one fixed Schur basis, scalar three-lines interpolation and propagation of equality to all right boundary phases."))),
                DescribeRole.Theorem))));
}

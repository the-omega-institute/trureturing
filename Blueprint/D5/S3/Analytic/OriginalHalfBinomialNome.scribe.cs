using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class OriginalHalfBinomialNomeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The same original period has a normalized holomorphic correction, continuation and nome.",
        H("The normalized disk nome and its Taylor coefficients"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-nome-disk"),
                DeclarationHandle.Create("D5/S3/Analytic/OriginalHalfBinomialNome.actual_nome_disk"),
                H("The normalized disk nome and its Taylor coefficients"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                Paragraph(Text("Define Q0=(r/16)exp(i pi H). It is holomorphic on all of D, with Q0'=exp(i pi H)/(16(1-r)P squared). The exponential and the proved denominator factors are nonzero on D, so Q0' never vanishes there. The sole zero of Q0 is zero.")),
                Paragraph(Text("At zero Q0'=1/16 and Q0''=1/16. Thus the degree-one Taylor coefficient is 1/16, and the degree-two Taylor coefficient Q0''(0)/2! is 1/32. These are coefficients of the holomorphic function at zero. A nonzero derivative gives a local analytic coordinate; it does not prove global injectivity or a global half-plane or unit-disk range."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-nome-source"),
                DeclarationHandle.Create("D5/S3/Analytic/OriginalHalfBinomialNome.actual_nome_source"),
                H("The same literal period and source nome"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                Paragraph(Text("At every complex point of the full lens, Q0=exp(i pi tau) for the literal tau=iP(1-r)/P(r). Substituting t0=tau and exponentiating its normalized logarithm gives the factor r/16 exactly.")),
                Paragraph(Text("For every real 0<r<1, the existing original_source_nome and reality of the original periods identify Q0(r)=r exp(2 sourceConstant(sqrt r))/16. The entire expression is extended to D by Q0; no complex extension of sourceConstant is assumed. The full Monster, vertex-algebra, conformal-field, anomaly, fusion, string and AdS/CFT objectives require additional results. No monodromy, global uniformization, operator transport or physical completion follows from these local identities."))), DescribeRole.Theorem))));
}

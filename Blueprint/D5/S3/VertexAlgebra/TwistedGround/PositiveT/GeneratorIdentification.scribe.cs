using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.PositiveT;

internal sealed class GeneratorIdentificationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original Positive Gaussian T Generator",
        H("Original Positive Gaussian T Generator"),
        Blocks(
            Paragraph(Text("Let r be real with 0<r<1, and let u,v be complex with norm(u)+sqrt(r)<1 and norm(v)+sqrt(r)<1. The literal positive square-resolvent generator equals the analytic candidate, including both axes and the diagonal. The finite mode definitions and the original source amplitudes are unchanged.")),
            Paragraph(Text("The actual finite denominator coefficients obey norm(h(p,q,r)) <= (1+sqrt(r))^(p+q) and norm(h2(p,q,r)) <= (p+1)*(q+1)*(1+sqrt(r))^(p+q). Polynomial geometric majorants give absolute convergence before any rearrangement. Guarded successor reindexings turn the finite identities E*h=delta00 and E*h2=h into the sums 1/E and 1/E squared; the first identity also proves E is nonzero. A rectangular Cauchy product evaluates the actual finite source convolutions.")),
            Paragraph(Text("The summed expression retains both r*(1+(1-r)*u*v)/(2*E) and r squared*u*v/E squared, as well as the logarithmic derivative correction r*(1-r)*periodPrime/period. The full unit-disk mode identity externalT_positive_finite_eq identifies every original positive mode at z=sqrt(r) with its finite coefficient. The equality then follows by equality of the actual sums. No extra summability, germ-equality or differentiability hypothesis is imposed. Signed J/T sectors and the full string-theory goal remain outside this result.")),
            Describe.Lean(DescribeId.Create("positive-t-has-sum"), DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/PositiveT/GeneratorIdentification.positiveT_hasSum"), H("positiveT_hasSum"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For every real 0<r<1 and every complex u,v in the stated source bidisk, the family t(p,q,r)*u^p*v^q, indexed by all natural pairs, has sum OriginalGaussianExternalAnalyticCandidate.candidateT(u,v,r). Absolute convergence is derived from the actual finite h and h2 bounds and the original source generators."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("positive-t-eq-candidate-t"), DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/PositiveT/GeneratorIdentification.positiveT_eq_candidateT"), H("positiveT_eq_candidateT"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For every real 0<r<1 and complex u,v satisfying norm(u)+sqrt(r)<1 and norm(v)+sqrt(r)<1, OriginalGaussianExternalGeneratedSource.kernelMode(true,true,true,u,v,sqrt(r)) equals OriginalGaussianExternalAnalyticCandidate.candidateT(u,v,r). The proof consumes positiveT_hasSum and the unconditional full unit-disk identity for the original positive modes. Zero coordinates and equal coordinates are included."))), DescribeRole.Theorem)
        )));
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class GainRayWorldDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Whole polynomial worlds and positive source coordinates", H("Whole polynomial worlds and positive source coordinates"), Blocks(
            Paragraph(Text("For any declared natural maximum degree d, Coeff d is the real vector space indexed by Fin(d+1). The polynomial gain d beta is Polynomial.ofFn(d+1,beta), with ascending ordinary coefficients. World d contains a strictly entrywise positive real 2 by 2 source of matrix rank one and trace one, a nonzero coefficient vector, and an arbitrary real drift. No individual coefficient, sampled value, root multiplicity, sign, or actual degree is constrained. Statements about the adaptive threshold additionally require d>=1.")),
            Paragraph(Text("PolynomialWorld d instead stores the same source and drift together with a nonzero real polynomial whose natural degree is at most d. coefficientEquiv reconstructs every such bounded polynomial from its ordinary coefficients. worldEquiv is an equivalence with both inverse laws, preserving the source and drift. Its nonzero condition concerns the whole polynomial.")),
            Paragraph(Text("The sourceChart(x,r) is the matrix [1,r;x,xr] divided by 1+xr. For x,r>0 it is strictly positive, rank one, and trace one. Every legal original source is exactly one such matrix, with recovered coordinates x=P10/P00 and r=P01/P00. The denominator is strictly positive. No auxiliary source restriction is introduced.")),
            Describe.Lean(DescribeId.Create("gain-ray-gainrayworld-coefficientEquiv"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GainRayWorld.coefficientEquiv"),
                H("Ordinary coefficient equivalence"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural d, coefficientEquiv d is an equivalence from Coeff d to the subtype of real polynomials p with p.natDegree<=d. Its forward map is gain d and its inverse takes the first d+1 coefficients."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gain-ray-gainrayworld-worldEquiv"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GainRayWorld.worldEquiv"),
                H("Exact whole-world equivalence"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural d, worldEquiv d is an equivalence from World d to PolynomialWorld d. It preserves source and drift and sends the coefficient vector to its whole polynomial. Both nonzero predicates and both inverse identities are proved."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gain-ray-gainrayworld-source-chart-legal"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GainRayWorld.source_chart_legal"),
                H("Legality of every positive chart point"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every x,r in the reals, 0<x and 0<r imply LegalSource(sourceChart x r). This means every entry is positive, its matrix rank is one, and its trace is one."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gain-ray-gainrayworld-source-chart-exact"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GainRayWorld.source_chart_exact"),
                H("Every original source is represented"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real 2 by 2 matrix P satisfying LegalSource P there exist positive real x,r with P=sourceChart x r, x=P10/P00, and r=P01/P00. The rank-one hypothesis gives determinant zero; trace one reconstructs the positive denominator."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gain-ray-gainrayworld-normalization-read"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GainRayWorld.normalization_read"),
                H("Trace normalization preserves scalar observations"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real 2 by 2 R,A, every real G and drift delta, and trace(R) nonzero, (trace(R) G) trace(A (trace(R) inverse times R))+delta equals G trace(A R)+delta. Positive rank-one unnormalized worlds use the positive trace as this scale."))), DescribeRole.Theorem))));
}

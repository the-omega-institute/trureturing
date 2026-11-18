using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalGaussianAllIndexResolventDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All-index Original Gaussian Resolvents",
        H("All-index Original Gaussian Resolvents"),
        Blocks(
            Paragraph(Text("The central series A_s and its shifted derivative E_s have summable polynomial-geometric bounds. They are differentiated as genuine series, and the period is A_0. The explicit jet Q_s retains the period denominator, which is nonzero on the complex unit disk.")),
            Paragraph(Text("The actual source column extends from the real radial interval to the full complex disk by holomorphic uniqueness. The original scaled radial column derivative gives the differentiated column; the finite displacement limit then determines every odd resolvent entry. The branch-free central-binomial expression includes both diagonal and off-diagonal positive frequencies.")),
            Paragraph(Text("The square resolvent is reconstructed from T = I + KJ. Its diagonal retains the identity term and a norm-absolutely convergent scalar convolution with the explicit odd entry. No unknown resolvent entry occurs in this formula.")),
            Paragraph(Text("These are classical Gaussian displacement and analytic continuation arguments on the repository carrier, consumed by the actual external source blocks. No literature novelty, boundary value at norm one, original cross-channel identityK or C1, or physical realization is claimed.")),
            Describe.Lean(
                DescribeId.Create("shifted-central-series"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianAllIndexResolvent.shiftedCentralSeries"),
                H("shiftedCentralSeries"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The shiftedCentralSeries definition fixes the literal objects and conventions used in the proof."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("shifted-central-derivative"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianAllIndexResolvent.shiftedCentralDerivative"),
                H("shiftedCentralDerivative"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The shiftedCentralDerivative definition fixes the literal objects and conventions used in the proof."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("central-column-jet"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianAllIndexResolvent.centralColumnJet"),
                H("centralColumnJet"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The centralColumnJet definition fixes the literal objects and conventions used in the proof."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("explicit-odd-entry"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianAllIndexResolvent.explicitOddEntry"),
                H("explicitOddEntry"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The explicitOddEntry definition fixes the literal objects and conventions used in the proof."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("square-resolvent"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianAllIndexResolvent.squareResolvent"),
                H("squareResolvent"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The squareResolvent definition fixes the literal objects and conventions used in the proof."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("odd-resolvent"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianAllIndexResolvent.oddResolvent"),
                H("oddResolvent"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The oddResolvent definition fixes the literal objects and conventions used in the proof."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("column-series-entry-explicit-complex"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianAllIndexResolvent.columnSeries_entry_explicit_complex"),
                H("columnSeries_entry_explicit_complex"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The columnSeries_entry_explicit_complex statement is verified on its displayed full domain and consumed by the original Gaussian source calculation."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("square-eq-one-add"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianAllIndexResolvent.square_eq_one_add"),
                H("square_eq_one_add"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The square_eq_one_add statement is verified on its displayed full domain and consumed by the original Gaussian source calculation."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("odd-resolvent-entry-explicit"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianAllIndexResolvent.oddResolvent_entry_explicit"),
                H("oddResolvent_entry_explicit"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The oddResolvent_entry_explicit statement is verified on its displayed full domain and consumed by the original Gaussian source calculation."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("square-resolvent-entry-explicit"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianAllIndexResolvent.squareResolvent_entry_explicit"),
                H("squareResolvent_entry_explicit"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The squareResolvent_entry_explicit statement is verified on its displayed full domain and consumed by the original Gaussian source calculation."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("period-ofreal"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianAllIndexResolvent.period_ofReal"),
                H("period_ofReal"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real r, the literal complex period at r is the complex embedding of the existing real period F r."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("central-hasderivat"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianAllIndexResolvent.central_hasDerivAt"),
                H("central_hasDerivAt"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural shift and complex x with norm less than one, shiftedCentralSeries has complex derivative shiftedCentralDerivative."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("period-eq-central"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianAllIndexResolvent.period_eq_central"),
                H("period_eq_central"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every complex x, the original period tsum is exactly shiftedCentralSeries at shift zero."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("radial-positive-column"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianAllIndexResolvent.radial_positive_column"),
                H("radial_positive_column"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real 0<r<1 and each natural n, the actual resolvent applied to weightedSource has coordinate sqrt(1-r)(-1)^(n+1) sqrt(r)^(n+1) centralColumnJet(r,n+1)/sqrt(n+1)."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("radial-negative-column"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianAllIndexResolvent.radial_negative_column"),
                H("radial_negative_column"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real 0<r<1 and each natural n, the actual oppositeResolvent applied to weightedSource has coordinate sqrt(1-r)(-1)^(n+1) sqrt(r)^(n+1) sqrt(n+1) shiftedCentralSeries(r,n+1)."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("signed-square-factorization"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianAllIndexResolvent.signed_square_factorization"),
                H("signed_square_factorization"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On the complex unit disk, the actual resolvent equals (1+operator) times squareResolvent, and oppositeResolvent equals (1-operator) times squareResolvent."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("odd-eq-half-difference"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianAllIndexResolvent.odd_eq_half_difference"),
                H("odd_eq_half_difference"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On the complex unit disk, the actual oddResolvent is half the difference of resolvent and oppositeResolvent."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("opposite-differentiable"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianAllIndexResolvent.opposite_differentiable"),
                H("opposite_differentiable"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual oppositeResolvent is complex differentiable at every point of the unit disk."))), DescribeRole.Theorem))));
}

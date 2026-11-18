using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalGaussianExternalResolventDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original Binomial External Resolvent Contractions",
        H("Original Binomial External Resolvent Contractions"),
        Blocks(
            Paragraph(Text("Every fixed original input and output mode has a polynomial-geometric l1 majorant. The estimate follows from the generalized binomial recurrence, a natural binomial bound and geometric summability; l2 membership alone is not used to justify double sums.")),
            Paragraph(Text("The external odd contraction is the absolutely convergent double series in the explicit all-index odd kernel. The square contraction contains the direct identity pairing and an absolutely convergent triple series in the literal Cauchy kernel and explicit odd kernel. Basis expansions on the actual carrier prove that these are the bounded bilinear contractions.")),
            Paragraph(Text("The literal mixed corrected source row has exactly the stated binomial column and frequency-root factor. Uniform norm convergence of its finite cutoffs supplies the external-block limit. All pairings use ordinary complex bilinear transpose.")),
            Describe.Lean(
                DescribeId.Create("external-binomial"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalResolvent.externalBinomial"),
                H("externalBinomial"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The externalBinomial definition fixes the literal objects and conventions used in the proof."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("external-column"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalResolvent.externalColumn"),
                H("externalColumn"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The externalColumn definition fixes the literal objects and conventions used in the proof."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("external-j"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalResolvent.externalJ"),
                H("externalJ"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The externalJ definition fixes the literal objects and conventions used in the proof."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("external-t"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalResolvent.externalT"),
                H("externalT"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The externalT definition fixes the literal objects and conventions used in the proof."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("external-column-l1"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalResolvent.externalColumn_l1"),
                H("externalColumn_l1"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The externalColumn_l1 statement is verified on its displayed full domain and consumed by the original Gaussian source calculation."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("external-vector-apply"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalResolvent.externalVector_apply"),
                H("externalVector_apply"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The externalVector_apply statement is verified on its displayed full domain and consumed by the original Gaussian source calculation."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("external-contractions-explicit"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalResolvent.external_contractions_explicit"),
                H("external_contractions_explicit"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The external_contractions_explicit statement is verified on its displayed full domain and consumed by the original Gaussian source calculation."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("external-cutoff-control"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalResolvent.externalCutoff_control"),
                H("externalCutoff_control"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The externalCutoff_control statement is verified on its displayed full domain and consumed by the original Gaussian source calculation."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-left-mixed"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalResolvent.actual_left_mixed"),
                H("actual_left_mixed"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual_left_mixed statement is verified on its displayed full domain and consumed by the original Gaussian source calculation."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("choose-bound"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalResolvent.choose_bound"),
                H("choose_bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural p and complex a with norm(a)<=p+1, and every natural s, norm(choose(a,s)) is at most Nat.choose(p+s,s)."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("externalcolumn-bound"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalResolvent.externalColumn_bound"),
                H("externalColumn_bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For either sign, natural p and nonnegative rho, every complex z with norm(z)<=rho and every natural n, norm of the original externalColumn is bounded by (p+1)^p (n+1)^(p+1) rho^(n+1)."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("external-double-summable"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalResolvent.external_double_summable"),
                H("external_double_summable"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For all signed input and output modes, every complex z in the unit disk and every bounded operator on the actual carrier, the coordinate double contraction with the two original external columns is norm summable."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("external-bilinear-expansion"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalResolvent.external_bilinear_expansion"),
                H("external_bilinear_expansion"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For all signed external modes, complex z in the unit disk and every bounded carrier operator, the ordinary bilinear contraction of the two actual vectors equals its coordinate double series."))), DescribeRole.Theorem))));
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalGaussianExternalCandidateCoreDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rational Core of the Signed Gaussian Candidate",
        H("Rational Core of the Signed Gaussian Candidate"),
        Blocks(
            Paragraph(Text("These are algebraic identities for the rational part of the candidate kernel. Its analytic square-root factors and its identification with the complete original J/T mode generators remain to be established.")),
            Describe.Lean(
                DescribeId.Create("npoly"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.nPoly"),
                H("nPoly"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For complex x,t,s, the numerator is t*s*(t+s) - 2*(2-x)*t*s + (1-x)*(t+s)."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("qpoly"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.qPoly"),
                H("qPoly"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The rational core divides nPoly by 2*(t-s)^2. This uses total complex division; identities interpreting the quotient away from the diagonal carry explicit nonzero assumptions."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("npoly-comm"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.nPoly_comm"),
                H("nPoly_comm"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every complex x,t,s, exchanging t and s preserves the numerator."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("npoly-diagonal"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.nPoly_diagonal"),
                H("nPoly_diagonal"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every complex x,t, the diagonal numerator is 2*t*(t-1)*(t-(1-x))."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("npoly-sub-diagonal-factor"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.nPoly_sub_diagonal_factor"),
                H("nPoly_sub_diagonal_factor"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every complex x,t,s, subtracting nPoly x s s from nPoly x t s gives (t-s)*(s*t+2*s^2-2*(2-x)*s+(1-x)), without dividing by t-s."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("npoly-first-diagonal"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.nPoly_first_diagonal"),
                H("nPoly_first_diagonal"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every complex x,s, the diagonal value of the preceding factor normalizes to 3*s^2-2*(2-x)*s+(1-x)."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("npoly-source-curve"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.nPoly_source_curve"),
                H("nPoly_source_curve"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every complex x,t,s, the same numerator has the source-curve form t*s*(t+s)-2*(1+(1-x))*t*s+(1-x)*(t+s)."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("right-chart"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.rightChart"),
                H("rightChart"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The right chart sends u to 1/u for true and to u for false."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("left-chart"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.leftChart"),
                H("leftChart"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The left chart sends u to (1-(1-x)*u)/(1-u) for true and to ((1-x)-u)/(1-u) for false."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("complementary-kernel-reflection"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.complementary_kernel_reflection"),
                H("complementary_kernel_reflection"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For complex x,t,s with t distinct from s, qPoly x t s plus qPoly (1-x) (1-t) (1-s) equals one half."))), DescribeRole.Theorem),
            Paragraph(Text("Each chart-reflection theorem below assumes x is nonzero, 1-u and 1-v are nonzero, and both the right-chart pair and the left-chart pair are distinct. It also assumes u is nonzero when its sign is true and v is nonzero when its sign is true.")),
            Describe.Lean(
                DescribeId.Create("reflected-positive-positive"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.reflected_positive_positive"),
                H("reflected_positive_positive"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the stated chart-domain assumptions with both signs true, evaluating qPoly on the two left charts equals evaluating it on the two right charts."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reflected-negative-negative"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.reflected_negative_negative"),
                H("reflected_negative_negative"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the stated chart-domain assumptions with both signs false, evaluating qPoly on the two left charts equals evaluating it on the two right charts."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reflected-positive-negative"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.reflected_positive_negative"),
                H("reflected_positive_negative"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the stated chart-domain assumptions with signs true and false, evaluating qPoly on the two left charts equals evaluating it on the two right charts."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reflected-negative-positive"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore.reflected_negative_positive"),
                H("reflected_negative_positive"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the stated chart-domain assumptions with signs false and true, evaluating qPoly on the two left charts equals evaluating it on the two right charts."))), DescribeRole.Theorem))));
}

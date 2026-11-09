using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class VarianceTransferDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Increments, profile averages, and parameterized short-interval variance hypotheses.",
        H("Variance transfer definitions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unit-measure"),
                DeclarationHandle.Create(Prefix + "unitMeasure"),
                H("Unit interval measure"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Lebesgue measure restricted to the interval (0,1]."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("profile-integrable"),
                DeclarationHandle.Create(Prefix + "ProfileIntegrable"),
                H("Integrable profiles"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A profile is a measurable real function whose absolute value is integrable for unit interval measure. Choose a global Borel representative; its values outside [0,1] do not affect the conclusions."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("valid-band"),
                DeclarationHandle.Create(Prefix + "ValidBand"),
                H("Admissible exponents"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The exponents satisfy 0<alpha<theta<beta<1."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("profile-primitive"),
                DeclarationHandle.Create(Prefix + "profilePrimitive"),
                H("Profile primitives"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The primitive at length h and center x is the oriented integral from 0 to h of g(u/h)*D_u(x)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("profile-average"),
                DeclarationHandle.Create(Prefix + "profileAverage"),
                H("Profile averages"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The profile average is the profile primitive divided by h^2."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("moving-average"),
                DeclarationHandle.Create(Prefix + "movingAverage"),
                H("Moving profile averages"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The moving average uses length x^theta in the profile average."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("profile-l1"),
                DeclarationHandle.Create(Prefix + "profileL1"),
                H("Profile absolute integral"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The profile L1 size is the integral of abs(g) for unit interval measure."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("tail-profile"),
                DeclarationHandle.Create(Prefix + "tailProfile"),
                H("Tail profiles"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The tail profile at r is the oriented integral of g from r to 1."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("q"),
                DeclarationHandle.Create(Prefix + "Q"),
                H("Profile quadratic energy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Q(g) is the iterated integral on the unit square of g(s)*g(t)*min(s,t)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("increment"),
                DeclarationHandle.Create(Prefix + "increment"),
                H("Increments"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The increment D_h(x) is E(x+h)-E(x), for a real error function E and real h and x."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cumulative-variance"),
                DeclarationHandle.Create(Prefix + "cumulativeVariance"),
                H("Cumulative variance"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "V(Y,h) is the oriented integral of D_h(x)^2 from 1 to Y."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fixed-length"),
                DeclarationHandle.Create(Prefix + "fixedLength"),
                H("The fixed comparison length"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The comparison length is c*X^theta."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("length-log"),
                DeclarationHandle.Create(Prefix + "lengthLog"),
                H("The length logarithm"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The length logarithm is log(X/(c*X^theta))."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mean-square-scale"),
                DeclarationHandle.Create(Prefix + "meanSquareScale"),
                H("The dyadic scale"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The normalization of the moving-length mean square is X^(1-theta)*log(X)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("locally-bounded-measurable"),
                DeclarationHandle.Create(Prefix + "LocallyBoundedMeasurable"),
                H("Regularity of an error function"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An error function is measurable and, on each closed finite real interval, its absolute value has a finite nonnegative upper bound."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cumulative-variance-band-asymptotic-for"),
                DeclarationHandle.Create(Prefix + "CumulativeVarianceBandAsymptoticFor"),
                H("The uniform variance hypothesis"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each positive epsilon and all sufficiently large Y, uniformly for Y^alpha<=h<=Y^beta, the absolute difference between V(Y,h)/(Y*h*log(Y/h)) and 1 is at most epsilon. The threshold for Y precedes the choice of h."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("short-interval-mean-square-bound-for"),
                DeclarationHandle.Create(Prefix + "ShortIntervalMeanSquareBoundFor"),
                H("The short-interval mean-square hypothesis"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "There are C>0 and X0>=2 such that, for X>=X0 and 0<theta<=1, the integral over [X,2X] of (E((1+theta)*x)-E(x))^2 is at most C*theta*X^2*log(2/theta)^2."))),
                DescribeRole.Definition))));
}

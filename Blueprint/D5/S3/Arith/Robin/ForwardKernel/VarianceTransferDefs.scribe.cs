using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class VarianceTransferDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Increments, triangular averages, and the uniform short-interval variance hypotheses.",
        H("Variance transfer definitions"),
        Blocks(
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
                DescribeId.Create("triangular-primitive"),
                DeclarationHandle.Create(Prefix + "triangularPrimitive"),
                H("Triangular primitives"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "B_h(x) is the oriented integral of D_u(x) with respect to u from 0 to h."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("triangular-average"),
                DeclarationHandle.Create(Prefix + "triangularAverage"),
                H("Triangular averages"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "P_h(x) is B_h(x)/h^2."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fixed-length"),
                DeclarationHandle.Create(Prefix + "fixedLength"),
                H("The fixed comparison length"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The comparison length is c*X^(4/5)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("length-log"),
                DeclarationHandle.Create(Prefix + "lengthLog"),
                H("The length logarithm"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The length logarithm is log(X/(c*X^(4/5)))."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mean-square-scale"),
                DeclarationHandle.Create(Prefix + "meanSquareScale"),
                H("The dyadic scale"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The normalization of the moving-length mean square is X^(1/5)*log(X)."))),
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
                    "For each positive epsilon and all sufficiently large Y, uniformly for Y^(3/4)<=h<=Y^(7/8), the absolute difference between V(Y,h)/(Y*h*log(Y/h)) and 1 is at most epsilon. The threshold for Y precedes the choice of h."))),
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

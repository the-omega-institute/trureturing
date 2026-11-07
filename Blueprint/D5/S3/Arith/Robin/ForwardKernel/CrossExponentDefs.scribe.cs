using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class CrossExponentDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/CrossExponentDefs.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Square norms, moving increments, and forward averages for comparisons between power scales.",
        H("Cross-exponent averages and variance scales"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("interval-l2"),
                DeclarationHandle.Create(Prefix + "intervalL2"),
                H("Interval square norm"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The interval square norm of u on [A,B] is the square root of the oriented integral of u(x)^2. Its norm interpretation is used when A is at most B."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("moving-increment"),
                DeclarationHandle.Create(Prefix + "movingIncrement"),
                H("Moving increments"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The moving increment at x is E(x+s*x^theta)-E(x), using the shared increment function."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("moving-shift"),
                DeclarationHandle.Create(Prefix + "movingShift"),
                H("Moving endpoints"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The moving endpoint is x+s*x^theta."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("window-average"),
                DeclarationHandle.Create(Prefix + "windowAverage"),
                H("Forward window averages"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The forward window average of u at x is the integral of u(x+r) for r from zero to R, divided by R."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("comparable-length-variance-upper-for"),
                DeclarationHandle.Create(Prefix + "ComparableLengthVarianceUpperFor"),
                H("Comparable-length variance bounds"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The scale R(X) is eventually positive. For each fixed 0<A<=B and d>0, a positive constant bounds V(d*X,u) by C*X*R(X)*log(X), eventually uniformly for A*R(X)<=u<=B*R(X). The threshold precedes the choice of u.")),
                Paragraph(Text(
                    "The quantifier covers every spatial factor d>0; for C>=1 this is the form supplied by (491.1), since cumulative variance is monotone in its first argument."))),
                DescribeRole.Definition))));
}

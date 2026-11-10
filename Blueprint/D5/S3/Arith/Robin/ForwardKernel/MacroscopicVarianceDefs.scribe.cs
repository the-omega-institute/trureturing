using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class MacroscopicVarianceDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/MacroscopicVarianceDefs.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Macroscopic increments and weighted moments",
        H("Macroscopic increments and weighted moments"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("variance-window-bound"),
                DeclarationHandle.Create(Prefix + "VarianceWindowBound"),
                H("Variance error on a comparable window"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every Y in [X/2,4X] and Y^alpha<=v<=Y^beta, the relative error of V(Y,v) from Y*v*log(Y/v) is at most epsilon."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("variance-scale"),
                DeclarationHandle.Create(Prefix + "varianceScale"),
                H("The macroscopic variance scale"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The scale is X*X^theta*log(X)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("macro-increment"),
                DeclarationHandle.Create(Prefix + "macroIncrement"),
                H("A macroscopic variable length"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At x the increment is E(x+X^theta*a(x/X))-E(x)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("normalized-square"),
                DeclarationHandle.Create(Prefix + "normalizedSquare"),
                H("The normalized square integral"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Integrate f(x)^2 over [X,2X] and divide by X*X^theta*log(X)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("macroscopic-length-bounds"),
                DeclarationHandle.Create(Prefix + "MacroscopicLengthBounds"),
                H("Bounded differentiable lengths"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On [1,2], the length function a is continuously differentiable, takes values in [0,M], and its derivative within the interval has absolute value at most L."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("freezing-error"),
                DeclarationHandle.Create(Prefix + "freezingError"),
                H("The error from freezing lengths on blocks"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Partition [X,2X] into n equal blocks with endpoints X*(1+j/n). Sum the integrals of the squared difference between the variable increment and the increment with length frozen at the left endpoint, and divide by X*X^theta*log(X)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("weighted-macro-covariance"),
                DeclarationHandle.Create(Prefix + "weightedMacroCovariance"),
                H("Weighted covariance of macroscopic increments"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Integrate w(x/X) times the two increments with lengths X^theta*a(x/X) and X^theta*b(x/X) over [X,2X], and divide by X*X^theta*log(X)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("weighted-dyadic-covariance"),
                DeclarationHandle.Create(Prefix + "weightedDyadicCovariance"),
                H("Weighted dyadic covariance"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under logarithmic dyadic probability, integrate phi(U_X) times the two normalized increments B_X(s) and B_X(t), allowing separate exponents for the two increments."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("weighted-dyadic-first-moment"),
                DeclarationHandle.Create(Prefix + "weightedDyadicFirstMoment"),
                H("Weighted dyadic first moment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under logarithmic dyadic probability, integrate phi(U_X)*B_X(s)."))),
                DescribeRole.Definition))));
}

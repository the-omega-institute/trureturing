using System.Numerics;
using System.Text;

namespace StrataLint.Scribe.Tests;

public sealed class ComputedValueTests
{
    private static int evaluationCount;
    private static int unstableCount;

    [Fact]
    public void ExactResultsHaveCanonicalRepresentations()
    {
        Assert.Equal(
            "123456789012345678901234567890",
            new ComputedResult.Integer(BigInteger.Parse("123456789012345678901234567890"))
                .ToCanonicalString());
        Assert.Equal("12.34", new ComputedResult.Decimal(12.3400m).ToCanonicalString());
        Assert.Equal(
            "3/4",
            new ComputedResult.Rational(ExactRational.Create(-6, -8)).ToCanonicalString());
        Assert.Equal(
            "Z(89) + Z(34) = Z(123) = 1010000000_W",
            new ComputedResult.Text(CanonicalComputedText.Create(
                "Z(89) + Z(34) = Z(123) = 1010000000_W"))
                .ToCanonicalString());
    }

    [Fact]
    public void MarkdownWriterEvaluatesAtEmissionAndLabelsComputedValues()
    {
        evaluationCount = 0;
        var document = Document(
            new DocumentBlock.ComputedValue(
                Heading.Create("Exact example"),
                DeterministicComputation.Create(CountedResult)));

        Assert.Equal(0, evaluationCount);

        var first = CanonicalMarkdownWriter.Write(document);
        var second = CanonicalMarkdownWriter.Write(document);

        Assert.Equal(first.ToArray(), second.ToArray());
        Assert.Equal(4, evaluationCount);
        Assert.Equal(
            "# Computed fixture\n\n"
            + "**Exact example:** `3/4` "
            + "⟨computed-by-C#; illustrative, not kernel-verified⟩\n",
            Encoding.UTF8.GetString(first.AsSpan()));
    }

    [Fact]
    public void NonDeterministicComputationFailsClosed()
    {
        unstableCount = 0;
        var document = Document(
            new DocumentBlock.ComputedValue(
                Heading.Create("Unstable"),
                DeterministicComputation.Create(UnstableResult)));

        var exception = Assert.Throws<InvalidOperationException>(
            () => CanonicalMarkdownWriter.Write(document));

        Assert.Contains("deterministic", exception.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void ComputationExceptionFailsClosed()
    {
        var document = Document(
            new DocumentBlock.ComputedValue(
                Heading.Create("Failure"),
                DeterministicComputation.Create(ThrowingResult)));

        var exception = Assert.Throws<InvalidOperationException>(
            () => CanonicalMarkdownWriter.Write(document));

        Assert.Contains("computed C# evaluation failed", exception.Message, StringComparison.Ordinal);
        Assert.IsType<DivideByZeroException>(exception.InnerException);
    }

    [Fact]
    public void ComputationMustUseAStaticDelegate()
    {
        var captured = BigInteger.One;

        var exception = Assert.Throws<ArgumentException>(
            () => DeterministicComputation.Create(
                () => new ComputedResult.Integer(captured)));

        Assert.Contains("static", exception.Message, StringComparison.OrdinalIgnoreCase);
    }

    private static ComputedResult CountedResult()
    {
        evaluationCount++;
        return new ComputedResult.Rational(ExactRational.Create(6, 8));
    }

    private static ComputedResult UnstableResult() =>
        new ComputedResult.Integer(++unstableCount);

    private static ComputedResult ThrowingResult() =>
        throw new DivideByZeroException("fixture");

    private static ScribeDocument Document(DocumentBlock block) =>
        ScribeDocument.Create(
            DefinitionDsl.Header("D5/S1/Digit/Raw", "Computed fixture."),
            Heading.Create("Computed fixture"),
            BlockSequence.Create([block]));
}

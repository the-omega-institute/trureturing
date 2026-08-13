namespace StrataLint.Scribe.Tests;

public sealed class ValuesProjectionTests
{
    [Fact]
    public void ExactQuadraticEvaluationUsesAControlledDecimalInterval()
    {
        var definition = LoadSynthetic("D5/kappa", "Values.kappa", "exact-quadratic", """
            exact_value = "1/(2*phi)"
            rational_numerator = -1
            rational_denominator = 4
            sqrt_five_numerator = 1
            sqrt_five_denominator = 4
            """);

        var result = ValuesEvaluator.Evaluate(definition);

        Assert.Equal("1/(2*phi)", result.Value);
        Assert.Equal("0.309016994374947424", result.Decimal);
        Assert.Equal("0", result.Error);
        var receipt = Assert.Single(result.KernelReceipts);
        Assert.Equal("exact-quadratic", receipt.Kernel);
        Assert.Equal("24", receipt.Parameters["decimal_digits"]);
        Assert.Equal(PhiFractionalPartKernel.PrecisionStrategy, receipt.Parameters["precision_strategy"]);
    }

    [Fact]
    public void CphiProjectionRequiresFourWindowsForItsSpreadEstimate()
    {
        var definition = LoadSynthetic("D5/Cphi", "Values.cPhi", "cphi", """
            term_count = 12
            fractional_part_decimal_digits = 30
            first_fibonacci_index = 5
            last_fibonacci_index = 5
            """) with
        {
            Computation = new ValueComputation.Cphi(new CphiKernelSpec(
                TermCount: 12,
                FractionalPartDecimalDigits: 30,
                FirstFibonacciIndex: 5,
                LastFibonacciIndex: 5)),
        };

        var exception = Assert.Throws<InvalidOperationException>(() => ValuesEvaluator.Evaluate(definition));

        Assert.Contains("at least four", exception.Message, StringComparison.Ordinal);
    }

    private static ValueDefinition LoadSynthetic(
        string id,
        string declaration,
        string computation,
        string computationFields)
    {
        var referenceValue = id == "D5/kappa" ? "1/(2*phi)" : "0";
        var directory = TemporaryFileSystem.Directory.CreateTempSubdirectory("stratalint-values-projection-");
        var path = Path.Combine(directory.FullName, "values-kernels.toml");
        var text = $"""
            schema_version = 1

            [[constants]]
            id = "{id}"
            lean_gid = "D5/S3/Constants/{declaration}"
            lean_statement_sha256 = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
            status = "emitted"
            definition = "synthetic value"
            method = "synthetic"
            reference_value = "{referenceValue}"
            reference_error = "0"
            error = "0"
            """ + "refs = {}\n" + $"""
            computation = "{computation}"
            {computationFields}
            """;
        TemporaryFileSystem.File.WriteAllText(path, text);
        var definition = Assert.Single(ValuesKernelDataLoader.LoadFile(path));
        directory.Delete(recursive: true);
        return definition;
    }

}

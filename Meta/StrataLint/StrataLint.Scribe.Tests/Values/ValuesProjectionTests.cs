using System.Text.Json;
using System.Text;

namespace StrataLint.Scribe.Tests;

public sealed class ValuesProjectionTests
{
    [Fact]
    public void ExactQuadraticEvaluationUsesAControlledDecimalInterval()
    {
        var definition = ValuesDefinitions.All.Single(static item => item.Id == "D5/kappa");

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
    public void CphiEvaluationQuantizesPlatformDependentFloatingOutput()
    {
        var definition = ValuesDefinitions.All.Single(static item => item.Id == "D5/Cphi");

        var result = ValuesEvaluator.Evaluate(definition);

        Assert.Equal("0.04576252043708", result.Value);
        Assert.Equal("0.00000002050367", result.Error);
        var windowReceipt = Assert.Single(
            result.KernelReceipts,
            static receipt => receipt.Kernel == "full-period-window-average");
        Assert.Equal("14", windowReceipt.Parameters["emitted_decimal_places"]);
        Assert.Equal(
            "ceiling-at-emitted-decimal-places",
            windowReceipt.Parameters["error_quantization"]);
        Assert.All(
            windowReceipt.Results.Values,
            static value => Assert.Matches(@"^-?[0-9]+\.[0-9]{14}$", value));
    }

    [Fact]
    public void CphiProjectionRequiresFourWindowsForItsSpreadEstimate()
    {
        var definition = ValuesDefinitions.All.Single(static item => item.Id == "D5/Cphi") with
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

    [Fact]
    public void ValuesWriterIsByteStableAndCarriesTheCompleteAttestation()
    {
        var root = FindRepositoryRoot();

        var first = CanonicalValuesWriter.Write(root);
        var second = CanonicalValuesWriter.Write(root);

        Assert.True(first.AsSpan().SequenceEqual(second.AsSpan()));
        Assert.True(first.AsSpan().SequenceEqual(File.ReadAllBytes(
            Path.Combine(root, CanonicalValuesWriter.RelativePath))));
        Assert.Equal((byte)'\n', first[^1]);
        using var document = JsonDocument.Parse(first.ToArray());
        var attestation = document.RootElement.GetProperty("attestation");
        Assert.Equal("StrataLint.Scribe.ValuesProducer", attestation.GetProperty("emitter").GetString());
        Assert.Equal(1, attestation.GetProperty("emitter_version").GetInt32());
        Assert.Equal("D5/E/values--json", attestation.GetProperty("projection").GetString());
        Assert.Matches("^[0-9a-f]{64}$", attestation.GetProperty("input_sha256").GetString());
        var inputPaths = attestation.GetProperty("inputs").EnumerateArray()
            .Select(static input => input.GetProperty("path").GetString()!)
            .ToArray();
        Assert.Equal(
            [
                "D5/X_Frontier/ValuesProducer.lean",
                "Directory.Build.props",
                "Directory.Packages.props",
                "Meta/StrataLint/StrataLint.Scribe/packages.lock.json",
                "global.json",
            ],
            inputPaths);

        var constants = document.RootElement.GetProperty("constants").EnumerateArray().ToArray();
        Assert.Equal(14, constants.Length);
        Assert.Equal(
            constants.Select(static item => item.GetProperty("id").GetString()).Order(StringComparer.Ordinal),
            constants.Select(static item => item.GetProperty("id").GetString()));
        Assert.All(constants, static item => Assert.Equal(
            JsonValueKind.Array,
            item.GetProperty("kernel_receipts").ValueKind));
        var cphi = Assert.Single(constants, static item =>
            item.GetProperty("id").GetString() == "D5/Cphi");
        Assert.Equal("reference-mismatch-open", cphi.GetProperty("comparison").GetString());
        Assert.Equal(3, cphi.GetProperty("kernel_receipts").GetArrayLength());
    }

    [Fact]
    public void EmitValuesCliWritesAndChecksWithoutOverwritingDrift()
    {
        var sourceRoot = FindRepositoryRoot();
        var root = Path.Combine(Path.GetTempPath(), "stratalint-values-" + Guid.NewGuid().ToString("N"));
        foreach (var inputPath in CanonicalValuesWriter.InputPaths)
        {
            var destination = Path.Combine(root, inputPath);
            Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
            File.Copy(Path.Combine(sourceRoot, inputPath), destination);
        }

        Directory.CreateDirectory(Path.Combine(root, "Blueprint"));
        var working = Path.Combine(root, "Meta", "StrataLint");
        Directory.CreateDirectory(working);

        try
        {
            using var output = new StringWriter();
            using var error = new StringWriter();

            Assert.Equal(0, ScribeCli.Run(["emit-values"], working, output, error));
            Assert.Equal(0, ScribeCli.Run(["emit-values", "--check"], working, output, error));
            Assert.Equal(string.Empty, error.ToString());

            var path = Path.Combine(root, CanonicalValuesWriter.RelativePath);
            File.AppendAllText(path, " ", new UTF8Encoding(false, true));
            var drifted = File.ReadAllBytes(path);

            Assert.Equal(1, ScribeCli.Run(["emit-values", "--check"], working, output, error));
            Assert.Equal(drifted, File.ReadAllBytes(path));
            Assert.Contains("out of date", error.ToString(), StringComparison.Ordinal);
        }
        finally
        {
            Directory.Delete(root, recursive: true);
        }
    }

    private static string FindRepositoryRoot()
    {
        for (var current = new DirectoryInfo(AppContext.BaseDirectory);
             current is not null;
             current = current.Parent)
        {
            if (File.Exists(Path.Combine(current.FullName, "D5", "X_Frontier", "ValuesProducer.lean")))
            {
                return current.FullName;
            }
        }

        throw new DirectoryNotFoundException("Could not locate the repository root.");
    }
}

using System.Text.Json;
using System.Text;

namespace StrataLint.Scribe.Tests;

public sealed class ValuesProjectionTests
{
    [Fact]
    public void ExactQuadraticEvaluationUsesAControlledDecimalInterval()
    {
        var definition = ValuesKernelDataLoader.LoadRepository(RepositoryAccessor.Discover(RepositoryRootCriterion.ValuesProducerDirectoryNotFound).Root.FullPath)
            .Single(static item => item.Id == "D5/kappa");

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
        var definition = ValuesKernelDataLoader.LoadRepository(RepositoryAccessor.Discover(RepositoryRootCriterion.ValuesProducerDirectoryNotFound).Root.FullPath)
            .Single(static item => item.Id == "D5/Cphi");

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
        var definition = ValuesKernelDataLoader.LoadRepository(RepositoryAccessor.Discover(RepositoryRootCriterion.ValuesProducerDirectoryNotFound).Root.FullPath)
            .Single(static item => item.Id == "D5/Cphi") with
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
        var repository = RepositoryAccessor.Discover(RepositoryRootCriterion.ValuesProducerDirectoryNotFound);
        var root = repository.Root.FullPath;

        var first = CanonicalValuesWriter.Write(root);
        var second = CanonicalValuesWriter.Write(root);

        Assert.True(first.AsSpan().SequenceEqual(second.AsSpan()));
        Assert.True(first.AsSpan().SequenceEqual(repository.ReadAllBytes(
            RepositoryRelativePath.Create(CanonicalValuesWriter.RelativePath))));
        Assert.Equal((byte)'\n', first[^1]);
        using var document = JsonDocument.Parse(first.ToArray());
        var attestation = document.RootElement.GetProperty("attestation");
        var consistency = attestation.GetProperty("consistency");
        Assert.Equal(
            "gid+kind=def+std3+statement-sha256",
            consistency.GetProperty("lean_binding").GetString());
        Assert.Equal(
            "not-kernel-evaluated:noncomputable-real",
            consistency.GetProperty("numeric_binding").GetString());
        Assert.Equal("StrataLint.Scribe.ValuesProducer", attestation.GetProperty("emitter").GetString());
        Assert.Equal(2, attestation.GetProperty("emitter_version").GetInt32());
        Assert.Equal("D5/E/values--json", attestation.GetProperty("projection").GetString());
        var provenance = attestation.GetProperty("provenance").EnumerateArray()
            .Select(static item => item.GetString()!)
            .ToArray();
        Assert.Equal(14, provenance.Length);
        Assert.All(provenance, static gid => Assert.StartsWith(
            "D5/S3/Constants/Values.",
            gid,
            StringComparison.Ordinal));
        Assert.Matches("^[0-9a-f]{64}$", attestation.GetProperty("input_sha256").GetString());
        var inputPaths = attestation.GetProperty("inputs").EnumerateArray()
            .Select(static input => input.GetProperty("path").GetString()!)
            .ToArray();
        Assert.Equal(
            [
                ValuesKernelDataLoader.LeanModulePath,
                CanonicalValuesWriter.InputPath,
                "Directory.Build.props",
                "Directory.Packages.props",
                ValuesKernelDataLoader.RelativePath,
                CanonicalValuesWriter.ScribeLockPath,
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
        Assert.All(constants, item =>
        {
            var leanGid = item.GetProperty("lean_gid").GetString();
            Assert.Contains(leanGid, provenance, StringComparer.Ordinal);
            Assert.Equal(leanGid, item.GetProperty("provenance").GetString());
            Assert.Matches(
                "^[0-9a-f]{64}$",
                item.GetProperty("lean_statement_sha256").GetString());
        });
        Assert.Equal(2, document.RootElement.GetProperty("schema_version").GetInt32());
        var cphi = Assert.Single(constants, static item =>
            item.GetProperty("id").GetString() == "D5/Cphi");
        Assert.Equal("reference-mismatch-open", cphi.GetProperty("comparison").GetString());
        Assert.Equal(3, cphi.GetProperty("kernel_receipts").GetArrayLength());
    }

    [Fact]
    public void EmitValuesCliWritesAndChecksWithoutOverwritingDrift()
    {
        var repository = RepositoryAccessor.Discover(RepositoryRootCriterion.ValuesProducerDirectoryNotFound);
        var root = Path.Combine(Path.GetTempPath(), "stratalint-values-" + Guid.NewGuid().ToString("N"));
        foreach (var inputPath in CanonicalValuesWriter.InputPaths)
        {
            var destination = Path.Combine(root, inputPath);
            TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
            repository.CopyTo(RepositoryRelativePath.Create(inputPath), destination);
        }

        TemporaryFileSystem.Directory.CreateDirectory(Path.Combine(root, "Blueprint"));
        var working = Path.Combine(root, "Meta", "StrataLint");
        TemporaryFileSystem.Directory.CreateDirectory(working);

        try
        {
            using var output = new StringWriter();
            using var error = new StringWriter();

            Assert.Equal(0, ScribeCli.Run(["emit-values"], working, output, error));
            Assert.Equal(0, ScribeCli.Run(["emit-values", "--check"], working, output, error));
            Assert.Equal(string.Empty, error.ToString());

            var path = Path.Combine(root, CanonicalValuesWriter.RelativePath);
            TemporaryFileSystem.File.AppendAllText(path, " ", new UTF8Encoding(false, true));
            var drifted = TemporaryFileSystem.File.ReadAllBytes(path);

            Assert.Equal(1, ScribeCli.Run(["emit-values", "--check"], working, output, error));
            Assert.Equal(drifted, TemporaryFileSystem.File.ReadAllBytes(path));
            Assert.Contains("out of date", error.ToString(), StringComparison.Ordinal);
        }
        finally
        {
            TemporaryFileSystem.Directory.Delete(root, recursive: true);
        }
    }
}

using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class ValuesProjectionLoaderTests
{
    private const string InputPath = ValuesProjectionLoader.InputPath;
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);
    private static readonly ImmutableArray<string> InputPaths = ValuesProjectionLoader.InputPaths;

    [Fact]
    public void CanonicalProjectionValidatesFourteenDefinitionsAndItsInputAttestation()
    {
        var input = StrictUtf8.GetBytes("formal values producer input\n");
        var inputs = Inputs(input);
        var snapshot = Snapshot(inputs, Projection(inputs));

        var projection = ValuesProjectionLoader.Load(snapshot);

        Assert.Equal(14, projection.Definitions.Count);
        Assert.Equal(8, projection.Definitions.Values.Count(static item => item.Status == "emitted"));
        Assert.Equal(6, projection.Definitions.Values.Count(static item => item.Status == "registered-open"));
    }

    [Fact]
    public void ProjectionFailsClosedWhenTheAttestedInputDrifts()
    {
        var input = StrictUtf8.GetBytes("formal values producer input\n");
        var inputs = Inputs(input);
        var projection = Projection(inputs);
        var drifted = StrictUtf8.GetBytes("formal values producer input drifted\n");
        var inputIndex = InputPaths.IndexOf(InputPath);
        var snapshot = Snapshot(inputs.SetItem(inputIndex, (InputPath, drifted)), projection);

        var exception = Assert.Throws<FormatException>(() => ValuesProjectionLoader.Load(snapshot));

        Assert.Contains("input SHA-256", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ProjectionFailsClosedWhenThePinnedEnvironmentDrifts()
    {
        var inputs = Inputs(StrictUtf8.GetBytes("formal values producer input\n"));
        var projection = Projection(inputs);
        var drifted = inputs.SetItem(
            2,
            (InputPaths[2], StrictUtf8.GetBytes("<Project><!-- drift --></Project>\n")));
        var snapshot = Snapshot(drifted, projection);

        var exception = Assert.Throws<FormatException>(() => ValuesProjectionLoader.Load(snapshot));

        Assert.Contains("input SHA-256", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ProjectionFailsClosedWhenCanonicalBytesDrift()
    {
        var input = StrictUtf8.GetBytes("formal values producer input\n");
        var inputs = Inputs(input);
        var projection = Projection(inputs).ToArray();
        projection[^1] = (byte)' ';
        var snapshot = Snapshot(inputs, ImmutableArray.CreateRange(projection));

        var exception = Assert.Throws<FormatException>(() => ValuesProjectionLoader.Load(snapshot));

        Assert.Contains("canonical", exception.Message, StringComparison.OrdinalIgnoreCase);
    }

    private static RepositorySnapshot Snapshot(
        ImmutableArray<(string Path, byte[] Bytes)> inputs,
        ImmutableArray<byte> projection)
    {
        var entries = inputs.Select(static input => new RawRepositoryEntry(
                input.Path,
                ImmutableArray.CreateRange(input.Bytes)))
            .Append(new RawRepositoryEntry(ValuesProjectionLoader.RelativePath, projection));
        var decoded = SnapshotDecoder.Decode(RawRepositorySnapshot.Create(
            entries));
        return Assert.IsType<SnapshotDecodeOutcome.Decoded>(decoded).Snapshot;
    }

    private static ImmutableArray<(string Path, byte[] Bytes)> Inputs(byte[] formalInput) =>
        InputPaths.Select(path =>
            (Path: path, Bytes: path == InputPath
                ? formalInput
                : StrictUtf8.GetBytes("fixture for " + path + "\n"))).ToImmutableArray();

    private static ImmutableArray<byte> Projection(
        ImmutableArray<(string Path, byte[] Bytes)> inputs)
    {
        var inputReceipts = inputs.Select(static input =>
            (input.Path, Sha256: Convert.ToHexStringLower(SHA256.HashData(input.Bytes)))).ToArray();
        var combinedSha = CombinedInputSha(inputReceipts);
        var emitted = new HashSet<string>(StringComparer.Ordinal)
        {
            "D5/Ah", "D5/C0", "D5/Cphi", "D5/E", "D5/cstar", "D5/hbar", "D5/kappa", "D5/s1",
        };
        var ids = new[]
        {
            "D5/Ah", "D5/Bh", "D5/C0", "D5/Cphi", "D5/E", "D5/T0", "D5/T1",
            "D5/c1", "D5/c2", "D5/cstar", "D5/delta.mean", "D5/hbar", "D5/kappa", "D5/s1",
        };
        var constants = ids.Select(id => Constant(id, emitted.Contains(id))).ToArray();
        var root = JsonSerializer.SerializeToElement(new
        {
            attestation = new
            {
                consistency = new
                {
                    lean_binding = "gid+kind=def+std3+statement-sha256",
                    numeric_binding = "not-kernel-evaluated:noncomputable-real",
                },
                emitter = "StrataLint.Scribe.ValuesProducer",
                emitter_version = 2,
                input_sha256 = combinedSha,
                inputs = inputReceipts.Select(static input => new
                {
                    path = input.Path,
                    sha256 = input.Sha256,
                }).ToArray(),
                projection = "D5/E/values--json",
                provenance = ids.Select(LeanGid).ToArray(),
            },
            constants,
            schema_version = 2,
        });
        return StructuredCanonicalWriter.WriteJson(root);
    }

    private static object Constant(string id, bool emitted)
    {
        var kernels = emitted
            ? id == "D5/Cphi"
                ? new[]
                {
                    Receipt("exact-fractional-parts"),
                    Receipt("neumaier-summation"),
                    Receipt("full-period-window-average"),
                }
                : new[] { Receipt("exact-quadratic") }
            : [];
        return new
        {
            comparison = emitted ? id == "D5/Cphi" ? "reference-mismatch-open" : "reference-exact" : "not-computed-open",
            @decimal = emitted ? "0.1" : null,
            definition = "typed fixture",
            error = emitted ? "0" : null,
            exact_value = id == "D5/Cphi" || !emitted ? null : "fixture-exact",
            formula = (string?)null,
            id,
            kernel_receipts = kernels,
            lean_gid = LeanGid(id),
            lean_statement_sha256 = new string('a', 64),
            method = emitted ? "fixture-emitted" : "registered-open",
            open_reason = emitted ? null : "fixture parameters are untranslated",
            provenance = LeanGid(id),
            reference_error = "0",
            reference_value = "0.1",
            refs = ImmutableDictionary<string, string>.Empty,
            status = emitted ? "emitted" : "registered-open",
            value = emitted ? "0.1" : null,
        };
    }

    private static object Receipt(string kernel) => new
    {
        kernel,
        parameters = new Dictionary<string, string>(StringComparer.Ordinal) { ["fixture"] = "1" },
        results = new Dictionary<string, string>(StringComparer.Ordinal),
    };

    private static string CombinedInputSha(IEnumerable<(string Path, string Sha256)> inputs)
    {
        var material = "stratalint-scribe-values-input-v2\0" + string.Concat(
            inputs.Select(static input => input.Path + "\0" + input.Sha256 + "\n"));
        return Convert.ToHexStringLower(SHA256.HashData(StrictUtf8.GetBytes(material)));
    }

    private static string LeanGid(string id) => "D5/S3/Constants/Values." + id switch
    {
        "D5/Ah" => "ah",
        "D5/Bh" => "bh",
        "D5/C0" => "c0",
        "D5/Cphi" => "cPhi",
        "D5/E" => "e",
        "D5/T0" => "t0",
        "D5/T1" => "t1",
        "D5/c1" => "c1",
        "D5/c2" => "c2",
        "D5/cstar" => "cStar",
        "D5/delta.mean" => "deltaMean",
        "D5/hbar" => "hBar",
        "D5/kappa" => "kappa",
        "D5/s1" => "s1",
        _ => throw new ArgumentOutOfRangeException(nameof(id)),
    };
}

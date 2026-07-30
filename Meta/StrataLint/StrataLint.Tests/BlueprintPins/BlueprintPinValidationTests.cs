using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class BlueprintPinValidationTests
{
    [Fact]
    public void DuplicateGeneralityKeyRejectsIssue388Pins()
    {
        const string pins = """
            {
              "artifact": "lean",
              "anchors": [],
              "domain": "Carrier",
              "generality": "G",
              "generality": "I",
              "imports": [],
              "module": "CharacteristicEquation",
              "plane": "F",
              "selector": "",
              "tag": "",
              "theory": "D5"
            }
            """;

        var outcome = BlueprintPinManifestLoader.Load(Encoding.UTF8.GetBytes(pins));

        var rejected = Assert.IsType<BlueprintPinManifestLoadOutcome.Rejected>(outcome);
        Assert.Contains("duplicate key", rejected.Message, StringComparison.Ordinal);
        Assert.Contains("generality", rejected.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void UnsupportedRetiredTheoryAnchorRejectsIssue460Pins()
    {
        var unsupportedAnchor = string.Concat("pz", "g/proposition/9.2");
        var outcome = Validate(Pins(
            domain: "Arith",
            module: "PrimeModUnit",
            generality: "G",
            anchors: [unsupportedAnchor]));

        var rejected = Assert.IsType<BlueprintPinValidationOutcome.Rejected>(outcome);
        Assert.Contains(
            rejected.Diagnostics,
            diagnostic => diagnostic.Contains(
                $"anchor '{unsupportedAnchor}'",
                StringComparison.Ordinal));
    }

    [Fact]
    public void UncontrolledSpectralDomainRejectsIssue456Pins()
    {
        var outcome = Validate(Pins(
            domain: "Spectral",
            module: "ComplementaryEntropyBudget",
            generality: "G"));

        var rejected = Assert.IsType<BlueprintPinValidationOutcome.Rejected>(outcome);
        Assert.Contains(
            rejected.Diagnostics,
            static diagnostic => diagnostic.Contains(
                "formal route requires a controlled domain",
                StringComparison.Ordinal));
    }

    [Theory]
    [InlineData("B", "markdown", "")]
    [InlineData("F", "lean", "some_declaration")]
    public void PinManifestMustDescribeOneFormalFileHeader(
        string plane,
        string artifact,
        string selector)
    {
        var outcome = Validate(Pins(
            domain: "Carrier",
            module: "ProspectiveHeader",
            generality: "G",
            plane: plane,
            artifact: artifact,
            selector: selector));

        var rejected = Assert.IsType<BlueprintPinValidationOutcome.Rejected>(outcome);
        Assert.Contains(
            rejected.Diagnostics,
            static diagnostic => diagnostic.Contains(
                "F-layer Lean file",
                StringComparison.Ordinal));
    }

    [Fact]
    public void Issue398InstancePinWithGeneralPremisesReportsSemanticGeneralityAsUndecidable()
    {
        var conj = FormalGid("D5/S0/Carrier/Conj");
        var norm = FormalGid("D5/S0/Carrier/Norm");
        var snapshot = Snapshot(ExistingFormalFiles(conj, norm));
        var outcome = BlueprintPinValidator.Validate(
            Policy(),
            snapshot,
            Pins(
                domain: "Carrier",
                module: "CharacteristicEquation",
                generality: "I",
                imports: [conj.Value, norm.Value]));

        var accepted = Assert.IsType<BlueprintPinValidationOutcome.Accepted>(outcome);
        Assert.Contains(
            accepted.Unverified,
            static item => item.Contains("freely generalizable", StringComparison.Ordinal));
    }

    [Fact]
    public void Issue411PinsRejectAnUnregisteredAnchorFromAnAcceptedScheme()
    {
        var outcome = Validate(Pins(
            domain: "Scale",
            module: "FibonacciPowers",
            generality: "I",
            anchors: ["mathlib/module/Mathlib.Data.Nat.Fib.Basic"]));

        var rejected = Assert.IsType<BlueprintPinValidationOutcome.Rejected>(outcome);
        Assert.Contains(
            rejected.Diagnostics,
            static diagnostic => diagnostic.Contains(
                "unregistered in the typed catalog",
                StringComparison.Ordinal));
    }

    [Fact]
    public void GeneralPinRejectsAnInstanceImportLikeSl010()
    {
        var instanceFact = FormalGid("D5/S0/Carrier/InstanceFact");
        var snapshot = Snapshot(new Dictionary<string, string>(StringComparer.Ordinal)
        {
            [instanceFact.Path.Value] = Header(instanceFact.Value, "I"),
        });
        var outcome = BlueprintPinValidator.Validate(
            Policy(),
            snapshot,
            Pins(
                domain: "Carrier",
                module: "GeneralConsumer",
                generality: "G",
                imports: [instanceFact.Value]));

        var rejected = Assert.IsType<BlueprintPinValidationOutcome.Rejected>(outcome);
        Assert.Contains(
            rejected.Diagnostics,
            diagnostic => diagnostic.Contains(
                $"G artifact imports I fact {instanceFact.Path.Value}",
                StringComparison.Ordinal));
    }

    [Fact]
    public void JumpCocyclePinsAreStructurallyAcceptedWithoutBanningInstanceGenerality()
    {
        var phaseBasic = FormalGid("D5/S1/Phase/Basic");
        var jumpCocycle = FormalGid("D5/S1/Dynamics/JumpCocycle");
        var snapshot = Snapshot(ExistingFormalFiles(phaseBasic));
        var outcome = BlueprintPinValidator.Validate(
            Policy(),
            snapshot,
            Pins(
                domain: "Dynamics",
                module: "JumpCocycle",
                generality: "I",
                imports: [phaseBasic.Value]));

        var accepted = Assert.IsType<BlueprintPinValidationOutcome.Accepted>(outcome);
        Assert.Equal(jumpCocycle.Value, accepted.TargetGid);
    }

    [Fact]
    public void ExistingGeneralCarrierPinsAreAccepted()
    {
        var conj = FormalGid("D5/S0/Carrier/Conj");
        var norm = FormalGid("D5/S0/Carrier/Norm");
        var snapshot = Snapshot(ExistingFormalFiles(conj));
        var outcome = BlueprintPinValidator.Validate(
            Policy(),
            snapshot,
            Pins(
                domain: "Carrier",
                module: "Norm",
                generality: "G",
                imports: [conj.Value]));

        var accepted = Assert.IsType<BlueprintPinValidationOutcome.Accepted>(outcome);
        Assert.Equal(norm.Value, accepted.TargetGid);
        Assert.Empty(accepted.Unverified);
    }

    private static BlueprintPinValidationOutcome Validate(BlueprintPinManifest pins) =>
        BlueprintPinValidator.Validate(
            Policy(),
            Snapshot(new Dictionary<string, string>(StringComparer.Ordinal)
            {
                [AnchorCatalogLoader.RelativePath] = File.ReadAllText(
                    Path.Combine(
                        FindRepositoryRoot(),
                        "Meta",
                        "StrataLint",
                        "Generated",
                        "anchor-catalog.v1.json"),
                    Encoding.UTF8),
            }),
            pins);

    private static BlueprintPinManifest Pins(
        string domain,
        string module,
        string generality,
        string[]? anchors = null,
        string[]? imports = null,
        string plane = "F",
        string artifact = "lean",
        string selector = "")
    {
        var json = JsonSerializer.Serialize(new
        {
            artifact,
            anchors = anchors ?? [],
            domain,
            generality,
            imports = imports ?? [],
            module,
            plane,
            selector,
            tag = "",
            theory = "D5",
        });
        var loaded = BlueprintPinManifestLoader.Load(Encoding.UTF8.GetBytes(json));
        return Assert.IsType<BlueprintPinManifestLoadOutcome.Loaded>(loaded).Manifest;
    }

    private static ValidatedPolicy Policy()
    {
        var root = FindRepositoryRoot();
        var outcome = RegistryLoader.Load(
            File.ReadAllBytes(Path.Combine(root, "Meta", "registry.yaml")),
            File.ReadAllBytes(Path.Combine(root, "Meta", "domains.yaml")));
        return Assert.IsType<RegistryLoadOutcome.Accepted>(outcome).Policy;
    }

    private static RepositorySnapshot Snapshot(IReadOnlyDictionary<string, string> files)
    {
        var raw = RawRepositorySnapshot.Create(
            files.Select(static pair => RawRepositoryEntry.FromText(pair.Key, pair.Value)));
        return Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
    }

    private static Dictionary<string, string> ExistingFormalFiles(params Gid[] gids)
    {
        var root = FindRepositoryRoot();
        return gids.ToDictionary(
            static gid => gid.Path.Value,
            gid => File.ReadAllText(
                Path.Combine(root, gid.Path.Value.Replace('/', Path.DirectorySeparatorChar)),
                Encoding.UTF8),
            StringComparer.Ordinal);
    }

    private static Gid FormalGid(string value)
    {
        Assert.True(Gid.TryParse(value, out var gid));
        Assert.Equal(value, gid.Value);
        return gid;
    }

    private static string Header(string gid, string generality) => $"""
        /- GID: {gid}
           generality: {generality}
           mirror-B: D5/B/{gid[3..]}
           mirror-E: none(waiver:test-fixture)
           anchors: []
           digest: Blueprint pin test fixture. -/
        """;

    private static string FindRepositoryRoot()
    {
        for (var current = new DirectoryInfo(AppContext.BaseDirectory);
             current is not null;
             current = current.Parent)
        {
            if (File.Exists(Path.Combine(current.FullName, "Meta", "domains.yaml")))
            {
                return current.FullName;
            }
        }

        throw new DirectoryNotFoundException("Could not locate repository root.");
    }
}

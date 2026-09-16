using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class InformationTemplateDebtStoreTests
{
    internal const string Seed = "d37c6134f47ae7f6faa9bf5d5cd0532b59c4d475";
    internal const string Source = "import LeanInformationAudit.Syntax\n-- Fixture.Registration: loader fixture occurrence A\n";
    internal const string RowPath = "Golden/InformationTemplateDebt/rows/1a49292654bc35592997b07d5fab4dbc7527947ec8c534fefdf5a4ff34d07daa.json";
    // Independent design fixture bytes, including the specified final LF.
    internal const string Row = """
        {"base_content_inputs":[{"path":"Registration.lean","sha256":"8b1a59ca0701832dce71a44850507e702d9e3399af64d43523d4d50da818189a"}],"base_registration_source_sha256":"8b1a59ca0701832dce71a44850507e702d9e3399af64d43523d4d50da818189a","base_statement_identity":"c7601acced7b5f6af7aa33f628dea763c75550049f2fe0b83a7e489eb2c6c151","key":{"catalog":"canonical","object_arena":"Fixture.arena","registration_module":"Fixture.Registration","root":"Fixture.Root","theorem":"Fixture.theorem_a"},"reason":"undeclared","schema_version":1,"seed_base":"d37c6134f47ae7f6faa9bf5d5cd0532b59c4d475"}
        """ + "\n";

    internal static RepositorySnapshot Snapshot(params (string Path, string Text)[] files) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create(files.Select(f => RawRepositoryEntry.FromText(f.Path, f.Text))))).Snapshot;

    internal static InformationTemplateDebtRow Read(string row = Row, string path = RowPath, string seed = Seed) =>
        InformationTemplateDebtStore.ReadRow(path, Encoding.UTF8.GetBytes(row), seed,
            Snapshot(("Registration.lean", Source)));

    [Theory]
    [InlineData("Golden/InformationTemplateDebt/activation.json", true)]
    [InlineData(RowPath, true)]
    [InlineData("Golden/InformationTemplateDebt/rows/activation.json", false)]
    [InlineData("Golden/InformationTemplateDebt/rows/abc.json", false)]
    [InlineData("Golden/InformationTemplateDebt/activation.json/extra", false)]
    public void debt_paths_have_one_canonical_layout(string path, bool accepted) =>
        Assert.Equal(accepted, InformationTemplateDebtStore.IsCanonicalPath(path));

    [Fact]
    public void debt_fixture_roundtrip_accepted()
    {
        var row = Read();
        Assert.Equal(RowPath, InformationTemplateDebtStore.PathFor(row.Key));
        Assert.Equal(Row, Encoding.UTF8.GetString(InformationTemplateDebtStore.WriteRow(row).AsSpan()));
        Assert.Equal(Seed, row.SeedBase);
    }

    [Fact]
    public void debt_snapshot_load_retains_exact_row()
    {
        var rows = InformationTemplateDebtStore.Load(Snapshot(
            (RowPath, Row), (InformationTemplateDebtStore.ActivationPath, "ignored by row loader"),
            ("Unrelated.json", "not a debt row")), new(Seed, false), Snapshot(("Registration.lean", Source)));
        var pair = Assert.Single(rows);
        var key = new InformationOccurrenceKey("Fixture.Root", "Fixture.Registration", "Fixture.theorem_a",
            "Fixture.arena", "canonical");
        Assert.Equal(key, pair.Key);
        Assert.Equal(key, pair.Value.Key);
        Assert.Equal(Seed, pair.Value.SeedBase);
        Assert.Equal("c7601acced7b5f6af7aa33f628dea763c75550049f2fe0b83a7e489eb2c6c151", pair.Value.StatementIdentity);
        Assert.Equal("8b1a59ca0701832dce71a44850507e702d9e3399af64d43523d4d50da818189a",
            pair.Value.RegistrationSourceSha256);
        Assert.Equal(new InformationTemplateContentInput("Registration.lean", pair.Value.RegistrationSourceSha256),
            Assert.Single(pair.Value.ContentInputs));
        Assert.Equal(Row, Encoding.UTF8.GetString(InformationTemplateDebtStore.WriteRow(pair.Value).AsSpan()));
    }

    [Fact]
    public void debt_snapshot_load_empty_control() =>
        Assert.Empty(InformationTemplateDebtStore.Load(Snapshot(), new(Seed, false), Snapshot()));

    [Theory]
    [InlineData("plain")]
    [InlineData("missing")]
    [InlineData("malformed")]
    [InlineData("symlink")]
    public void debt_snapshot_filemap_fragments_are_snapshot_bound(string change)
    {
        const string manifest = "schema_version = 2\ninclude = [\"FILEMAP.inputs.toml\"]\n";
        const string fragment = "schema_version = 2\nfiles = [ { pattern = \"Registration.lean\", "
            + "runtime_disposition = \"committed-source\" } ]\n";
        var files = new List<(string Path, string Text)>
        {
            ("Meta/FILEMAP.toml", manifest), ("Registration.lean", Source), ("Original.lean", Source),
        };
        if (change != "missing")
            files.Add(("Meta/FILEMAP.inputs.toml", change switch
            {
                "malformed" => "schema_version = 2\nfiles = []\n",
                "symlink" => fragment.Replace(" } ]", ", symlink = { target = \"Original.lean\", kind = \"file\" } } ]",
                    StringComparison.Ordinal),
                _ => fragment,
            }));
        var inputs = Snapshot(files.ToArray());
        ImmutableDictionary<InformationOccurrenceKey, InformationTemplateDebtRow> Load() =>
            InformationTemplateDebtStore.Load(Snapshot((RowPath, Row)), new(Seed, false), inputs);
        if (change == "plain")
        {
            Assert.Equal(Row, Encoding.UTF8.GetString(
                InformationTemplateDebtStore.WriteRow(Assert.Single(Load()).Value).AsSpan()));
            return;
        }
        var error = Assert.ThrowsAny<FormatException>(() => Load());
        Assert.Contains(change switch
        {
            "missing" => "included file is unavailable in this snapshot",
            "malformed" => "files must contain at least one entry",
            _ => "DTR-DebtSchema: unavailable, changed or noncanonical input Registration.lean",
        }, error.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("version")]
    [InlineData("duplicate")]
    [InlineData("unknown")]
    [InlineData("whitespace")]
    [InlineData("missing")]
    [InlineData("path")]
    [InlineData("input-hash")]
    public void debt_snapshot_load_rejects_malformed_row(string mutation) =>
        Assert.Throws<FormatException>(() => InformationTemplateDebtStore.Load(
            Snapshot((RowPath, MalformedRow(mutation))), new(Seed, false), Snapshot(("Registration.lean", Source))));

    [Theory]
    [InlineData("path")]
    [InlineData("seed")]
    [InlineData("inputs")]
    public void debt_snapshot_load_rejects_wrong_path_or_seed_or_inputs(string mutation) =>
        Assert.Throws<FormatException>(() => InformationTemplateDebtStore.Load(
            Snapshot((mutation == "path" ? RowPath.Replace("1a492", "2a492", StringComparison.Ordinal) : RowPath, Row)),
            new(mutation == "seed" ? "a37c6134f47ae7f6faa9bf5d5cd0532b59c4d475" : Seed, false),
            mutation == "inputs" ? Snapshot() : Snapshot(("Registration.lean", Source))));

    [Fact]
    public void debt_wrong_path_rejected() =>
        Assert.Throws<FormatException>(() => Read(path: RowPath.Replace("1a492", "2a492", StringComparison.Ordinal)));

    [Theory]
    [InlineData("version")]
    [InlineData("duplicate")]
    [InlineData("unknown")]
    [InlineData("whitespace")]
    [InlineData("missing")]
    [InlineData("path")]
    [InlineData("input-hash")]
    public void debt_strict_schema_rejected(string mutation)
    {
        Assert.Throws<FormatException>(() => Read(MalformedRow(mutation)));
    }

    private static string MalformedRow(string mutation) => mutation switch
        {
            "version" => Row.Replace("\"schema_version\":1", "\"schema_version\":2", StringComparison.Ordinal),
            "duplicate" => Row.Replace("\"schema_version\":1", "\"schema_version\":1,\"schema_version\":1", StringComparison.Ordinal),
            "unknown" => Row.Replace("\"schema_version\":1", "\"schema_version\":1,\"exempt\":true", StringComparison.Ordinal),
            "whitespace" => Row.Replace(":1", ": 1", StringComparison.Ordinal),
            "missing" => Row.Replace("\"reason\":\"undeclared\",", "", StringComparison.Ordinal),
            "path" => Row.Replace("Registration.lean", "../Registration.lean", StringComparison.Ordinal),
            "input-hash" => Row.Replace("8b1a59", "8b1a58", StringComparison.Ordinal),
            _ => throw new ArgumentException(nameof(mutation)),
        };

    [Fact]
    public void seed_retarget_rejected() =>
        Assert.Throws<FormatException>(() => Read(seed: "a37c6134f47ae7f6faa9bf5d5cd0532b59c4d475"));

    [Fact]
    public void seed_missing_base_input_rejected() =>
        Assert.Throws<FormatException>(() => InformationTemplateDebtStore.ReadRow(
            RowPath, Encoding.UTF8.GetBytes(Row), Seed, Snapshot()));

    [Theory]
    [InlineData("source")]
    [InlineData("missing")]
    [InlineData("symlink")]
    [InlineData("manifest")]
    public void input_snapshot_replacement_rechecked(string replacement)
    {
        var original = Snapshot(("Registration.lean", Source));
        InformationTemplateDebtRow ReadFrom(RepositorySnapshot snapshot) =>
            InformationTemplateDebtStore.ReadRow(RowPath, Encoding.UTF8.GetBytes(Row), Seed, snapshot);
        void Accept(RepositorySnapshot snapshot) =>
            Assert.Equal(Row, Encoding.UTF8.GetString(InformationTemplateDebtStore.WriteRow(ReadFrom(snapshot)).AsSpan()));
        Accept(original);
        Accept(original);
        var next = replacement switch
        {
            "source" => Snapshot(("Registration.lean", Source + "-- changed\n")),
            "missing" => Snapshot(),
            "symlink" => Snapshot(("Registration.lean", Source), ("Meta/FILEMAP.toml", """
                schema_version = 2
                [[files]]
                pattern = "Registration.lean"
                runtime_disposition = "committed-source"
                symlink = { target = "Original.lean", kind = "file" }
                """ + "\n")),
            "manifest" => Snapshot(("Registration.lean", Source), ("Meta/FILEMAP.toml", "invalid\n")),
            _ => throw new ArgumentException(nameof(replacement)),
        };
        Assert.ThrowsAny<FormatException>(() => ReadFrom(next));
        Accept(original);
        Accept(Snapshot(("Registration.lean", Source)));
    }

    [Fact]
    public void original_protected_activation_accepted()
    {
        var activation = InformationTemplateDebtStore.ReadActivation(Snapshot(
            (InformationTemplateDebtStore.ActivationPath,
                "{\"activated\":false,\"schema_version\":1,\"seed_base\":\"" + Seed + "\"}\n")));
        Assert.Equal(Seed, activation.SeedBase);
        Assert.False(activation.Activated);
    }

    [Fact]
    public void missing_activation_rejected() =>
        Assert.Throws<FormatException>(() => InformationTemplateDebtStore.ReadActivation(Snapshot()));
    [Theory]
    [InlineData("Fixture.α₁.lemma?")]
    [InlineData("Fixture.«中文.name».value")]
    [InlineData("Fixture.«».23")]
    public void canonical_lean_name_roundtrip(string name) =>
        Assert.Equal(name, InformationTemplateJson.Name(name));

    [Theory]
    [InlineData("Fixture.«alpha»")]
    [InlineData("Fixture.中文")]
    [InlineData("Fixture.α.01")]
    [InlineData("Fixture.«missing")]
    [InlineData("Fixture.«name»tail")]
    [InlineData("Fixture.")]
    public void noncanonical_lean_name_rejected(string name) =>
        Assert.Throws<FormatException>(() => InformationTemplateJson.Name(name));
}

namespace StrataLint.Lean.Tests;

public sealed class InspectorNativeInterfaceTests(InspectorCompilerFixture compiler) : IClassFixture<InspectorCompilerFixture>
{
    // The standalone Interface package checks use a class-owned compiler stage.
    [Theory]
    [InlineData("test_native.NativeTests.test_interface_standalone_core_only")]
    [InlineData("test_native.NativeTests.test_interface_only_reports_missing_handler")]
    [InlineData("test_native.NativeTests.test_interface_grammar_has_single_owner")]
    [InlineData("test_native.NativeTests.test_interface_registered_build_inputs")]
    [InlineData("test_native.NativeTests.test_interface_records_have_single_owner")]
    [InlineData("test_native.NativeTests.test_interface_store_cross_module_persistence")]
    [InlineData("test_native.NativeTests.test_interface_edit_rebuilds_implementation_consumer")]
    [InlineData("test_native.NativeTests.test_output_audit_follows_compiler_package_owners")]
    [InlineData("test_native.NativeTests.test_reg_empty_and_nonempty_build_routing")]
    [InlineData("test_native.NativeTests.test_reg_report_rows_relocation_and_defaults")]
    [InlineData("test_native.NativeTests.test_reg_manifest_rejected_before_materialization")]
    [InlineData("test_native.NativeRelocationTests.test_census_callers_in_relocated_package_with_spaces")]
    public void InspectorArtifactBehavior(string suite) => InspectorNativeTestRunner.Run(compiler, suite);
}

public sealed class InspectorNativeSidecarConsumerTests(InspectorEnrollmentFixture compiler) : IClassFixture<InspectorEnrollmentFixture>
{
    private const string Owner = "Reg/Support/SidecarOwner.lean";
    private const string Binder = "Reg/Support/SidecarBinding.lean";
    private static readonly System.Text.Json.JsonSerializerOptions JsonOptions = new() { WriteIndented = true };

    [Fact]
    public void Fresh_public_sidecar_publication_reaches_delta_consumer()
    {
        using var temporary = new StrataLint.TestSupport.TemporaryDirectory();
        var output = Environment.GetEnvironmentVariable("REG_SIDECAR_NATIVE_OUT") ?? temporary.Path;
        Directory.CreateDirectory(output);
        var root = StrataLint.TestSupport.TestRepositoryLayout.FindRoot();
        var produced = StrataLint.TestSupport.TestProcessRunner.Run("env",
            ["REG_SIDECAR_NATIVE_OUT=" + output, "STRATALINT_NATIVE_ENROLLMENT_ROOT=" + compiler.Path, "python3", "-B", "-m", "unittest",
                "test_native.NativeTests.test_reg_sidecar_publication", "-v"],
            Path.Combine(root, "tools/lean-inspector/tests"),
            StrataLint.TestSupport.TestBudgets.ReportSupervisorHangGuard, 1024 * 1024);
        File.WriteAllText(Path.Combine(output, "producer-result.json"), System.Text.Json.JsonSerializer.Serialize(new
        {
            produced.ExitCode,
            stdout = System.Text.Encoding.UTF8.GetString(produced.StandardOutput),
            stderr = System.Text.Encoding.UTF8.GetString(produced.StandardError),
        }, JsonOptions));
        Assert.True(produced.ExitCode == 0, System.Text.Encoding.UTF8.GetString(produced.StandardOutput)
            + System.Text.Encoding.UTF8.GetString(produced.StandardError));
        var policy = StrataLint.TestSupport.RegistryLoadAssert.Accepted(StrataLint.Engine.RegistryPolicyCompiler.Compile(
            new(1, ["Reg/lake-manifest.json", "Reg/lakefile.toml"], [], [],
                [new("json", "structured-json", ["run"], ["formal"])]),
            [new("Carrier", "S0", "Native fixture domain")])).Policy;
        foreach (var (mode, prefix) in new[] { ("validated", "DTR-Declared "),
                     ("unresolved", "DTR-Evidence "), ("missing_slots", "DTR-Undeclared ") })
        {
            var directory = Path.Combine(output, mode);
            var current = System.Text.Json.JsonSerializer.Deserialize<Dictionary<string, string>>(
                File.ReadAllText(Path.Combine(directory, "sources.json")))!;
            // Match this bounded native report's actual source domain. Imported
            // D5 dependencies remain in sources.json and the publication materials.
            current = current.Where(p => !StrataLint.Engine.LeanClosureValidator.IsReportLean(p.Key)
                    || p.Key is Owner or Binder).ToDictionary(p => p.Key, p => p.Value, StringComparer.Ordinal);
            var snapshot = Snapshot(current);
            var raw = Path.Combine(directory, "raw-lean-report.json");
            var report = StrataLint.Engine.RawLeanReportArtifact.ReadFile(raw, snapshot, validateMaterials: true);
            var staleSource = new Dictionary<string, string>(current) { [Binder] = current[Binder] + "-- later bytes\n" };
            Assert.Throws<FormatException>(() => StrataLint.Engine.RawLeanReportArtifact.ReadFile(raw, Snapshot(staleSource)));
            Assert.Null(StrataLint.Engine.RepositoryPathPolicy.Validate(StrataLint.Engine.RepoPath.CreateKnown(Owner), policy));
            Assert.Null(StrataLint.Engine.RepositoryPathPolicy.Validate(StrataLint.Engine.RepoPath.CreateKnown(Binder), policy));
            var producer = report.Files[StrataLint.Engine.RepoPath.CreateKnown(Binder)].InformationTemplates!.Value;
            var selected = StrataLint.Engine.InformationTemplateEvidence.Read(producer, Binder, snapshot);
            Assert.Empty(selected.Inventory);
            var overlay = Assert.Single(selected.Records);
            Assert.Equal(Binder, overlay.BindingSourcePath);
            var ownerPath = StrataLint.Engine.RepoPath.CreateKnown(Owner);
            var binderPath = StrataLint.Engine.RepoPath.CreateKnown(Binder);
            Assert.DoesNotContain(binderPath, StrataLint.Engine.LeanImportClosure.RepositoryPaths(report, ownerPath));
            Assert.Contains(ownerPath, StrataLint.Engine.LeanImportClosure.RepositoryPaths(report, binderPath));
            var joined = StrataLint.Engine.InformationTemplateEvidence.Collect(snapshot, report, [ownerPath],
                bindingSources: [binderPath], occurrences: System.Collections.Immutable.ImmutableHashSet.Create(overlay.Key));
            Assert.Equal(overlay, Assert.Single(joined.Occurrences).Value);
            var baseline = new Dictionary<string, string>(current) { [Binder] = current[Binder] + "-- previous binder\n" };
            var context = Context(baseline, current, report, policy, Binder);
            Assert.Equal(new[] { Binder }, StrataLint.Engine.InformationTemplateSelection.ChangedProducers(context).Select(p => p.Value));
            var actual = StrataLint.Engine.DeclaredTemplateBindingRule.Evaluate(context);
            AssertFinding(Assert.Single(actual), prefix);
            Assert.Contains("NativeSidecar.original", actual[0].Message, StringComparison.Ordinal);
            Assert.DoesNotContain("NativeSidecar.unrelated", actual[0].Message, StringComparison.Ordinal);
            var dispatched = StrataLint.Engine.RuleCatalog.Default.EvaluateSingle(
                StrataLint.Engine.RuleId.CreateKnown(31), context).Diagnostics;
            var dispatchedDtr = Assert.Single(dispatched.Where(d => d.Message.StartsWith("DTR-", StringComparison.Ordinal)));
            Assert.Equal(actual[0].Message, dispatchedDtr.Message);
            Assert.Equal(StrataLint.Engine.AdmissionEffect.Observe, dispatchedDtr.AdmissionEffect);
            Assert.Empty(StrataLint.Engine.DeclaredTemplateBindingRule.Evaluate(Context(current, current, report, policy, Binder, Owner)));
            var ownerBaseline = new Dictionary<string, string>(current) { [Owner] = current[Owner] + "-- previous owner\n" };
            var ownerControl = StrataLint.Engine.DeclaredTemplateBindingRule.Evaluate(Context(ownerBaseline, current, report, policy, Owner));
            Assert.Equal(2, ownerControl.Length);
            AssertFinding(Assert.Single(ownerControl.Where(f => f.Message.Contains("NativeSidecar.original", StringComparison.Ordinal))), prefix);
            AssertFinding(Assert.Single(ownerControl.Where(f => f.Message.Contains("NativeSidecar.unrelated", StringComparison.Ordinal))), "DTR-Undeclared ");
            var malformed = new List<object>();
            foreach (var mutation in new[] { "certificate", "duplicate", "retarget", "missing_original", "unrelated_owner" })
            {
                var wire = System.Text.Json.Nodes.JsonNode.Parse(File.ReadAllText(raw))!;
                var modules = wire["modules"]!.AsArray();
                var owner = modules.Single(m => m!["source_path"]!.GetValue<string>() == Owner)!["information_templates"]!;
                var binder = modules.Single(m => m!["source_path"]!.GetValue<string>() == Binder)!["information_templates"]!;
                if (mutation == "certificate") binder["records"]![0]!["certificate"] = "malformed";
                if (mutation == "duplicate") binder["records"]!.AsArray().Add(binder["records"]![0]!.DeepClone());
                if (mutation == "retarget") binder["records"]![0]!["unit_name"] = "NativeSidecar.missing";
                if (mutation == "missing_original") owner["records"]!.AsArray().RemoveAt(0);
                if (mutation == "unrelated_owner")
                    owner["records"]!.AsArray().Single(r => r!["key"]!["theorem"]!.GetValue<string>() == "NativeSidecar.unrelated")!["certificate"] = "malformed";
                var bytes = Trureturing.Truth.StructuredCanonicalWriter.WriteJson(wire.ToJsonString());
                var changedReport = StrataLint.Engine.RawLeanReportArtifact.Read(bytes.AsSpan(), snapshot);
                var findings = StrataLint.Engine.DeclaredTemplateBindingRule.Evaluate(Context(baseline, current, changedReport, policy, Binder));
                AssertFinding(Assert.Single(findings), mutation == "unrelated_owner" ? prefix : "DTR-Evidence ");
                malformed.Add(new { mutation, findings });
            }
            File.WriteAllText(Path.Combine(directory, "consumer.json"), System.Text.Json.JsonSerializer.Serialize(new
            {
                mode, actual, dispatched = dispatchedDtr, owner_control = ownerControl,
                unchanged_count = 0, joined_count = joined.Occurrences.Count, malformed,
                native_report = raw,
                assemblies = new[] { typeof(StrataLint.Engine.RuleCatalog).Assembly, GetType().Assembly }.Select(a => new
                {
                    a.FullName, a.Location, mvid = a.ManifestModule.ModuleVersionId,
                    sha256 = Convert.ToHexStringLower(System.Security.Cryptography.SHA256.HashData(File.ReadAllBytes(a.Location))),
                    pdb_sha256 = Convert.ToHexStringLower(System.Security.Cryptography.SHA256.HashData(File.ReadAllBytes(Path.ChangeExtension(a.Location, ".pdb")))),
                }),
            }, JsonOptions));
        }
    }

    [Fact]
    public void runtime_assemblies_match_portable_pdb_and_target_source_bytes()
    {
        var root = StrataLint.TestSupport.TestRepositoryLayout.FindRoot();
        using var temporary = new StrataLint.TestSupport.TemporaryDirectory();
        var output = Environment.GetEnvironmentVariable("REG_SIDECAR_NATIVE_OUT") ?? temporary.Path;
        Directory.CreateDirectory(output);
        var bindings = new List<RuntimeBinding>();
        var transported = new List<RuntimeBinding>();
        foreach (var assembly in new[] { typeof(StrataLint.Engine.DeclaredTemplateBindingRule).Assembly, GetType().Assembly })
        {
            var pdb = Path.ChangeExtension(assembly.Location, ".pdb");
            var binding = BindRuntimeSources(root, assembly.Location, pdb, assembly.ManifestModule.ModuleVersionId);
            bindings.Add(binding);
            var transport = Path.Combine(temporary.Path, "transport");
            foreach (var source in binding.AuthoredSources)
            {
                var destination = Path.Combine(transport, source);
                Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
                File.Copy(Path.Combine(root, source), destination, overwrite: true);
            }
            var peCopy = Path.Combine(transport, Path.GetFileName(assembly.Location));
            var pdbCopy = Path.ChangeExtension(peCopy, ".pdb");
            File.Copy(assembly.Location, peCopy, overwrite: true);
            File.Copy(pdb, pdbCopy, overwrite: true);
            if (assembly == GetType().Assembly)
                File.Copy(Path.ChangeExtension(assembly.Location, ".deps.json"), Path.ChangeExtension(peCopy, ".deps.json"));
            transported.Add(BindRuntimeSources(transport, peCopy, pdbCopy, assembly.ManifestModule.ModuleVersionId));
            Assert.Empty(Directory.GetDirectories(transport, "obj", SearchOption.AllDirectories));
        }
        File.WriteAllText(Path.Combine(output, "runtime-source-binding.json"),
            System.Text.Json.JsonSerializer.Serialize(new { bindings, transported }, JsonOptions));
        Assert.All(bindings.Concat(transported), binding =>
            Assert.True(binding.Failures.Count == 0, string.Join("; ", binding.Failures)));
    }

    // CommonBuildOutputs transports compiler FileWrites in TargetDir (plus the
    // reference assembly), not obj source. JudgeSeed's compiler-input binding
    // owns generated inputs; this probe binds authored target bytes separately.
    // These three exact SDK documents retain PDB checksums and PE/PDB identity.
    // They do not assert equality to generated source on the consumer machine.
    private sealed record RuntimeBinding(object Assembly, List<object> Rows, List<string> Failures, List<string> AuthoredSources);

    [System.Diagnostics.CodeAnalysis.SuppressMessage("Security", "CA5350:Do Not Use Weak Cryptographic Algorithms",
        Justification = "Match Roslyn's stored SHA1 document checksums; separately retain SHA256 of authored source.")]
    private static RuntimeBinding BindRuntimeSources(string root, string assemblyPath, string pdbPath, Guid runtimeMvid)
    {
        static byte[] ReadBounded(string path, int limit)
        {
            using var stream = File.OpenRead(path);
            if (stream.Length > limit) throw new InvalidDataException("runtime material exceeds byte limit: " + path);
            var bytes = new byte[checked((int)stream.Length)];
            stream.ReadExactly(bytes);
            return bytes;
        }
        static string Hash(byte[] bytes) => Convert.ToHexStringLower(System.Security.Cryptography.SHA256.HashData(bytes));
        var assemblyBytes = ReadBounded(assemblyPath, 64 * 1024 * 1024);
        var pdbBytes = ReadBounded(pdbPath, 64 * 1024 * 1024);
        using var pe = new System.Reflection.PortableExecutable.PEReader(new MemoryStream(assemblyBytes));
        var metadata = System.Reflection.Metadata.PEReaderExtensions.GetMetadataReader(pe);
        Assert.Equal(runtimeMvid, metadata.GetGuid(metadata.GetModuleDefinition().Mvid));
        var assemblyName = metadata.GetString(metadata.GetAssemblyDefinition().Name);
        var project = assemblyName == "StrataLint.Engine" ? "tools/StrataLint.Engine"
            : assemblyName == "StrataLint.Lean.Tests" ? "tools/tests/StrataLint.Lean.Tests"
            : throw new InvalidDataException("unexpected runtime assembly: " + assemblyName);
        var debug = pe.ReadDebugDirectory().Single(d => d.Type == System.Reflection.PortableExecutable.DebugDirectoryEntryType.CodeView);
        var codeView = pe.ReadCodeViewDebugDirectoryData(debug);
        using var provider = System.Reflection.Metadata.MetadataReaderProvider.FromPortablePdbStream(new MemoryStream(pdbBytes));
        var reader = provider.GetMetadataReader();
        var id = reader.DebugMetadataHeader!.Id;
        Assert.Equal(20, id.Length);
        Assert.Equal(1, codeView.Age);
        Assert.Equal(codeView.Guid, new Guid(id.AsSpan()[..16]));
        Assert.Equal(debug.Stamp, System.Buffers.Binary.BinaryPrimitives.ReadUInt32LittleEndian(id.AsSpan()[16..]));
        Assert.InRange(reader.Documents.Count, 1, 4096);
        var rows = new List<object>();
        var failures = new List<string>();
        var authoredSources = new List<string>();
        foreach (var handle in reader.Documents)
        {
            var document = reader.GetDocument(handle);
            var name = reader.GetString(document.Name).Replace('\\', '/');
            var algorithm = reader.GetGuid(document.HashAlgorithm);
            var checksumBytes = reader.GetBlobBytes(document.Hash);
            var sha256 = algorithm == new Guid("8829d00f-11b8-4213-878b-770e8597ac16");
            var sha1 = algorithm == new Guid("ff1816ec-aa5e-4d10-87f7-6f4963833460");
            if (!(sha256 && checksumBytes.Length == 32 || sha1 && checksumBytes.Length == 20))
                throw new InvalidDataException("unsupported PDB checksum: " + name);
            var expected = Convert.ToHexStringLower(checksumBytes);
            var marker = name.IndexOf("/tools/", StringComparison.Ordinal);
            var relative = marker < 0 ? name : name[(marker + 1)..];
            var generated = new[] { assemblyName + ".GlobalUsings.g.cs",
                ".NETCoreApp,Version=v10.0.AssemblyAttributes.cs", assemblyName + ".AssemblyInfo.cs" }
                .Any(leaf => relative == project + "/obj/Release/net10.0/" + leaf);
            var package = assemblyName == "StrataLint.Lean.Tests" && name.EndsWith(
                "/microsoft.net.test.sdk/18.0.1/build/net8.0/Microsoft.NET.Test.Sdk.Program.cs", StringComparison.Ordinal);
            if (generated || package)
            {
                rows.Add(new { source = relative, source_kind = generated ? "sdk_generated" : "test_sdk_package",
                    binding = "pdb_checksum_only", pdb_hash_algorithm = algorithm, expected_checksum = expected });
                continue;
            }
            if (marker < 0 || !StrataLint.Engine.RepoPath.TryCreate(relative, out _))
            {
                failures.Add("unmapped PDB source " + name);
                continue;
            }
            // Never read producer absolute paths or substitute embedded copies
            // for missing/stale authored source in the assigned target tree.
            var current = Path.Combine(root, relative);
            var sourceKind = "target_file";
            byte[] bytes;
            if (assemblyName == "StrataLint.Engine" && (
                relative.StartsWith(project + "/obj/Release/net10.0/Dunet.Generator/Dunet.Generator.UnionGeneration.UnionGenerator/", StringComparison.Ordinal)
                    && relative.EndsWith(".g.cs", StringComparison.Ordinal)
                || relative == project + "/obj/Release/net10.0/System.Text.RegularExpressions.Generator/System.Text.RegularExpressions.Generator.RegexGenerator/RegexGenerator.g.cs"))
            {
                // Roslyn source-generator documents carry actual embedded
                // bytes, unlike the SDK's three generated Compile items.
                var embedded = reader.GetCustomDebugInformation(handle).Select(reader.GetCustomDebugInformation)
                    .Where(d => reader.GetGuid(d.Kind) == new Guid("0e8a571b-6926-466e-b4ad-8ab04611f5fe")).ToArray();
                Assert.Single(embedded);
                var blob = reader.GetBlobBytes(embedded[0].Value);
                bytes = DecodeEmbeddedSource(blob);
                sourceKind = "pdb_embedded_generated";
            }
            else
            {
                if (!File.Exists(current)) { failures.Add("missing target source " + relative); continue; }
                bytes = ReadBounded(current, 1024 * 1024);
                authoredSources.Add(relative);
            }
            var actual = Hash(bytes);
            var checksum = sha256 ? actual : Convert.ToHexStringLower(System.Security.Cryptography.SHA1.HashData(bytes));
            if (expected != checksum) failures.Add("source checksum mismatch " + relative);
            rows.Add(new { source = relative, source_kind = sourceKind, binding = sourceKind == "target_file" ? "target_bytes" : "embedded_bytes",
                pdb_hash_algorithm = algorithm, expected_checksum = expected, actual_checksum = checksum, source_sha256 = actual });
        }
        return new RuntimeBinding(new { name = assemblyName, mvid = runtimeMvid,
            pe_sha256 = Hash(assemblyBytes), pdb_sha256 = Hash(pdbBytes),
            deps_sha256 = assemblyName == "StrataLint.Lean.Tests"
                ? Hash(ReadBounded(Path.ChangeExtension(assemblyPath, ".deps.json"), 1024 * 1024)) : null,
            codeView.Guid, debug.Stamp }, rows, failures, authoredSources);
    }

    private static byte[] DecodeEmbeddedSource(byte[] blob)
    {
        const int limit = 1024 * 1024;
        if (blob.Length < 4 || blob.Length > limit + 4) throw new InvalidDataException("invalid embedded source size");
        var size = System.Buffers.Binary.BinaryPrimitives.ReadInt32LittleEndian(blob);
        if (size < 0 || size > limit) throw new InvalidDataException("invalid embedded source length");
        if (size == 0) return blob[4..];
        using var compressed = new MemoryStream(blob, 4, blob.Length - 4);
        using var inflate = new System.IO.Compression.DeflateStream(compressed, System.IO.Compression.CompressionMode.Decompress);
        var bytes = new byte[size];
        inflate.ReadExactly(bytes);
        if (inflate.ReadByte() != -1) throw new InvalidDataException("embedded source exceeds declared length");
        return bytes;
    }

    [Theory]
    [InlineData("missing_source")]
    [InlineData("stale_source")]
    [InlineData("wrong_pdb")]
    [InlineData("missing_pdb")]
    [InlineData("wrong_pe")]
    public void runtime_source_binding_rejects_invalid_material(string mutation)
    {
        var root = StrataLint.TestSupport.TestRepositoryLayout.FindRoot();
        var assembly = GetType().Assembly;
        using var temporary = new StrataLint.TestSupport.TemporaryDirectory();
        var target = temporary.Path;
        var source = "tools/tests/StrataLint.Lean.Tests/Native/InspectorNativeInterfaceTests.cs";
        var destination = Path.Combine(target, source);
        Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
        if (mutation == "stale_source") File.WriteAllText(destination, File.ReadAllText(Path.Combine(root, source)) + "// stale\n");
        if (mutation is "missing_source" or "stale_source")
        {
            var result = BindRuntimeSources(target, assembly.Location, Path.ChangeExtension(assembly.Location, ".pdb"),
                assembly.ManifestModule.ModuleVersionId);
            Assert.Contains((mutation == "missing_source" ? "missing target source " : "source checksum mismatch ") + source,
                result.Failures);
            return;
        }
        var other = typeof(StrataLint.Engine.DeclaredTemplateBindingRule).Assembly;
        var pe = mutation == "wrong_pe" ? other.Location : assembly.Location;
        var pdb = mutation == "wrong_pdb" ? Path.ChangeExtension(other.Location, ".pdb")
            : mutation == "missing_pdb" ? Path.Combine(target, "missing.pdb") : Path.ChangeExtension(assembly.Location, ".pdb");
        Assert.ThrowsAny<Exception>(() => BindRuntimeSources(root, pe, pdb, assembly.ManifestModule.ModuleVersionId));
    }

    private static void AssertFinding(StrataLint.Engine.RuleFinding finding, string prefix)
    {
        Assert.StartsWith(prefix, finding.Message, StringComparison.Ordinal);
        Assert.Equal(StrataLint.Engine.AdmissionEffect.Observe, finding.Effect);
    }

    private static StrataLint.Engine.RepositorySnapshot Snapshot(Dictionary<string, string> files) =>
        Assert.IsType<StrataLint.Engine.SnapshotDecodeOutcome.Decoded>(StrataLint.Engine.SnapshotDecoder.Decode(
            StrataLint.Engine.RawRepositorySnapshot.Create(files.Select(p =>
                StrataLint.Engine.RawRepositoryEntry.FromText(p.Key, p.Value))))).Snapshot;

    private static StrataLint.Engine.DeltaRuleContext Context(Dictionary<string, string> baseline,
        Dictionary<string, string> current, StrataLint.Engine.LeanAxiomReport report,
        StrataLint.Engine.ValidatedPolicy policy, params string[] paths)
    {
        var changes = StrataLint.Engine.RawChangeSet.Create(paths);
        var clear = Assert.IsType<StrataLint.Engine.BootstrapOutcome.Clear>(StrataLint.Engine.BootstrapGate.Evaluate(changes));
        return StrataLint.Engine.DeltaRuleContext.Create(Snapshot(current), Snapshot(baseline), policy,
            StrataLint.Engine.AcceptedLeanClosure.Create(report), changes, clear.Capability);
    }
}

// The real enrollment consumer has mathematical prerequisites beyond the
// statement-only Inspector. Prepare only its selected targets in a private
// class fixture under the existing command and supervisor guards.
public sealed class InspectorEnrollmentFixture : IDisposable
{
    private readonly StrataLint.TestSupport.TemporaryDirectory temporary = new();
    private readonly Lazy<string> stage;

    public InspectorEnrollmentFixture()
    {
        stage = new Lazy<string>(() =>
        {
            var root = StrataLint.TestSupport.TestRepositoryLayout.FindRoot();
            var result = StrataLint.TestSupport.TestProcessRunner.Run("python3",
                ["-B", "-m", "packages.reg", temporary.Path],
                System.IO.Path.Combine(root, "tools/lean-inspector/tests"),
                StrataLint.TestSupport.TestBudgets.ReportSupervisorHangGuard, 1024 * 1024);
            Assert.True(result.ExitCode == 0, System.Text.Encoding.UTF8.GetString(result.StandardOutput)
                + System.Text.Encoding.UTF8.GetString(result.StandardError));
            return System.IO.Path.Combine(temporary.Path, "enrollment fixture");
        });
    }

    public string Path => stage.Value;

    public void Dispose() => temporary.Dispose();
}

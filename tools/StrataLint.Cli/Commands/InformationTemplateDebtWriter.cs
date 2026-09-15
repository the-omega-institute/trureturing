using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class InformationTemplateDebtWriter
{
    internal static CommandResult Run(string root, IRepositoryGateway repository, IReadOnlyList<string> arguments)
    {
        try
        {
            if (arguments.Count == 0 || arguments[0] is not ("install" or "initialize" or "discharge"))
                throw new FormatException("information-template-debt requires install, initialize or discharge");
            var options = new Dictionary<string, string>(StringComparer.Ordinal);
            for (var i = 1; i < arguments.Count; i += 2)
                if (i + 1 >= arguments.Count || arguments[i] is not
                    ("--protected-base" or "--candidate-lean-report" or "--seed-lean-report" or "--base-lean-report")
                    || !options.TryAdd(arguments[i], arguments[i + 1]))
                    throw new FormatException("invalid or duplicate information-template-debt option");
            if (!options.TryGetValue("--protected-base", out var requestedBase))
                throw new FormatException("--protected-base is required");
            // Seeding creates its first delta from an already installed, immutable
            // base. Admission's non-vacuous comparison is still required for all
            // other commands and for an initialization against an earlier base.
            var prepared = arguments[0] == "initialize"
                && requestedBase == repository.ResolveCurrentRevision().Revision
                ? new PreparedRepository(requestedBase, repository.ReadCurrentChanges())
                : repository.Prepare(requestedBase);
            InformationTemplateJson.Hash(prepared.Revision, 40);
            var baseline = Decode(repository.ReadRevision(prepared.Revision));
            var currentRaw = repository.ReadCurrent();
            var current = Decode(currentRaw);
            var existing = DebtFiles(current);
            if (arguments[0] == "install")
            {
                if (baseline.TryGetFile(InformationTemplateDebtStore.ActivationPath, out _) || existing.Count != 0)
                    throw new FormatException("DTR-Activation: mechanism already installed or candidate debt exists");
                var installation = new InformationTemplateActivation(prepared.Revision, false);
                Apply(root, existing, new Dictionary<string, ImmutableArray<byte>>(StringComparer.Ordinal)
                {
                    [InformationTemplateDebtStore.ActivationPath] = InformationTemplateDebtStore.WriteActivation(installation),
                }, RequireUnchanged);
                return new(true, "DTR-Inactive installed row-free mechanism\n", "");
            }
            var activation = InformationTemplateDebtStore.ReadActivation(baseline);
            var seed = Decode(repository.ReadRevision(activation.SeedBase));
            var reportDirectory = Path.Combine(root, ".lake", "build", "stratalint");
            string ReportPath(string option, string revision) => options.GetValueOrDefault(option)
                ?? Path.Combine(reportDirectory, "information-template-history", revision, "raw-lean-report.json");
            var seedReport = RawLeanReportArtifact.ReadFile(ReportPath("--seed-lean-report", activation.SeedBase),
                InformationTemplateEvidence.HistoricalInputs(seed, current));
            var seedUniverse = InformationTemplateEvidence.Collect(seed, seedReport);
            var baseDebt = InformationTemplateDebtStore.Load(baseline, activation, seed);
            var headDebt = InformationTemplateDebtStore.Load(current, activation, seed);
            ImmutableDictionary<InformationOccurrenceKey, InformationTemplateDebtRow> retained;
            if (arguments[0] == "initialize")
            {
                if (baseDebt.Count != 0 || headDebt.Count != 0)
                    throw new FormatException("DTR-Seed: initialization cannot replace existing rows");
                retained = Initialize(activation, activation.SeedBase, seed, seedUniverse);
                DeclaredTemplateBindingRule.CheckSeed(activation, seed, seedUniverse, retained);
                if (options.ContainsKey("--candidate-lean-report") || options.ContainsKey("--base-lean-report"))
                    throw new FormatException("DTR-Seed: initialization is seed-only");
            }
            else
            {
                if (!options.TryGetValue("--candidate-lean-report", out var candidatePath))
                    throw new FormatException("--candidate-lean-report is required for discharge");
                var currentReport = RawLeanReportArtifact.ReadFile(candidatePath, current);
                var beforeReport = RawLeanReportArtifact.ReadFile(ReportPath("--base-lean-report", prepared.Revision),
                    InformationTemplateEvidence.HistoricalInputs(baseline, current));
                var after = InformationTemplateEvidence.Collect(current, currentReport);
                var before = InformationTemplateEvidence.Collect(baseline, beforeReport);
                if (!headDebt.Keys.ToHashSet().SetEquals(baseDebt.Keys))
                    throw new FormatException("DTR-Subset: writer requires the untouched protected row set");
                retained = Discharge(activation, baseDebt, after);
                var findings = DeclaredTemplateBindingRule.Evaluate(activation, baseline, current, baseDebt,
                    retained, before, after, prepared.Changes.Paths.Select(p => p.Value).ToHashSet(StringComparer.Ordinal));
                if (findings.Length != 0)
                    throw new FormatException(string.Join("; ", findings.Select(f => f.Code + " " + f.Detail)));
            }
            var outputs = retained.Values.ToDictionary(row => InformationTemplateDebtStore.PathFor(row.Key),
                InformationTemplateDebtStore.WriteRow, StringComparer.Ordinal);
            if (!existing.TryGetValue(InformationTemplateDebtStore.ActivationPath, out var activationBytes)
                || !baseline.TryGetFile(InformationTemplateDebtStore.ActivationPath, out var protectedActivation)
                || !activationBytes.AsSpan().SequenceEqual(protectedActivation.RawBytes.AsSpan()))
                throw new FormatException("DTR-Activation: writer cannot change activation");
            outputs.Add(InformationTemplateDebtStore.ActivationPath, activationBytes);
            Apply(root, existing, outputs, RequireUnchanged);
            return new(true, "DTR-DebtSchema wrote validated debt set\n", "");

            void RequireUnchanged()
            {
                var reread = repository.ReadCurrent();
                if (reread.Entries.Length != currentRaw.Entries.Length
                    || !reread.Entries.OrderBy(e => e.Path, StringComparer.Ordinal)
                        .Zip(currentRaw.Entries.OrderBy(e => e.Path, StringComparer.Ordinal))
                        .All(pair => pair.First.Path == pair.Second.Path
                            && pair.First.Bytes.AsSpan().SequenceEqual(pair.Second.Bytes.AsSpan())))
                    throw new IOException("DTR-Evidence: inputs changed before debt publication");
            }
        }
        catch (Exception error) when (error is FormatException or IOException or InvalidOperationException)
        {
            return new(false, "", error.Message + "\n");
        }
    }

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) => SnapshotDecoder.Decode(raw) switch
    {
        SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
        SnapshotDecodeOutcome.InfrastructureFailure error => throw new FormatException(error.Message),
    };

    private static Dictionary<string, ImmutableArray<byte>> DebtFiles(RepositorySnapshot snapshot) =>
        snapshot.Files.Values.Where(file => file.Path.Value.StartsWith(InformationTemplateDebtStore.Root, StringComparison.Ordinal))
            .ToDictionary(file => file.Path.Value, file => file.RawBytes, StringComparer.Ordinal);

    // Per-file atomic replacements with complete batch rollback, protected by
    // the writer lock. An interrupted/partial set cannot pass residual equality.
    internal static void Apply(string root, IReadOnlyDictionary<string, ImmutableArray<byte>> before,
        IReadOnlyDictionary<string, ImmutableArray<byte>> after, Action requireInputsUnchanged,
        Action<string, string>? commit = null)
    {
        var git = GitWorktreeDirectory.Read(root) ?? throw new IOException("DTR-Required: git worktree unavailable");
        using var guard = new FileStream(Path.Combine(git, "stratalint-information-template-debt.lock"),
            FileMode.OpenOrCreate, FileAccess.ReadWrite, FileShare.None);
        var directory = Path.Combine(root, InformationTemplateDebtStore.Root);
        RequireRegularDirectoryPath(root, directory);
        var actualPaths = Directory.Exists(directory) ? Directory.GetFileSystemEntries(directory) : [];
        if (actualPaths.Any(path => (File.GetAttributes(path) & (FileAttributes.ReparsePoint | FileAttributes.Directory)) != 0)
            || !actualPaths.Select(path => Path.GetRelativePath(root, path).Replace('\\', '/')).ToHashSet(StringComparer.Ordinal)
                .SetEquals(before.Keys)
            || before.Any(pair => !File.ReadAllBytes(Path.Combine(root, pair.Key)).AsSpan().SequenceEqual(pair.Value.AsSpan())))
            throw new IOException("DTR-DebtSchema: debt changed before write");
        requireInputsUnchanged();
        var touched = new List<string>();
        try
        {
            foreach (var path in before.Keys.Union(after.Keys, StringComparer.Ordinal).Order(StringComparer.Ordinal))
            {
                if (before.TryGetValue(path, out var old) && after.TryGetValue(path, out var next)
                    && old.AsSpan().SequenceEqual(next.AsSpan())) continue;
                if (!path.StartsWith(InformationTemplateDebtStore.Root, StringComparison.Ordinal)
                    || !RepoPath.TryCreate(path, out _)
                    || path[InformationTemplateDebtStore.Root.Length..].Contains('/'))
                    throw new FormatException("DTR-DebtSchema: invalid writer path");
                var target = Path.Combine(root, path);
                RequireRegularDirectoryPath(root, directory);
                touched.Add(path);
                if (after.TryGetValue(path, out var bytes))
                {
                    Directory.CreateDirectory(Path.GetDirectoryName(target)!);
                    IngestCommand.ReplaceLedgerAtomically(target, bytes.AsSpan(), commit);
                }
                else File.Delete(target);
            }
        }
        catch (Exception error) when (error is not OutOfMemoryException)
        {
            var failures = new List<Exception> { error };
            foreach (var path in touched.AsEnumerable().Reverse())
                try
                {
                    if (before.TryGetValue(path, out var bytes))
                        IngestCommand.ReplaceLedgerAtomically(Path.Combine(root, path), bytes.AsSpan());
                    else File.Delete(Path.Combine(root, path));
                }
                catch (Exception rollback) when (rollback is not OutOfMemoryException) { failures.Add(rollback); }
            if (failures.Count > 1) throw new AggregateException("DTR-DebtSchema: rollback incomplete", failures);
            throw;
        }
    }

    private static void RequireRegularDirectoryPath(string root, string directory)
    {
        var relative = Path.GetRelativePath(root, directory);
        var current = Path.GetFullPath(root);
        foreach (var component in relative.Split(Path.DirectorySeparatorChar).Prepend(""))
        {
            current = Path.Combine(current, component);
            // GetAttributes also detects a dangling link; Exists would hide it.
            FileAttributes attributes;
            try { attributes = File.GetAttributes(current); }
            catch (FileNotFoundException) { continue; }
            catch (DirectoryNotFoundException) { continue; }
            if ((attributes & FileAttributes.ReparsePoint) != 0
                || (attributes & FileAttributes.Directory) == 0)
                throw new IOException("DTR-DebtSchema: debt directory must be regular");
        }
    }

    internal static ImmutableDictionary<InformationOccurrenceKey, InformationTemplateDebtRow> Initialize(
        InformationTemplateActivation activation, string evaluatedRevision, RepositorySnapshot seed,
        InformationTemplateUniverse inventory)
    {
        if (activation.Activated || activation.SeedBase != evaluatedRevision)
            throw new FormatException("DTR-Seed: initialization requires the original protected inactive seed");
        RequireComplete(inventory);
        var rows = ImmutableDictionary.CreateBuilder<InformationOccurrenceKey, InformationTemplateDebtRow>();
        foreach (var occurrence in inventory.Occurrences.Values)
        {
            if (occurrence.State != InformationTemplateBindingState.Undeclared)
                throw new FormatException("DTR-Seed: seed-only initialization cannot enroll or discharge");
            if (!seed.TryGetFile(occurrence.RegistrationSourcePath, out var source))
                throw new FormatException("DTR-Seed: registration source absent from protected seed");
            var row = new InformationTemplateDebtRow(occurrence.Key, activation.SeedBase,
                occurrence.StatementIdentity, InformationTemplateJson.Sha256(source.RawBytes.AsSpan()),
                occurrence.ContentInputs);
            // Same strict loader used by admission, including every immutable input.
            var bytes = InformationTemplateDebtStore.WriteRow(row);
            rows.Add(row.Key, InformationTemplateDebtStore.ReadRow(InformationTemplateDebtStore.PathFor(row.Key),
                bytes.AsSpan(), activation.SeedBase, seed));
        }

        return rows.ToImmutable();
    }

    internal static ImmutableDictionary<InformationOccurrenceKey, InformationTemplateDebtRow> Discharge(
        InformationTemplateActivation activation,
        ImmutableDictionary<InformationOccurrenceKey, InformationTemplateDebtRow> debt,
        InformationTemplateUniverse inventory)
    {
        if (!activation.Activated) throw new FormatException("DTR-Activation: discharge precedes activation");
        RequireComplete(inventory);
        var retained = debt.ToBuilder();
        foreach (var (key, row) in debt)
        {
            if (row.SeedBase != activation.SeedBase) throw new FormatException("DTR-Seed: mixed or retargeted seed");
            if (!inventory.Occurrences.TryGetValue(key, out var occurrence))
                throw new FormatException("DTR-Inventory: deleting registration cannot discharge debt");
            switch (occurrence.State)
            {
                case InformationTemplateBindingState.DeclaredValidated:
                    if (occurrence.EvidenceRef is null)
                        throw new FormatException("DTR-Evidence: validated occurrence has no certificate");
                    InformationTemplateJson.Hash(occurrence.EvidenceRef, 64);
                    retained.Remove(key);
                    break;
                case InformationTemplateBindingState.DeclaredUnresolved:
                    throw new FormatException("DTR-Evidence: unresolved declaration cannot discharge debt");
                case InformationTemplateBindingState.Undeclared:
                    break;
                default:
                    throw new FormatException("DTR-Evidence: unknown binding state");
            }
        }

        return retained.ToImmutable();
    }

    private static void RequireComplete(InformationTemplateUniverse inventory)
    {
        if (!inventory.Inventory.SetEquals(inventory.Occurrences.Keys)
            || !inventory.GovernedSources.SetEquals(inventory.AssessedSources))
            throw new FormatException("DTR-Inventory: incomplete authoritative inventory");
    }
}

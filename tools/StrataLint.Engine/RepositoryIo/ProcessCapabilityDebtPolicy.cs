using System.Collections.Immutable;
using System.ComponentModel;
using System.Text;
using System.Text.RegularExpressions;
using System.Xml.Linq;

namespace StrataLint.Engine;

internal sealed record ProcessCapabilityDiagnostic(
    string Path,
    int Line,
    int Column,
    string Symbol,
    string Message)
{
    internal string Identity => $"{Path}:{Line}:{Column}:{Symbol}";
}

internal sealed record ProcessCapabilityAudit(
    ImmutableArray<ProcessCapabilityDiagnostic> Diagnostics,
    ImmutableArray<string> InfrastructureFailures);

internal sealed record ProcessCapabilityDebtFinding(string Path, string Message);

internal static class ProcessCapabilityDebtPolicy
{
    internal const string ProjectPath =
        "tools/tests/StrataLint.Tests/StrataLint.Tests.csproj";
    internal const string BanPath =
        "tools/Architecture/BannedSymbols.ProcessCapability.txt";
    internal const string WiringPath =
        "tools/tests/StrataLint.Tests/ProcessCapability.props";
    private const string SharedAnalyzerPath = "tools/tests/Directory.Build.props";
    private const string ImportPath = "ProcessCapability.props";
    private const string AdditionalFileInclude =
        "$(MSBuildThisFileDirectory)../../Architecture/BannedSymbols.ProcessCapability.txt";

    private static readonly ImmutableHashSet<string> RequiredSymbols =
        ImmutableHashSet.Create(
            StringComparer.Ordinal,
            "T:System.Diagnostics.Process",
            "T:System.Diagnostics.ProcessStartInfo",
            "T:StrataLint.Engine.BoundedProcessRunner",
            "T:StrataLint.Tests.TestProcessRunner");

    private static readonly ImmutableHashSet<string> CompilerBindingPaths =
        ImmutableHashSet.Create(
            StringComparer.Ordinal,
            BanPath,
            WiringPath,
            ProjectPath,
            SharedAnalyzerPath,
            ".editorconfig",
            "Directory.Build.props",
            "Directory.Build.targets",
            "Directory.Packages.props",
            "global.json",
            "tools/StrataLint.Cli/StrataLint.Cli.csproj",
            "tools/StrataLint.Engine/StrataLint.Engine.csproj",
            "tools/StrataLint.EngineeringScope/StrataLint.EngineeringScope.csproj",
            "tools/StrataLint.Scribe/StrataLint.Scribe.csproj",
            "tools/Trureturing.Truth/Trureturing.Truth.csproj");

    internal static ImmutableArray<ProcessCapabilityDebtFinding> Evaluate(
        RuleEvaluationContext context)
    {
        if (!context.Current.TryGetFile(ProjectPath, out _)
            || !IsRelevantChange(context.Changes))
        {
            return [];
        }

        var mechanismFindings = ValidateMechanism(context.Current);
        if (mechanismFindings.Length != 0)
        {
            return mechanismFindings;
        }

        var baselineMechanismParts = BaselineMechanismParts(context.Baseline);
        if (baselineMechanismParts is not (0 or 3))
        {
            return
            [
                new ProcessCapabilityDebtFinding(
                    WiringPath,
                    "protected base has a partial process-capability compiler wiring; fail closed"),
            ];
        }

        var bootstrap = baselineMechanismParts == 0 ? context.Current : null;
        var baselineAudit = ProcessCapabilityCompileOracle.Inspect(context.Baseline, bootstrap);
        var currentAudit = ProcessCapabilityCompileOracle.Inspect(context.Current, bootstrap: null);
        var infrastructure = baselineAudit.InfrastructureFailures
            .Select(static failure => $"protected base: {failure}")
            .Concat(currentAudit.InfrastructureFailures.Select(static failure => $"candidate: {failure}"))
            .ToArray();
        if (infrastructure.Length != 0)
        {
            return infrastructure.Select(static failure => new ProcessCapabilityDebtFinding(
                ProjectPath,
                failure)).ToImmutableArray();
        }

        var wiringChanged = baselineAudit.Diagnostics.Length != 0
            && baselineMechanismParts == 3
            && BindingInputsChanged(context.Current, context.Baseline);
        return EvaluateDebt(
            context.Current,
            context.Baseline,
            currentAudit.Diagnostics,
            baselineAudit.Diagnostics,
            wiringChanged);
    }

    internal static ImmutableArray<ProcessCapabilityDebtFinding> EvaluateDebt(
        RepositorySnapshot current,
        RepositorySnapshot baseline,
        IEnumerable<ProcessCapabilityDiagnostic> currentDiagnostics,
        IEnumerable<ProcessCapabilityDiagnostic> baselineDiagnostics,
        bool wiringChanged)
    {
        var inherited = baselineDiagnostics
            .GroupBy(static diagnostic => diagnostic.Identity, StringComparer.Ordinal)
            .Select(static group => group.First())
            .ToDictionary(static diagnostic => diagnostic.Identity, StringComparer.Ordinal);
        if (inherited.Count != 0 && wiringChanged)
        {
            return
            [
                new ProcessCapabilityDebtFinding(
                    WiringPath,
                    "process-capability compiler binding or wiring changed while inherited debt remains"),
            ];
        }

        var findings = ImmutableArray.CreateBuilder<ProcessCapabilityDebtFinding>();
        foreach (var diagnostic in currentDiagnostics
                     .GroupBy(static item => item.Identity, StringComparer.Ordinal)
                     .Select(static group => group.First())
                     .OrderBy(static item => item.Identity, StringComparer.Ordinal))
        {
            if (!inherited.ContainsKey(diagnostic.Identity))
            {
                findings.Add(new ProcessCapabilityDebtFinding(
                    diagnostic.Path,
                    $"candidate-new process capability at {diagnostic.Line}:{diagnostic.Column}: "
                        + diagnostic.Message));
                continue;
            }

            if (!ByteIdentical(current, baseline, diagnostic.Path))
            {
                findings.Add(new ProcessCapabilityDebtFinding(
                    diagnostic.Path,
                    $"process debt at {diagnostic.Line}:{diagnostic.Column} may remain only in a "
                        + "byte-identical protected-base source blob"));
            }
        }

        return findings.ToImmutable();
    }

    private static ImmutableArray<ProcessCapabilityDebtFinding> ValidateMechanism(
        RepositorySnapshot snapshot)
    {
        var findings = ImmutableArray.CreateBuilder<ProcessCapabilityDebtFinding>();
        if (!snapshot.TryGetFile(BanPath, out var ban))
        {
            findings.Add(new ProcessCapabilityDebtFinding(BanPath, "process-capability ban is absent"));
        }
        else
        {
            var symbols = ban.Text.Split('\n', StringSplitOptions.RemoveEmptyEntries)
                .Select(static line => line.Trim().Split(';', 2)[0])
                .ToHashSet(StringComparer.Ordinal);
            if (!symbols.SetEquals(RequiredSymbols))
            {
                findings.Add(new ProcessCapabilityDebtFinding(
                    BanPath,
                    "process-capability ban must name exactly Process, ProcessStartInfo, "
                        + "BoundedProcessRunner, and TestProcessRunner"));
            }
        }

        if (!snapshot.TryGetFile(WiringPath, out var wiring)
            || !ValidWiring(wiring.Text))
        {
            findings.Add(new ProcessCapabilityDebtFinding(
                WiringPath,
                "process-capability audit wiring or its compiler canary is absent"));
        }

        if (!snapshot.TryGetFile(ProjectPath, out var project)
            || !HasImport(project.Text))
        {
            findings.Add(new ProcessCapabilityDebtFinding(
                ProjectPath,
                $"StrataLint.Tests must import {ImportPath}"));
        }

        if (!snapshot.TryGetFile(SharedAnalyzerPath, out var shared)
            || !shared.Text.Contains(
                "Microsoft.CodeAnalysis.BannedApiAnalyzers",
                StringComparison.Ordinal))
        {
            findings.Add(new ProcessCapabilityDebtFinding(
                SharedAnalyzerPath,
                "shared test props must provide Microsoft.CodeAnalysis.BannedApiAnalyzers"));
        }

        return findings.ToImmutable();
    }

    private static bool ValidWiring(string text)
    {
        try
        {
            var document = XDocument.Parse(text, LoadOptions.None);
            var additional = document.Descendants("AdditionalFiles").SingleOrDefault();
            var compile = document.Descendants("Compile").SingleOrDefault();
            var target = document.Descendants("Target").SingleOrDefault(element =>
                (string?)element.Attribute("Name") == "WriteProcessCapabilityAuditCanary");
            var writer = target?.Descendants("WriteLinesToFile").SingleOrDefault();
            return document.Root?.Name.LocalName == "Project"
                && (string?)additional?.Attribute("Include") == AdditionalFileInclude
                && (string?)additional?.Parent?.Attribute("Condition") ==
                    "'$(ProcessCapabilityAudit)' == 'true'"
                && (string?)compile?.Attribute("Include") == "$(ProcessCapabilityCanary)"
                && (string?)target?.Attribute("BeforeTargets") == "CoreCompile"
                && (string?)target?.Attribute("Condition") ==
                    "'$(ProcessCapabilityAudit)' == 'true'"
                && ((string?)writer?.Attribute("Lines"))?.Contains(
                    "new System.Diagnostics.Process()",
                    StringComparison.Ordinal) == true;
        }
        catch (Exception exception) when (exception is InvalidOperationException
            or System.Xml.XmlException)
        {
            return false;
        }
    }

    private static bool HasImport(string text)
    {
        try
        {
            var document = XDocument.Parse(text, LoadOptions.None);
            return document.Descendants("Import").Count(element =>
                (string?)element.Attribute("Project") == ImportPath
                && element.Attribute("Condition") is null) == 1;
        }
        catch (Exception exception) when (exception is System.Xml.XmlException)
        {
            return false;
        }
    }

    private static int BaselineMechanismParts(RepositorySnapshot snapshot) => new[]
    {
        snapshot.TryGetFile(BanPath, out _),
        snapshot.TryGetFile(WiringPath, out _),
        snapshot.TryGetFile(ProjectPath, out var project) && HasImport(project.Text),
    }.Count(static present => present);

    private static bool IsRelevantChange(RawChangeSet changes) => changes.Paths.Any(path =>
        path.Value.StartsWith("tools/tests/StrataLint.Tests/", StringComparison.Ordinal)
        || path.Value.StartsWith("tools/StrataLint.Engine/", StringComparison.Ordinal)
        || IsBuildBindingPath(path.Value));

    private static bool BindingInputsChanged(
        RepositorySnapshot current,
        RepositorySnapshot baseline) => current.Files.Keys
        .Concat(baseline.Files.Keys)
        .Select(static path => path.Value)
        .Where(IsBuildBindingPath)
        .Distinct(StringComparer.Ordinal)
        .Any(path => !ByteIdentical(current, baseline, path));

    private static bool IsBuildBindingPath(string path) =>
        CompilerBindingPaths.Contains(path)
        || path.StartsWith("tools/tests/StrataLint.Tests/", StringComparison.Ordinal)
        && (path.EndsWith("/.editorconfig", StringComparison.Ordinal)
            || path.EndsWith("/Directory.Build.props", StringComparison.Ordinal)
            || path.EndsWith("/Directory.Build.targets", StringComparison.Ordinal)
            || path.EndsWith(".ruleset", StringComparison.Ordinal));

    private static bool ByteIdentical(
        RepositorySnapshot current,
        RepositorySnapshot baseline,
        string path) => current.TryGetFile(path, out var currentFile)
        && baseline.TryGetFile(path, out var baselineFile)
        && currentFile.RawBytes.AsSpan().SequenceEqual(baselineFile.RawBytes.AsSpan());
}

internal static partial class ProcessCapabilityCompileOracle
{
    private const int MaximumOutputBytes = 32 * 1024 * 1024;
    private const string CanaryFileName = "ProcessCapabilityAuditCanary.cs";
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);
    private static readonly Regex DiagnosticPattern = new(
        "^(?<path>.+)\\((?<line>[0-9]+),(?<column>[0-9]+)\\): "
            + "(?:warning|error) RS0030: (?<message>.*?)(?: \\[[^\\]]+\\])?$",
        RegexOptions.CultureInvariant | RegexOptions.Multiline);

    internal static ProcessCapabilityAudit Inspect(
        RepositorySnapshot snapshot,
        RepositorySnapshot? bootstrap)
    {
        try
        {
            using var checkout = MsBuildCompileOracle.Materialize(snapshot);
            if (bootstrap is not null)
            {
                AddBootstrapMechanism(checkout.Root, bootstrap);
            }

            var result = BoundedProcessRunner.Run(
                ResolveDotnetExecutable(),
                BuildArguments(),
                checkout.Root,
                BoundedProcessRunner.HangDetectionBudget,
                MaximumOutputBytes);
            var output = StrictUtf8.GetString(result.StandardOutput)
                + "\n" + StrictUtf8.GetString(result.StandardError);
            var diagnostics = ParseDiagnostics(output, checkout.Root);
            var canaries = diagnostics
                .Where(static item => Path.GetFileName(item.Path) == CanaryFileName)
                .GroupBy(static item => item.Identity, StringComparer.Ordinal)
                .Select(static group => group.First())
                .ToArray();
            var failures = ImmutableArray.CreateBuilder<string>();
            if (result.ExitCode != 0)
            {
                failures.Add($"process-capability audit build exited {result.ExitCode}: "
                    + FirstError(output));
            }

            if (canaries.Length != 1)
            {
                failures.Add($"process-capability RS0030 canary expected 1 diagnostic, got "
                    + canaries.Length);
            }

            return new ProcessCapabilityAudit(
                diagnostics
                    .Where(static item => Path.GetFileName(item.Path) != CanaryFileName)
                    .GroupBy(static item => item.Identity, StringComparer.Ordinal)
                    .Select(static group => group.First())
                    .OrderBy(static item => item.Identity, StringComparer.Ordinal)
                    .ToImmutableArray(),
                failures.ToImmutable());
        }
        catch (Exception exception) when (exception is IOException
            or UnauthorizedAccessException
            or InvalidOperationException
            or TimeoutException
            or Win32Exception
            or DecoderFallbackException)
        {
            return new ProcessCapabilityAudit(
                [],
                [$"process-capability compiler audit failed closed: {exception.Message}"]);
        }
    }

    internal static ImmutableArray<ProcessCapabilityDiagnostic> ParseDiagnostics(
        string output,
        string repositoryRoot) => DiagnosticPattern.Matches(output)
        .Select(match => new ProcessCapabilityDiagnostic(
            NormalizePath(match.Groups["path"].Value, repositoryRoot),
            int.Parse(match.Groups["line"].Value, System.Globalization.CultureInfo.InvariantCulture),
            int.Parse(match.Groups["column"].Value, System.Globalization.CultureInfo.InvariantCulture),
            SymbolFrom(match.Groups["message"].Value),
            match.Groups["message"].Value.Trim()))
        .ToImmutableArray();

    private static void AddBootstrapMechanism(string root, RepositorySnapshot bootstrap)
    {
        WriteSnapshotFile(root, bootstrap, ProcessCapabilityDebtPolicy.BanPath);
        WriteSnapshotFile(root, bootstrap, ProcessCapabilityDebtPolicy.WiringPath);
        var projectPath = Path.Combine(
            root,
            ProcessCapabilityDebtPolicy.ProjectPath.Replace('/', Path.DirectorySeparatorChar));
        var document = XDocument.Load(projectPath, LoadOptions.None);
        document.Root!.Add(new XElement("Import", new XAttribute("Project", "ProcessCapability.props")));
        document.Save(projectPath, SaveOptions.DisableFormatting);
    }

    private static void WriteSnapshotFile(
        string root,
        RepositorySnapshot source,
        string path)
    {
        if (!source.TryGetFile(path, out var file))
        {
            throw new InvalidOperationException($"bootstrap mechanism is missing {path}");
        }

        var fullPath = Path.Combine(root, path.Replace('/', Path.DirectorySeparatorChar));
        Directory.CreateDirectory(Path.GetDirectoryName(fullPath)!);
        File.WriteAllBytes(fullPath, file.RawBytes.AsSpan().ToArray());
    }

    private static IReadOnlyList<string> BuildArguments() =>
    [
        "build",
        ProcessCapabilityDebtPolicy.ProjectPath,
        "--configuration", "Release",
        "--nologo",
        "--verbosity", "minimal",
        "-p:ProcessCapabilityAudit=true",
        "-p:TreatWarningsAsErrors=false",
        "-p:WarningsAsErrors=",
        "-p:RestoreLockedMode=true",
        "-p:UseSharedCompilation=false",
    ];

    private static string NormalizePath(string path, string repositoryRoot)
    {
        var trimmed = path.Trim();
        var relative = Path.IsPathFullyQualified(trimmed)
            ? Path.GetRelativePath(
                MsBuildCompileOracle.CanonicalizePath(repositoryRoot),
                MsBuildCompileOracle.CanonicalizePath(trimmed))
            : trimmed;
        return relative.Replace(Path.DirectorySeparatorChar, '/');
    }

    private static string SymbolFrom(string message)
    {
        var first = message.IndexOf('\'', StringComparison.Ordinal);
        var second = first < 0 ? -1 : message.IndexOf('\'', first + 1);
        return first >= 0 && second > first ? message[(first + 1)..second] : message.Trim();
    }

    private static string FirstError(string output) => output
        .Split(['\r', '\n'], StringSplitOptions.RemoveEmptyEntries)
        .FirstOrDefault(static line => line.Contains(": error ", StringComparison.Ordinal))
        ?.Trim() ?? "no compiler error line was emitted";

    private static string ResolveDotnetExecutable()
    {
        if (Environment.GetEnvironmentVariable("DOTNET_HOST_PATH") is { Length: > 0 } host
            && File.Exists(host))
        {
            return host;
        }

        if (Environment.GetEnvironmentVariable("DOTNET_ROOT") is { Length: > 0 } root
            && File.Exists(Path.Combine(root, "dotnet")))
        {
            return Path.Combine(root, "dotnet");
        }

        var userInstall = Path.Combine(
            Environment.GetFolderPath(Environment.SpecialFolder.UserProfile),
            ".dotnet",
            "dotnet");
        return File.Exists(userInstall) ? userInstall : "dotnet";
    }
}

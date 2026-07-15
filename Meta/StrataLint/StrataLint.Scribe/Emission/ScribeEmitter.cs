using StrataLint.Engine;

namespace StrataLint.Scribe;

public static class ScribeEmitter
{
    private sealed record ScribeEmissionRun(
        int ExitCode,
        VerifiedScribeEmissions? Verification);

    internal static string AttestationRelativePath => ScribeEmissionAttestation.RelativePath;

    public static int Emit(
        string repositoryRoot,
        bool check,
        TextWriter output,
        TextWriter error)
        => Run(
            repositoryRoot,
            check,
            output,
            error,
            LeanCompiledArtifactReports.InspectRepository,
            validateRepository: true).ExitCode;

    internal static int Emit(
        string repositoryRoot,
        bool check,
        TextWriter output,
        TextWriter error,
        LeanAxiomReport leanReport)
    {
        ArgumentNullException.ThrowIfNull(leanReport);
        return Run(
            repositoryRoot,
            check,
            output,
            error,
            _ => leanReport,
            validateRepository: false).ExitCode;
    }

    internal static int Emit(
        string repositoryRoot,
        bool check,
        TextWriter output,
        TextWriter error,
        LeanAxiomReport leanReport,
        bool validateRepository)
    {
        ArgumentNullException.ThrowIfNull(leanReport);
        return Run(
            repositoryRoot,
            check,
            output,
            error,
            _ => leanReport,
            validateRepository).ExitCode;
    }

    internal static VerifiedScribeEmissions? Verify(
        string repositoryRoot,
        TextWriter error,
        LeanAxiomReport leanReport)
    {
        ArgumentNullException.ThrowIfNull(leanReport);
        return Run(
            repositoryRoot,
            check: true,
            TextWriter.Null,
            error,
            _ => leanReport,
            validateRepository: true).Verification;
    }

    private static ScribeEmissionRun Run(
        string repositoryRoot,
        bool check,
        TextWriter output,
        TextWriter error,
        Func<string, LeanAxiomReport> loadLeanReport,
        bool validateRepository)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(output);
        ArgumentNullException.ThrowIfNull(error);
        ArgumentNullException.ThrowIfNull(loadLeanReport);

        try
        {
            var leanReport = loadLeanReport(repositoryRoot);
            if (validateRepository)
            {
                var findings = DescribeRepositoryValidator.Validate(
                    repositoryRoot,
                    DocumentDefinitions.All.Select(static definition => definition.Document),
                    leanReport);
                if (!findings.IsEmpty)
                {
                    foreach (var finding in findings)
                    {
                        error.WriteLine(
                            $"describe red code={finding.Code} path={finding.Path} message={finding.Message}");
                    }

                    return new ScribeEmissionRun(1, null);
                }
            }

            return EmitVerified(repositoryRoot, check, output, error, leanReport);
        }
        catch (Exception exception) when (
            exception is InvalidOperationException
                or FormatException
                or IOException
                or UnauthorizedAccessException
                or ArgumentException)
        {
            error.WriteLine($"emit failed: {exception.Message}");
            return new ScribeEmissionRun(1, null);
        }
    }

    private static ScribeEmissionRun EmitVerified(
        string repositoryRoot,
        bool check,
        TextWriter output,
        TextWriter error,
        LeanAxiomReport leanReport)
    {
        var rendered = new List<(DocumentDefinition Definition, byte[] Bytes)>();
        var attestations = new List<ScribeEmissionRecord>();
        foreach (var definition in DocumentDefinitions.All)
        {
            var first = CanonicalMarkdownWriter.Write(definition.Document, leanReport).ToArray();
            var second = CanonicalMarkdownWriter.Write(definition.Document, leanReport).ToArray();
            if (!first.AsSpan().SequenceEqual(second))
            {
                throw new InvalidOperationException(
                    $"Scribe rendering is not deterministic for {definition.Document.Header.Gid.Value}.");
            }

            rendered.Add((definition, first));
            var gid = definition.Document.Header.Gid.Value;
            var definitionPath = ScribeEmissionAttestation.DefinitionPath(gid);
            var source = File.ReadAllBytes(Path.Combine(repositoryRoot, definitionPath));
            attestations.Add(new ScribeEmissionRecord(
                gid,
                definitionPath,
                DigestionFingerprint.Compute(source).RawSha256,
                definition.RelativePath.Value,
                DigestionFingerprint.Compute(first).RawSha256));
        }

        var attestationBytes = ScribeEmissionAttestation.Write(attestations).ToArray();

        var differences = 0;
        var writes = 0;
        foreach (var (definition, expected) in rendered)
        {
            var path = Path.Combine(repositoryRoot, definition.RelativePath.Value);
            var current = File.Exists(path) ? File.ReadAllBytes(path) : [];
            if (current.AsSpan().SequenceEqual(expected))
            {
                continue;
            }

            if (check)
            {
                differences++;
                error.WriteLine($"out of date: {definition.RelativePath.Value}");
                continue;
            }

            var parent = Path.GetDirectoryName(path)
                ?? throw new InvalidOperationException("Blueprint path has no parent directory.");
            Directory.CreateDirectory(parent);
            File.WriteAllBytes(path, expected);
            writes++;
            output.WriteLine($"wrote: {definition.RelativePath.Value}");
        }

        var attestationPath = Path.Combine(repositoryRoot, ScribeEmissionAttestation.RelativePath);
        var currentAttestation = File.Exists(attestationPath)
            ? File.ReadAllBytes(attestationPath)
            : [];
        if (!currentAttestation.AsSpan().SequenceEqual(attestationBytes))
        {
            if (check)
            {
                differences++;
                error.WriteLine($"out of date: {ScribeEmissionAttestation.RelativePath}");
            }
            else
            {
                var parent = Path.GetDirectoryName(attestationPath)
                    ?? throw new InvalidOperationException("Scribe attestation path has no parent directory.");
                Directory.CreateDirectory(parent);
                File.WriteAllBytes(attestationPath, attestationBytes);
                output.WriteLine($"wrote: {ScribeEmissionAttestation.RelativePath}");
            }
        }

        if (check && differences == 0)
        {
            output.WriteLine($"checked: {DocumentDefinitions.All.Length} blueprint(s)");
            output.WriteLine($"checked: {ScribeEmissionAttestation.RelativePath}");
        }
        else if (!check)
        {
            output.WriteLine($"emitted: {writes} changed blueprint(s)");
        }

        return new ScribeEmissionRun(
            differences == 0 ? 0 : 1,
            check && differences == 0
                ? VerifiedScribeEmissions.Create(attestations)
                : null);
    }
}

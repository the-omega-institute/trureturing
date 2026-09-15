using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed class UpstreamSettlementException(string code, string detail) : Exception(detail)
{
    internal string Code { get; } = code;
}

internal interface IUpstreamLeanProcessRunner
{
    ProcessOutput Run(string executable, IReadOnlyList<string> arguments, string root, TimeSpan budget);
}

internal sealed class UpstreamLeanProcessRunner : IUpstreamLeanProcessRunner
{
    public ProcessOutput Run(string executable, IReadOnlyList<string> arguments, string root, TimeSpan budget) =>
        BoundedProcessRunner.Run(executable, arguments, root, budget, 4 * 1024 * 1024);
}

internal sealed class UpstreamProbeVerifier(IUpstreamLeanProcessRunner runner, string executable, TimeSpan budget)
{
    // Infrastructure hang guard, never a mathematical verdict. Tests inject the pinned value and a runner.
    internal static readonly TimeSpan HangGuardBudget = TimeSpan.FromMinutes(5);
    private const string Name = @"[\p{L}_][\p{L}\p{N}_'′!?]*(?:\.[\p{L}_][\p{L}\p{N}_'′!?]*)*";
    private const RegexOptions Options = RegexOptions.CultureInvariant | RegexOptions.Multiline;
    private static readonly Regex Forbidden = new(@"\b(?:sorry|sorryAx|native_decide)\b|\baxiom\s", Options);

    internal static UpstreamProbeVerifier Production()
    {
        if (!LeanLakeExecutable.TryResolve(out var lake, out var reason)) throw new InvalidOperationException(reason);
        return new(new UpstreamLeanProcessRunner(), lake, HangGuardBudget);
    }

    internal ImmutableArray<string> Verify(string root, byte[] source, string manifest, ImmutableArray<string> declarations)
    {
        var text = new UTF8Encoding(false, true).GetString(source);
        var code = WithoutComments(text);
        var imports = Regex.Matches(code, @"^[ \t]*import[ \t]+([^\r\n]+)", Options)
            .Select(match => match.Groups[1].Value.Trim()).ToArray();
        // Any import outside the recognized single-line dialect remains unverified.
        // In particular, public/meta or line-broken imports must not evade the D5 guard.
        if (Regex.Matches(code, @"\bimport\b", Options).Count != imports.Length)
            throw Invalid("PROBE_IMPORTS_PROJECT", "use canonical single-line import commands");
        var modules = imports.SelectMany(line => line.Split((char[]?)null, StringSplitOptions.RemoveEmptyEntries)).ToArray();
        if (modules.Length == 0 || modules.Any(module => module == "D5" || module.StartsWith("D5.", StringComparison.Ordinal)))
            throw Invalid("PROBE_IMPORTS_PROJECT", "probe must import pinned upstream modules and cannot import D5");
        using (var document = JsonDocument.Parse(manifest))
        {
            var packages = document.RootElement.GetProperty("packages").EnumerateArray()
                .Select(package => package.GetProperty("name").GetString()!).ToArray();
            foreach (var module in modules)
            {
                if (!Regex.IsMatch(module, "^" + Name + @"\z", Options)
                    || !packages.Any(package => IsPackageName(package)
                        && File.Exists(Path.Combine(root, ".lake", "packages", package, module.Replace('.', '/') + ".lean"))))
                    throw Invalid("PROBE_IMPORTS_PROJECT", $"import outside pinned manifest closure: {module}");
            }
        }
        if (Forbidden.IsMatch(text)) throw Invalid("PROBE_FAILED", "probe source contains a forbidden proof command");
        var scratch = Path.Combine(root, ".lake");
        // Reject scratch aliases as well as input aliases: Lean must execute within this worktree.
        RequireNoLinks(root, scratch);
        Directory.CreateDirectory(scratch);
        var probePath = Path.Combine(scratch, $"upstream-probe-{Guid.NewGuid():N}.lean");
        var checkPath = Path.Combine(scratch, $"upstream-check-{Guid.NewGuid():N}.lean");
        try
        {
            File.WriteAllBytes(probePath, source);
            var compiled = runner.Run(executable, ["env", "lean", probePath], root, budget);
            var stdout = Encoding.UTF8.GetString(compiled.StandardOutput);
            var diagnostics = stdout + Encoding.UTF8.GetString(compiled.StandardError);
            if (compiled.ExitCode != 0 || Forbidden.IsMatch(diagnostics))
                throw Invalid("PROBE_FAILED", $"exit={compiled.ExitCode}\n{diagnostics}");
            var axioms = ParseAxioms(code, stdout);
            var checkSource = string.Join('\n', imports.Select(line => "import " + line)) + "\n"
                + string.Concat(declarations.Select(name => "#check @" + name + "\n"));
            File.WriteAllText(checkPath, checkSource, new UTF8Encoding(false));
            var checkedNames = runner.Run(executable, ["env", "lean", checkPath], root, budget);
            var checkDiagnostics = Encoding.UTF8.GetString(checkedNames.StandardOutput)
                + Encoding.UTF8.GetString(checkedNames.StandardError);
            if (checkedNames.ExitCode != 0 || Regex.IsMatch(checkDiagnostics, @"\berror:", Options))
            {
                var unresolved = declarations.Where(name => checkDiagnostics.Contains(name, StringComparison.Ordinal)).ToArray();
                // Lean reports source positions even when an elaboration error does not echo the name.
                var errorLines = Regex.Matches(checkDiagnostics, @":([0-9]+):[0-9]+: error:", Options)
                    .Select(match => int.Parse(match.Groups[1].Value, System.Globalization.CultureInfo.InvariantCulture) - imports.Length - 1)
                    .Where(index => index >= 0 && index < declarations.Length).Select(index => declarations[index]);
                var failures = unresolved.Concat(errorLines).ToHashSet(StringComparer.Ordinal);
                var ordered = declarations.Where(failures.Contains).ToArray();
                if (ordered.Length == 0) ordered = declarations.ToArray();
                throw Invalid("DECLARATION_UNRESOLVED", $"{ordered[0]} unresolved=[{string.Join(',', ordered)}] exit={checkedNames.ExitCode}\n{checkDiagnostics}");
            }
            return axioms;
        }
        finally
        {
            File.Delete(checkPath);
            File.Delete(probePath);
        }
    }

    private static ImmutableArray<string> ParseAxioms(string code, string stdout)
    {
        // The bounded probe dialect uses top-level, named theorems (qualified names are allowed).
        // Namespace/section state, lemma aliases and anonymous examples are deliberately unverified.
        var theorems = Regex.Matches(code, @"^[ \t]*theorem[ \t]+(" + Name + @")(?=[ \t\r\n:({])", Options)
            .Select(match => match.Groups[1].Value).ToArray();
        var prints = Regex.Matches(code, @"^[ \t]*#print[ \t]+axioms[ \t]+(" + Name + @")[ \t]*\r?$", Options);
        if (theorems.Length == 0 || Regex.Matches(code, @"\btheorem\b", Options).Count != theorems.Length
            || theorems.Distinct(StringComparer.Ordinal).Count() != theorems.Length
            || Regex.IsMatch(code, @"\b(?:example|lemma|namespace|section)\b", Options)
            || !theorems.Order(StringComparer.Ordinal).SequenceEqual(prints.Select(match => match.Groups[1].Value).Order(StringComparer.Ordinal))
            || prints.Count == 0
            || !Regex.IsMatch(code[prints[0].Index..], @"\A(?:[ \t\r\n]*#print[ \t]+axioms[ \t]+" + Name + @"[ \t]*(?:\r?\n|\z))+\s*\z", Options))
            throw Invalid("PROBE_AXIOMS", "use named top-level theorems followed by exactly one #print axioms per theorem");
        var parsed = new HashSet<string>(StringComparer.Ordinal);
        var union = new SortedSet<string>(StringComparer.Ordinal);
        foreach (Match match in Regex.Matches(stdout,
                     @"^'(?<name>[^\r\n]+)' (?:depends on axioms: \[(?<axioms>[^\]\r\n]*)\]|does not depend on any axioms)[ \t]*\r?$", Options))
        {
            if (!theorems.Contains(match.Groups["name"].Value, StringComparer.Ordinal)) continue;
            if (!parsed.Add(match.Groups["name"].Value)) throw Invalid("PROBE_AXIOMS", "duplicate axiom output");
            foreach (var axiom in match.Groups["axioms"].Value.Split(',', StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries))
            {
                if (!DigestionUpstream.IsAllowedAxiom(axiom)) throw Invalid("PROBE_AXIOMS", $"unlicensed axiom: {axiom}");
                union.Add(axiom);
            }
        }
        if (theorems.Any(name => !parsed.Contains(name))) throw Invalid("PROBE_AXIOMS", "theorem lacks parsed axiom output");
        return [.. union];
    }

    private static bool IsPackageName(string name) => name.Length > 0 && name.All(c => char.IsAsciiLetterOrDigit(c) || c is '_' or '-');

    internal static void RequireNoLinks(string root, string path)
    {
        var relative = Path.GetRelativePath(root, path);
        var cursor = Path.GetFullPath(root);
        foreach (var part in relative.Split(Path.DirectorySeparatorChar))
        {
            cursor = Path.Combine(cursor, part);
            if (new FileInfo(cursor).LinkTarget is not null || new DirectoryInfo(cursor).LinkTarget is not null)
                throw Invalid("PROBE_PATH_INVALID", "probe and scratch paths cannot traverse symbolic links");
        }
    }

    private static string WithoutComments(string source)
    {
        var chars = source.ToCharArray();
        var depth = 0;
        var line = false;
        for (var i = 0; i < chars.Length; i++)
        {
            if (depth == 0 && !line && i + 1 < chars.Length && chars[i] == '-' && chars[i + 1] == '-') line = true;
            if (!line && i + 1 < chars.Length && chars[i] == '/' && chars[i + 1] == '-')
            { depth++; chars[i++] = ' '; chars[i] = ' '; continue; }
            if (!line && depth > 0 && i + 1 < chars.Length && chars[i] == '-' && chars[i + 1] == '/')
            { depth--; chars[i++] = ' '; chars[i] = ' '; continue; }
            if (chars[i] == '\n') line = false;
            else if (line || depth > 0) chars[i] = ' ';
        }
        return new string(chars);
    }

    private static UpstreamSettlementException Invalid(string code, string detail) => new(code, detail);
}

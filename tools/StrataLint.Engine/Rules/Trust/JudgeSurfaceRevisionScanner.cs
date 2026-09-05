using System.Collections.Immutable;
using System.Text.RegularExpressions;
using YamlDotNet.Core;
using YamlDotNet.RepresentationModel;

namespace StrataLint.Engine;

internal static partial class JudgeSurfaceRevisionScanner
{
    private const string Head = "HEAD";

    // A parseable YAML tree can still be arbitrarily deep; the walk stops here, fail-closed.
    private const int MaximumYamlDepth = 64;

    private const string Suffix =
        " (SL-030, CLAUDE.md rule 19: base data enters the candidate judge through its snapshot reader)";

    // `github.base_ref`, `github.event.pull_request.base.sha` and the bracket spelling
    // `pull_request['base']['sha']` of the same expression (review round 15).
    private static readonly Regex BaseRefIndicator = new(
        @"base_ref|pull_request(\.base\b|\s*\[\s*[""']base[""']\s*\])",
        RegexOptions.CultureInvariant | RegexOptions.Compiled);

    // Git's own global options (`git [global options] <verb> …`). Options that take a value may
    // carry it as the next word, glued (`-Cdir`) or after `=`; any option outside these two tables
    // fails closed because an unknown option may consume the verb or shift it.
    private static readonly HashSet<string> GlobalOptionsWithValue = new(StringComparer.Ordinal)
    {
        "-C", "-c", "--git-dir", "--work-tree", "--namespace", "--exec-path", "--super-prefix",
        "--config-env", "--attr-source", "--list-cmds",
    };

    private static readonly HashSet<string> GlobalFlags = new(StringComparer.Ordinal)
    {
        "--no-pager", "-p", "--paginate", "-P", "--bare", "--no-replace-objects", "--no-lazy-fetch",
        "--no-optional-locks", "--no-advice", "--literal-pathspecs", "--glob-pathspecs",
        "--noglob-pathspecs", "--icase-pathspecs", "--html-path", "--man-path", "--info-path",
        "--version", "--help",
    };

    private static readonly HashSet<string> Verbs = new(StringComparer.Ordinal)
    {
        "show", "cat-file", "archive", "worktree", "checkout", "checkout-index", "restore", "read-tree",
    };

    internal static bool IsJudgeSurfacePath(string path) =>
        path.StartsWith(".github/", StringComparison.Ordinal)
        || path.StartsWith("tools/scripts/workflow/", StringComparison.Ordinal);

    internal static ImmutableArray<string> Scan(string path, string text)
    {
        var messages = ImmutableArray.CreateBuilder<string>();
        // Any YAML under `.github/**` (workflows and composite actions alike) is read by the same
        // parser family the Actions runner uses; every `run:` scalar is shell and every `ref:`
        // scalar is a checkout input, wherever the YAML structure puts them (review rounds 5–11:
        // a line-oriented reading of YAML missed folding, tags, flow mappings and multi-line
        // scalars one form per round). Everything else on the judge surface is shell, line by line.
        if (path.StartsWith(".github/", StringComparison.Ordinal)
            && (path.EndsWith(".yml", StringComparison.Ordinal) || path.EndsWith(".yaml", StringComparison.Ordinal)))
        {
            ScanYaml(text, messages);
            return messages.ToImmutable();
        }

        messages.AddRange(JudgeShell(1, text));
        return messages.ToImmutable();
    }

    private static void ScanYaml(string text, ImmutableArray<string>.Builder messages)
    {
        var stream = new YamlStream();
        try
        {
            stream.Load(new StringReader(text));
        }
        catch (Exception exception) when (exception is YamlException or ArgumentException or InvalidOperationException)
        {
            // YAML the runner would not accept either: judged as it stands, never skipped.
            var line = exception is YamlException yaml ? yaml.Start.Line : 1;
            messages.Add($"line {line}: YAML on the judge surface does not parse ({exception.Message.Trim()}) — fail-closed" + Suffix);
            return;
        }

        var visited = new HashSet<YamlNode>(ReferenceEqualityComparer.Instance);
        foreach (var document in stream.Documents)
        {
            if (document.RootNode is not null)
            {
                WalkYaml(document.RootNode, messages, visited, 0);
            }
        }
    }

    private static void WalkYaml(YamlNode node, ImmutableArray<string>.Builder messages, HashSet<YamlNode> visited, int depth)
    {
        if (depth > MaximumYamlDepth)
        {
            messages.Add($"line {node.Start.Line}: YAML nesting deeper than {MaximumYamlDepth} levels is fail-closed" + Suffix);
            return;
        }

        // Aliases resolve to the anchored node itself; visiting it once is enough and keeps a
        // self-referential document finite.
        if (!visited.Add(node))
        {
            return;
        }

        switch (node)
        {
            case YamlMappingNode mapping:
                foreach (var (key, value) in mapping.Children)
                {
                    if (key is YamlScalarNode { Value: "run" })
                    {
                        if (value is YamlScalarNode run)
                        {
                            // A block scalar's content starts on the line after its `|` / `>`
                            // indicator; a flow scalar starts on the key's line.
                            var firstLine = (int)run.Start.Line + (run.Style is ScalarStyle.Literal or ScalarStyle.Folded ? 1 : 0);
                            messages.AddRange(JudgeShell(firstLine, run.Value ?? string.Empty));
                        }
                        else
                        {
                            messages.Add($"line {value.Start.Line}: a `run:` whose value is not a scalar is fail-closed" + Suffix);
                        }

                        continue;
                    }

                    if (key is YamlScalarNode { Value: "ref" } && value is YamlScalarNode reference)
                    {
                        // Deliberately over-match: any `ref:` naming the protected base, whether or
                        // not it sits under `actions/checkout`; a visible Block beats a silent miss.
                        if (BaseRefIndicator.IsMatch(reference.Value ?? string.Empty))
                        {
                            messages.Add(
                                $"line {reference.Start.Line}: a `ref:` naming the protected base "
                                + $"'{reference.Value}' is not allowed on the judge surface" + Suffix);
                        }

                        continue;
                    }

                    WalkYaml(key, messages, visited, depth + 1);
                    WalkYaml(value, messages, visited, depth + 1);
                }

                break;
            case YamlSequenceNode sequence:
                foreach (var child in sequence.Children)
                {
                    WalkYaml(child, messages, visited, depth + 1);
                }

                break;
        }
    }

    // `firstLine` is where the text starts in its file (1 for a script, the scalar's start line for
    // YAML); every command carries its own line within the text, so the diagnostic points at it.
    private static IEnumerable<string> JudgeShell(int firstLine, string shell)
    {
        var lexed = JudgeSurfaceShellLexer.Commands(shell.ReplaceLineEndings("\n"));
        if (lexed.Truncated)
        {
            yield return $"line {firstLine}: shell nesting deeper than {JudgeSurfaceShellLexer.MaximumDepth} levels is fail-closed" + Suffix;
        }

        foreach (var command in lexed.Commands)
        {
            var reason = JudgeCommand(command.Words, out var verb);
            if (reason is not null)
            {
                yield return $"line {firstLine + command.Line - 1}: git {verb} {reason}; only HEAD may be materialized on the judge surface" + Suffix;
            }
        }
    }

    private static string? JudgeCommand(ImmutableArray<string> words, out string verb)
    {
        verb = string.Empty;
        // `X=1 git …`, `! git …`: assignment prefixes and negation do not change what runs.
        var first = 0;
        while (first < words.Length)
        {
            var word = words[first];
            if (word == "!" || IsAssignmentWord(word))
            {
                first++;
                continue;
            }

            if (word == "time")
            {
                // `time [-p] [--] cmd` (review round 8: `time -p git show …`).
                first++;
                while (first < words.Length && words[first].StartsWith('-'))
                {
                    first++;
                }

                continue;
            }

            if (word == "coproc")
            {
                // `coproc [NAME] cmd`: an optional coprocess name precedes the command.
                first++;
                if (first + 1 < words.Length && !IsGit(words[first]) && !words[first].StartsWith('-'))
                {
                    first++;
                }

                continue;
            }

            if (CommandPrefixKeywords.Contains(word))
            {
                first++;
                continue;
            }

            break;
        }

        if (first >= words.Length)
        {
            return null;
        }

        // A dynamic command word (`$GIT`, `"$(command -v git)"`) is judged as git when a managed
        // verb follows it; followed by anything else it is out of class (`${X}` expansions are
        // declared unsupported). Measured on the real judge surface before choosing this: the
        // dynamic command words there (`"$HOME/.elan/bin/lake" --version`, …) are never followed
        // by a managed verb, so no real line is misjudged (review round 14).
        var dynamicCommand = !IsGit(words[first]) && words[first].Contains('$');
        if (!IsGit(words[first]) && !dynamicCommand)
        {
            return null;
        }

        var index = first + 1;
        while (index < words.Length && words[index].StartsWith('-'))
        {
            var option = words[index];
            if (GlobalFlags.Contains(option))
            {
                index++;
                continue;
            }

            if (GlobalOptionsWithValue.Contains(option))
            {
                index += 2;
                continue;
            }

            var separator = option.IndexOf('=', StringComparison.Ordinal);
            var name = separator > 0 ? option[..separator] : option;
            if (GlobalOptionsWithValue.Contains(name)
                || (option.Length > 2 && GlobalOptionsWithValue.Contains(option[..2])))
            {
                index++;
                continue;
            }

            if (dynamicCommand)
            {
                // `"$gate" --candidate …`, `[[ "$rc" -ne 0 ]]`: a dynamic command word followed by
                // something that is not git's option grammar is not git (review round 15: this
                // branch fired 13 times on the real judge surface before the verb was even looked
                // for).
                return null;
            }

            verb = "(global options)";
            return $"option '{option}' is not in the closed global option table (fail-closed)";
        }

        if (index >= words.Length)
        {
            return null;
        }

        if (!dynamicCommand && words[index].Contains('$'))
        {
            // `git $(printf show) HEAD^1:p`: the verb itself is dynamic (review round 14).
            verb = words[index];
            return "verb of unknown provenance (fail-closed)";
        }

        if (!Verbs.Contains(words[index]))
        {
            return null;
        }

        verb = words[index];
        return JudgeVerb(verb, words[(index + 1)..].ToArray());
    }

    // Shell control keywords that prefix a simple command without changing what runs
    // (review round 7: `if git show HEAD^1:… >/dev/null; then :; fi`).
    private static readonly HashSet<string> CommandPrefixKeywords = new(StringComparer.Ordinal)
    {
        "if", "then", "elif", "else", "while", "until", "do",
    };

    private static bool IsGit(string word) =>
        word == "git" || word.EndsWith("/git", StringComparison.Ordinal);

    private static bool IsAssignmentWord(string word)
    {
        var equals = word.IndexOf('=', StringComparison.Ordinal);
        if (equals <= 0)
        {
            return false;
        }

        for (var index = 0; index < equals; index++)
        {
            var character = word[index];
            if (!(char.IsAsciiLetterOrDigit(character) || character == '_') || (index == 0 && char.IsAsciiDigit(character)))
            {
                return false;
            }
        }

        return true;
    }
}

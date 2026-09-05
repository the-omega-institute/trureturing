using System.Collections.Immutable;
using System.Text.RegularExpressions;

namespace StrataLint.Engine;

internal static partial class JudgeSurfaceRevisionScanner
{
    private const string Head = "HEAD";

    private static readonly Regex WorkflowRef = new(
        @"[""']?\bref[""']?:\s*(?<value>[^,}\n]+)",
        RegexOptions.CultureInvariant | RegexOptions.Compiled);

    private static readonly Regex BaseRefIndicator = new(
        @"base_ref|pull_request\.base\b",
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
        // Any YAML under `.github/**` (workflows and composite actions alike) can carry `run:`
        // scalars and `ref:` inputs (review round 6: `.github/actions/*/action.yml`).
        var isWorkflow = path.StartsWith(".github/", StringComparison.Ordinal)
            && (path.EndsWith(".yml", StringComparison.Ordinal)
                || path.EndsWith(".yaml", StringComparison.Ordinal));
        (int Line, int Indent, string Text)? foldedBlock = null;
        foreach (var (lineNumber, line) in LogicalLines(text))
        {
            var index = lineNumber - 1;
            if (isWorkflow && foldedBlock is not null)
            {
                // Inside a folded `run: >` block the more-indented lines are one folded scalar: a
                // git command split across them is one command (review round 7).
                if (line.Length > foldedBlock.Value.Indent
                    && string.IsNullOrWhiteSpace(line[..(foldedBlock.Value.Indent + 1)]))
                {
                    foldedBlock = foldedBlock.Value with { Text = foldedBlock.Value.Text + " " + line.Trim() };
                    continue;
                }

                messages.AddRange(JudgeShell(foldedBlock.Value.Line, foldedBlock.Value.Text));
                foldedBlock = null;
            }

            if (isWorkflow && IsFoldedBlockStart(line, out var indent))
            {
                foldedBlock = (index + 1, indent, string.Empty);
                continue;
            }

            if (isWorkflow && !line.TrimStart().StartsWith('#'))
            {
                // Deliberately over-match: this line scanner cannot see YAML structure; a visible Block beats a silent miss.
                var reference = WorkflowRef.Match(line);
                if (reference.Success && BaseRefIndicator.IsMatch(reference.Groups["value"].Value))
                {
                    messages.Add(
                        $"line {index + 1}: a `ref:` naming the protected base "
                        + $"'{reference.Groups["value"].Value.Trim()}' is not allowed on the judge surface "
                        + "(SL-030, CLAUDE.md rule 19: base data enters the candidate judge through its snapshot reader)");
                }
            }

            // The lexer already dropped comments, quotes and redirections and split command
            // substitutions into commands of their own, so every git invocation on the line —
            // including one nested inside `$(…)` — is judged on its real argument vector.
            // In a workflow a single-line `run:` scalar is shell too (review round 5).
            var shell = isWorkflow ? WorkflowRunScalar(line) : line;
            messages.AddRange(JudgeShell(index + 1, shell));
        }

        if (foldedBlock is not null)
        {
            messages.AddRange(JudgeShell(foldedBlock.Value.Line, foldedBlock.Value.Text));
        }

        return messages.ToImmutable();
    }

    private static IEnumerable<string> JudgeShell(int lineNumber, string shell)
    {
        var lexed = JudgeSurfaceShellLexer.Commands(shell);
        if (lexed.Truncated)
        {
            yield return $"line {lineNumber}: shell nesting deeper than {JudgeSurfaceShellLexer.MaximumDepth} levels is fail-closed "
                + "(SL-030, CLAUDE.md rule 19: base data enters the candidate judge through its snapshot reader)";
        }

        foreach (var command in lexed.Commands)
        {
            var reason = JudgeCommand(command, out var verb);
            if (reason is not null)
            {
                yield return $"line {lineNumber}: git {verb} {reason}; only HEAD may be materialized on the judge surface "
                    + "(SL-030, CLAUDE.md rule 19: base data enters the candidate judge through its snapshot reader)";
            }
        }
    }

    private static readonly Regex FoldedBlockStart = new(
        @"^(?<indent>\s*)(?:-\s+)?[""']?run[""']?:\s*>[-+]?\s*$",
        RegexOptions.CultureInvariant | RegexOptions.Compiled);

    private static bool IsFoldedBlockStart(string line, out int indent)
    {
        var match = FoldedBlockStart.Match(line);
        indent = match.Success ? match.Groups["indent"].Value.Length : 0;
        return match.Success;
    }

    // Physical lines joined at a trailing unescaped backslash (`git \` + `show …` is one command);
    // the logical line keeps the first physical line's number for the diagnostic.
    private static IEnumerable<(int LineNumber, string Line)> LogicalLines(string text)
    {
        var lines = text.ReplaceLineEndings("\n").Split('\n');
        var index = 0;
        while (index < lines.Length)
        {
            var start = index;
            var builder = new System.Text.StringBuilder(lines[index]);
            while (EndsWithContinuation(lines[index]) && index + 1 < lines.Length)
            {
                // Bash removes the backslash-newline pair outright: `git sh\` + `ow` is `git show`.
                builder.Length -= 1;
                index++;
                builder.Append(lines[index]);
            }

            yield return (start + 1, builder.ToString());
            index++;
        }
    }

    private static bool EndsWithContinuation(string line)
    {
        var trailing = 0;
        for (var index = line.Length - 1; index >= 0 && line[index] == '\\'; index--)
        {
            trailing++;
        }

        return trailing % 2 == 1;
    }

    // The key may itself be quoted in YAML (`"run":`, `'run':`).
    private static readonly Regex RunScalar = new(
        @"^\s*(?:-\s+)?[""']?run[""']?:\s*(?<shell>.*)$",
        RegexOptions.CultureInvariant | RegexOptions.Compiled);

    // `run: <one-line shell>` (or `- run: …`) in a workflow: the scalar after `run:` is shell; a
    // block indicator (`|`, `>`) has no shell on this line and the block lines that follow are
    // plain shell already. Other YAML lines are lexed as they are (a leading `- name:` word is not
    // git and yields nothing).
    private static string WorkflowRunScalar(string line)
    {
        var match = RunScalar.Match(line);
        if (!match.Success)
        {
            return line;
        }

        var shell = match.Groups["shell"].Value.Trim();
        if (shell is "|" or "|-" or "|+" or ">" or ">-" or ">+")
        {
            return string.Empty;
        }

        // A YAML flow scalar (`run: "git …"` / `run: 'git …'`) is shell once the YAML quotes are
        // removed; whatever follows the closing quote (a YAML comment) is not part of the scalar.
        // Double-quoted escapes `\xHH` / `\uHHHH` / `\UHHHHHHHH` decode to the character (review
        // round 7: `"\x67it show …"` is `git show …`), `\n` / `\t` are whitespace, `\"` is a quote.
        // Single-quoted `''` is one quote.
        if (shell.Length >= 2 && shell[0] == '"')
        {
            var value = new System.Text.StringBuilder();
            for (var index = 1; index < shell.Length; index++)
            {
                if (shell[index] == '\\' && index + 1 < shell.Length)
                {
                    var escape = shell[index + 1];
                    var width = escape switch { 'x' => 2, 'u' => 4, 'U' => 8, _ => 0 };
                    if (width > 0
                        && index + 1 + width < shell.Length
                        && int.TryParse(shell.AsSpan(index + 2, width), System.Globalization.NumberStyles.HexNumber, null, out var code))
                    {
                        value.Append(char.ConvertFromUtf32(code));
                        index += 1 + width;
                        continue;
                    }

                    value.Append(escape is 'n' or 't' ? ' ' : escape);
                    index++;
                    continue;
                }

                if (shell[index] == '"')
                {
                    break;
                }

                value.Append(shell[index]);
            }

            return value.ToString();
        }

        if (shell.Length >= 2 && shell[0] == '\'')
        {
            var value = new System.Text.StringBuilder();
            for (var index = 1; index < shell.Length; index++)
            {
                if (shell[index] == '\'')
                {
                    if (index + 1 < shell.Length && shell[index + 1] == '\'')
                    {
                        value.Append('\'');
                        index++;
                        continue;
                    }

                    break;
                }

                value.Append(shell[index]);
            }

            return value.ToString();
        }

        return shell;
    }

    private static string? JudgeCommand(ImmutableArray<string> words, out string verb)
    {
        verb = string.Empty;
        // `X=1 git …`, `! git …`: assignment prefixes and negation do not change what runs.
        var first = 0;
        while (first < words.Length
            && (words[first] == "!" || CommandPrefixKeywords.Contains(words[first]) || IsAssignmentWord(words[first])))
        {
            first++;
        }

        if (first >= words.Length || !IsGit(words[first]))
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

            verb = "(global options)";
            return $"option '{option}' is not in the closed global option table (fail-closed)";
        }

        if (index >= words.Length || !Verbs.Contains(words[index]))
        {
            return null;
        }

        verb = words[index];
        var arguments = words[(index + 1)..].ToArray();
        return verb switch
        {
            "worktree" => WorktreeAddRevision(arguments),
            "read-tree" => ReadTreeOperands(arguments),
            "checkout-index" => "materializes index contents whose provenance is not a revision (fail-closed)",
            "restore" => RestoreSource(arguments),
            "checkout" => CheckoutRevision(arguments),
            "archive" => ArchiveRevision(arguments),
            "show" => RevisionPathOperand(arguments),
            "cat-file" => CatFileOperand(arguments),
            _ => null,
        };
    }

    // Shell control keywords that prefix a simple command without changing what runs
    // (review round 7: `if git show HEAD^1:… >/dev/null; then :; fi`).
    private static readonly HashSet<string> CommandPrefixKeywords = new(StringComparer.Ordinal)
    {
        "if", "then", "elif", "else", "while", "until", "do", "time", "coproc",
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

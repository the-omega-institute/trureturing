using System.Collections.Immutable;
using System.Text.RegularExpressions;

namespace StrataLint.Engine;

internal static partial class JudgeSurfaceRevisionScanner
{
    private const string Head = "HEAD";

    // YAML allows separation whitespace between a (quoted) key and its colon (`"ref" : …`;
    // review round 9), so every key regex accepts `\s*` before the colon.
    private static readonly Regex WorkflowRef = new(
        @"[""']?\bref[""']?\s*:\s*(?<value>[^,}\n]+)",
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
        (int Line, int Indent, int ContentIndent, bool PreviousMoreIndented, string Text)? foldedBlock = null;
        (int Line, string Text)? quotedScalar = null;
        foreach (var (lineNumber, line) in LogicalLines(text))
        {
            var index = lineNumber - 1;
            if (isWorkflow && foldedBlock is not null)
            {
                // Inside a folded `run: >` block the lines fold into one scalar (review round 7),
                // by YAML's rules: a line break folds to a space, but an empty line is a newline
                // and the breaks around a MORE-indented line are preserved — both are shell
                // command separators (review round 10: `echo ready` + `  git show HEAD^1:p`).
                if (string.IsNullOrWhiteSpace(line))
                {
                    foldedBlock = foldedBlock.Value with { Text = foldedBlock.Value.Text + "\n" };
                    continue;
                }

                if (line.Length > foldedBlock.Value.Indent
                    && string.IsNullOrWhiteSpace(line[..(foldedBlock.Value.Indent + 1)]))
                {
                    foldedBlock = FoldBlockLine(foldedBlock.Value, line);
                    continue;
                }

                messages.AddRange(JudgeShell(foldedBlock.Value.Line, foldedBlock.Value.Text));
                foldedBlock = null;
            }

            if (isWorkflow && quotedScalar is not null)
            {
                // A quoted `run:` scalar continues until its closing quote; YAML folds each line
                // break to one space (an empty line to a newline), so the git command split across
                // the lines is one command (review round 9: `run: "git show` + `  HEAD^1:p"`).
                quotedScalar = (quotedScalar.Value.Line, FoldQuotedContinuation(quotedScalar.Value.Text, line));
                if (IsClosedQuotedScalar(quotedScalar.Value.Text))
                {
                    messages.AddRange(JudgeShell(quotedScalar.Value.Line, DecodeYamlScalar(quotedScalar.Value.Text)));
                    quotedScalar = null;
                }

                continue;
            }

            if (isWorkflow && IsFoldedBlockStart(line, out var indent))
            {
                foldedBlock = (index + 1, indent, -1, false, string.Empty);
                continue;
            }

            if (isWorkflow && !line.TrimStart().StartsWith('#'))
            {
                // Deliberately over-match: this line scanner cannot see YAML structure; a visible Block beats a silent miss.
                // Every `ref:` on the line is judged (two checkout steps in one flow sequence are
                // two inputs; review round 9).
                foreach (Match reference in WorkflowRef.Matches(line))
                {
                    if (BaseRefIndicator.IsMatch(DecodeYamlScalar(reference.Groups["value"].Value.Trim())))
                    {
                        messages.Add(
                            $"line {index + 1}: a `ref:` naming the protected base "
                            + $"'{reference.Groups["value"].Value.Trim()}' is not allowed on the judge surface "
                            + "(SL-030, CLAUDE.md rule 19: base data enters the candidate judge through its snapshot reader)");
                    }
                }
            }

            // The lexer already dropped comments, quotes and redirections and split command
            // substitutions into commands of their own, so every git invocation on the line —
            // including one nested inside `$(…)` — is judged on its real argument vector.
            // In a workflow a single-line `run:` scalar is shell too (review round 5), and a flow
            // sequence may carry several steps on one line — each is judged on its own.
            if (isWorkflow && TryStartQuotedScalar(line, out var quoted))
            {
                quotedScalar = (index + 1, quoted);
                continue;
            }

            foreach (var shell in isWorkflow ? WorkflowRunScalars(line) : new[] { line })
            {
                messages.AddRange(JudgeShell(index + 1, shell));
            }
        }

        if (foldedBlock is not null)
        {
            messages.AddRange(JudgeShell(foldedBlock.Value.Line, foldedBlock.Value.Text));
        }

        if (quotedScalar is not null)
        {
            // An unterminated quoted scalar at the end of the file is judged as it stands (fail-closed).
            messages.AddRange(JudgeShell(quotedScalar.Value.Line, DecodeYamlScalar(quotedScalar.Value.Text)));
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

    // Block scalar indicators may carry an indentation digit and a chomping sign in either order
    // (`>2`, `>-2`, `|2-`; review round 8) and an explicit tag before them (`!!str >`; round 10).
    private static readonly Regex FoldedBlockStart = new(
        @"^(?<indent>\s*)(?:-\s+)?[""']?run[""']?\s*:\s*(?:!\S*[ \t]+)?>(?:[-+]?\d?|\d[-+]?)\s*(?:#.*)?$",
        RegexOptions.CultureInvariant | RegexOptions.Compiled);

    private static readonly Regex BlockIndicator = new(
        @"^[|>](?:[-+]?\d?|\d[-+]?)\s*(?:#.*)?$",
        RegexOptions.CultureInvariant | RegexOptions.Compiled);

    private static bool IsBlockIndicator(string scalar) => BlockIndicator.IsMatch(scalar);

    private static (int Line, int Indent, int ContentIndent, bool PreviousMoreIndented, string Text) FoldBlockLine(
        (int Line, int Indent, int ContentIndent, bool PreviousMoreIndented, string Text) block,
        string line)
    {
        var lineIndent = line.Length - line.TrimStart().Length;
        var trimmed = line.Trim();
        if (block.ContentIndent < 0)
        {
            // The first content line fixes the block's indentation.
            return block with { ContentIndent = lineIndent, Text = block.Text + trimmed };
        }

        var moreIndented = lineIndent > block.ContentIndent;
        var separator = block.Text.EndsWith('\n') ? string.Empty
            : moreIndented || block.PreviousMoreIndented ? "\n"
            : " ";
        return block with { PreviousMoreIndented = moreIndented, Text = block.Text + separator + trimmed };
    }

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
    // Line-anchored `run:` (block mapping) or a `run:` inside a flow mapping `{ …, run: … }`
    // (review round 8: `steps: [{run: "git show …"}]`); a flow value ends at `,` or `}` unless quoted.
    private static readonly Regex RunScalar = new(
        @"^\s*(?:-\s+)?[""']?run[""']?\s*:\s*(?<shell>.*)$",
        RegexOptions.CultureInvariant | RegexOptions.Compiled);

    private static readonly Regex FlowRunScalar = new(
        @"[{,]\s*[""']?run[""']?\s*:\s*(?<shell>""(?:[^""\\]|\\.)*""|'(?:[^']|'')*'|[^,}]*)",
        RegexOptions.CultureInvariant | RegexOptions.Compiled);

    // `run: <one-line shell>` (or `- run: …`) in a workflow: the scalar after `run:` is shell; a
    // block indicator (`|`, `>`) has no shell on this line and the block lines that follow are
    // plain shell already. Every `run:` inside flow mappings on the line is a step of its own and
    // is judged separately, so an unterminated quote in one step cannot swallow the next (review
    // round 9: `steps: [{run: "echo ready"}, {run: "git show HEAD^1:p"}]`). Other YAML lines are
    // lexed as they are (a leading `- name:` word is not git and yields nothing).
    private static IEnumerable<string> WorkflowRunScalars(string line)
    {
        var match = RunScalar.Match(line);
        if (match.Success)
        {
            var shell = StripTag(match.Groups["shell"].Value.Trim());
            return IsBlockIndicator(shell) ? Array.Empty<string>() : new[] { DecodeYamlScalar(shell) };
        }

        var flows = FlowRunScalar.Matches(line);
        return flows.Count == 0
            ? new[] { line }
            : flows.Select(flow => DecodeYamlScalar(flow.Groups["shell"].Value.Trim())).ToArray();
    }

    // A block-mapping `run:` whose quoted scalar does not close on its line starts a multi-line
    // scalar; an explicit tag before the quote is dropped (`run: !!str "git` + `show …"`).
    private static bool TryStartQuotedScalar(string line, out string scalar)
    {
        var match = RunScalar.Match(line);
        scalar = match.Success ? StripTag(match.Groups["shell"].Value.Trim()) : string.Empty;
        return scalar.Length > 0 && scalar[0] is '"' or '\'' && !IsClosedQuotedScalar(scalar);
    }

    private static string FoldQuotedContinuation(string text, string line)
    {
        var trimmed = line.Trim();
        return trimmed.Length == 0 ? text + "\n" : text + " " + trimmed;
    }

    private static bool IsClosedQuotedScalar(string scalar)
    {
        if (scalar[0] == '"')
        {
            for (var index = 1; index < scalar.Length; index++)
            {
                if (scalar[index] == '\\')
                {
                    index++;
                    continue;
                }

                if (scalar[index] == '"')
                {
                    return true;
                }
            }

            return false;
        }

        for (var index = 1; index < scalar.Length; index++)
        {
            if (scalar[index] == '\'')
            {
                if (index + 1 < scalar.Length && scalar[index + 1] == '\'')
                {
                    index++;
                    continue;
                }

                return true;
            }
        }

        return false;
    }

    // An explicit tag (`!!str "git …"`, `!custom …`) does not change the value that follows.
    private static readonly char[] TagSeparators = { ' ', '\t' };

    private static string StripTag(string scalar)
    {
        if (!scalar.StartsWith('!'))
        {
            return scalar;
        }

        // The tag ends at YAML separation whitespace — a space or a tab (review round 10:
        // `!!str<TAB>"git show …"`).
        var space = scalar.IndexOfAny(TagSeparators);
        return space < 0 ? string.Empty : scalar[(space + 1)..].TrimStart();
    }

    // A YAML flow scalar (`"…"` / `'…'`) decoded the way YAML does, up to its closing quote;
    // whatever follows (a YAML comment) is not part of the value. Double-quoted escapes:
    // `\xHH` / `\uHHHH` / `\UHHHHHHHH` decode to the character (`"\x67it show …"` is `git show …`),
    // `\n` is a real newline — i.e. a command separator for the shell lexer (review round 8:
    // `"echo ready\ngit show HEAD^1:… > out"` runs two commands) — `\t` a tab, `\"` a quote;
    // an escape outside the Unicode scalar range or in the surrogate block becomes U+FFFD instead
    // of throwing. Single-quoted `''` is one quote. Unquoted scalars are returned as they are.
    private static string DecodeYamlScalar(string scalar)
    {
        scalar = StripTag(scalar);
        if (scalar.Length >= 2 && scalar[0] == '"')
        {
            var value = new System.Text.StringBuilder();
            for (var index = 1; index < scalar.Length; index++)
            {
                if (scalar[index] == '\\' && index + 1 < scalar.Length)
                {
                    var escape = scalar[index + 1];
                    var width = escape switch { 'x' => 2, 'u' => 4, 'U' => 8, _ => 0 };
                    if (width > 0
                        && index + 1 + width < scalar.Length
                        && int.TryParse(scalar.AsSpan(index + 2, width), System.Globalization.NumberStyles.HexNumber, null, out var code))
                    {
                        value.Append(code is >= 0 and <= 0x10FFFF and (< 0xD800 or > 0xDFFF)
                            ? char.ConvertFromUtf32(code)
                            : "\uFFFD");
                        index += 1 + width;
                        continue;
                    }

                    value.Append(escape switch { 'n' => '\n', 't' => '\t', 'r' => '\r', _ => escape });
                    index++;
                    continue;
                }

                if (scalar[index] == '"')
                {
                    break;
                }

                value.Append(scalar[index]);
            }

            return value.ToString();
        }

        if (scalar.Length >= 2 && scalar[0] == '\'')
        {
            var value = new System.Text.StringBuilder();
            for (var index = 1; index < scalar.Length; index++)
            {
                if (scalar[index] == '\'')
                {
                    if (index + 1 < scalar.Length && scalar[index + 1] == '\'')
                    {
                        value.Append('\'');
                        index++;
                        continue;
                    }

                    break;
                }

                value.Append(scalar[index]);
            }

            return value.ToString();
        }

        return scalar;
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

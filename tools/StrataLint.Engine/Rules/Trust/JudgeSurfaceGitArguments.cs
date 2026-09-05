using System.Collections.Immutable;

namespace StrataLint.Engine;

// Per-verb argument parsing for SL-030: closed option tables, `--` semantics, attached and
// `=` option values, and the exact literal-HEAD object set. The invocation discovery lives in
// JudgeSurfaceRevisionScanner.cs; the shell structure in JudgeSurfaceShellLexer.cs.
internal static partial class JudgeSurfaceRevisionScanner
{
    // `git restore [-s <tree>] …`: `--source <tree>`, `--source=<tree>`, `-s <tree>`, `-s<tree>`.
    // Every source must be literal HEAD; a later `--source` overrides an earlier one in git, so any
    // non-HEAD value anywhere is a finding (review round 4: `-sHEAD^1`, `--source=HEAD --source=HEAD^1`).
    // Combined short options are git's parse-options semantics: `-WsHEAD^1` is `-W` then
    // `-s HEAD^1` (review round 6). Short flags restore knows; any other short letter fails closed.
    private static readonly HashSet<char> RestoreShortFlags = ['W', 'S', 'q', 'p', 'm', '2', '3'];

    // Long options restore knows. Git accepts unambiguous abbreviations (`--sour=HEAD^1` is
    // `--source=HEAD^1`, review round 8), so any long option outside this table fails closed
    // instead of being skipped.
    private static readonly HashSet<string> RestoreLongFlags = new(StringComparer.Ordinal)
    {
        "--staged", "--worktree", "--quiet", "--progress", "--no-progress", "--ours", "--theirs",
        "--merge", "--ignore-unmerged", "--ignore-skip-worktree-bits", "--recurse-submodules",
        "--no-recurse-submodules", "--overlay", "--no-overlay", "--pathspec-file-nul", "--patch",
    };

    private static readonly HashSet<string> RestoreLongOptionsWithValue = new(StringComparer.Ordinal)
    {
        "--conflict", "--pathspec-from-file",
    };

    // `--[no-]recurse-submodules[=<checkout>]` (restore, checkout, read-tree) takes its value only
    // attached; the bare word is a flag and must not consume `--source=HEAD^1` behind it (review
    // round 10: `restore --recurse-submodules --source=HEAD^1 -- p`).
    private static bool IsRecurseSubmodulesOption(string token) =>
        token.StartsWith("--recurse-submodules=", StringComparison.Ordinal);

    private static string? RestoreSource(string[] tokens)
    {
        for (var index = 0; index < tokens.Length; index++)
        {
            var token = tokens[index];
            if (token == "--")
            {
                break;
            }

            string? source = null;
            if (token == "--source")
            {
                source = index + 1 < tokens.Length ? tokens[++index] : string.Empty;
            }
            else if (token.StartsWith("--source=", StringComparison.Ordinal))
            {
                source = token["--source=".Length..];
            }
            else if (token.StartsWith("--", StringComparison.Ordinal))
            {
                if (RestoreLongOptionsWithValue.Contains(token))
                {
                    index++;
                    continue;
                }

                if (!(RestoreLongFlags.Contains(token)
                    || HasKnownValuePrefix(token, RestoreLongOptionsWithValue)
                    || IsRecurseSubmodulesOption(token)))
                {
                    return $"option '{token}' is not in the closed option table (fail-closed)";
                }
            }
            else if (token.Length > 1 && token[0] == '-' && token[1] != '-')
            {
                for (var position = 1; position < token.Length; position++)
                {
                    var letter = token[position];
                    if (letter == 's')
                    {
                        source = position + 1 < token.Length
                            ? token[(position + 1)..]
                            : index + 1 < tokens.Length ? tokens[++index] : string.Empty;
                        break;
                    }

                    if (!RestoreShortFlags.Contains(letter))
                    {
                        return $"option '-{letter}' is not in the closed option table (fail-closed)";
                    }
                }
            }

            if (source is not null && source != Head)
            {
                return $"--source '{source}' materializes another revision's files";
            }
        }

        return null;
    }

    // `git worktree add [options] <path> [<commit-ish>]`. Options are a closed table: an option
    // this table does not know fails closed, because an unknown option may consume the next token
    // and shift which positional is the commit-ish (review round 3: `--reason HEAD /tmp/h "$BASE"`).
    private static readonly HashSet<string> WorktreeAddFlags = new(StringComparer.Ordinal)
    {
        "--detach", "-d", "--lock", "-f", "--force", "--checkout", "--no-checkout", "--orphan",
        "-q", "--quiet", "--track", "--no-track", "--guess-remote", "--no-guess-remote",
        "--relative-paths", "--no-relative-paths",
    };

    private static readonly HashSet<string> WorktreeAddOptionsWithValue = new(StringComparer.Ordinal)
    {
        "-b", "-B", "--reason",
    };

    private static string? WorktreeAddRevision(string[] tokens)
    {
        if (tokens.Length == 0 || tokens[0] != "add")
        {
            return null;
        }

        var positional = new List<string>();
        for (var index = 1; index < tokens.Length; index++)
        {
            var token = tokens[index];
            if (token == "--")
            {
                // Git's option terminator: everything after it is positional (`-- -tmp HEAD`).
                positional.AddRange(tokens[(index + 1)..]);
                break;
            }

            if (WorktreeAddOptionsWithValue.Contains(token))
            {
                index++;
                continue;
            }

            if (WorktreeAddFlags.Contains(token) || HasKnownValuePrefix(token, WorktreeAddOptionsWithValue))
            {
                continue;
            }

            if (token.StartsWith('-'))
            {
                return $"add option '{token}' is not in the closed option table (fail-closed)";
            }

            positional.Add(token);
        }

        if (positional.Count < 2 || positional[1] == Head)
        {
            return null;
        }

        return $"add commit-ish '{positional[1]}' materializes another revision's tree";
    }

    private static readonly HashSet<string> ReadTreeFlags = new(StringComparer.Ordinal)
    {
        "-m", "-u", "-i", "-n", "-v", "-q", "--quiet", "--verbose", "--reset", "--empty", "--dry-run",
        "--trivial", "--aggressive", "--sparse-checkout", "--no-sparse-checkout", "--debug-unpack",
        "--recurse-submodules", "--no-recurse-submodules", "--",
    };

    private static readonly HashSet<string> ReadTreeOptionsWithValue = new(StringComparer.Ordinal)
    {
        "--prefix", "--index-output", "--exclude-per-directory",
    };

    private static string? ReadTreeOperands(string[] tokens)
    {
        var foundTree = false;
        for (var index = 0; index < tokens.Length; index++)
        {
            var token = tokens[index];
            if (ReadTreeOptionsWithValue.Contains(token))
            {
                index++;
                continue;
            }

            if (ReadTreeFlags.Contains(token)
                || HasKnownValuePrefix(token, ReadTreeOptionsWithValue)
                || IsRecurseSubmodulesOption(token))
            {
                continue;
            }

            if (token.StartsWith('-'))
            {
                return $"option '{token}' is not in the closed option table (fail-closed)";
            }

            foundTree = true;
            if (token != Head && token != "HEAD^{tree}")
            {
                return $"tree-ish '{token}' materializes another revision into the index";
            }
        }

        return foundTree ? null : "without a tree-ish is fail-closed";
    }

    // `git checkout [options] [<tree-ish>] [--] [<paths>]`: the first positional before `--` is the
    // tree-ish. Closed option table; branch-creating options consume a name, not a revision.
    private static readonly HashSet<string> CheckoutFlags = new(StringComparer.Ordinal)
    {
        "-q", "--quiet", "-f", "--force", "-m", "--merge", "--detach", "-p", "--patch", "--ours",
        "--theirs", "--ignore-skip-worktree-bits", "--track", "--no-track", "-t", "--guess",
        "--no-guess", "--recurse-submodules", "--no-recurse-submodules", "--overwrite-ignore",
        "--no-overwrite-ignore", "--progress", "--no-progress", "--ignore-other-worktrees",
        "--overlay", "--no-overlay", "-l",
    };

    private static readonly HashSet<string> CheckoutOptionsWithValue = new(StringComparer.Ordinal)
    {
        "-b", "-B", "--orphan", "--conflict", "--pathspec-from-file",
    };

    private static string? CheckoutRevision(string[] tokens)
    {
        for (var index = 0; index < tokens.Length; index++)
        {
            var token = tokens[index];
            if (token == "--")
            {
                return null;
            }

            if (CheckoutOptionsWithValue.Contains(token))
            {
                index++;
                continue;
            }

            if (CheckoutFlags.Contains(token)
                || HasKnownValuePrefix(token, CheckoutOptionsWithValue)
                || IsRecurseSubmodulesOption(token))
            {
                continue;
            }

            if (token.StartsWith('-'))
            {
                return $"option '{token}' is not in the closed option table (fail-closed)";
            }

            return token == Head ? null : $"'{token}' materializes another revision";
        }

        return null;
    }

    // `git archive [options] <tree-ish> [<path>…]`: closed option table; the first positional is the
    // tree-ish and must be literal HEAD.
    private static readonly HashSet<string> ArchiveFlags = new(StringComparer.Ordinal)
    {
        "-v", "--verbose", "-l", "--list", "--worktree-attributes", "-0", "-1", "-2", "-3", "-4",
        "-5", "-6", "-7", "-8", "-9",
    };

    private static readonly HashSet<string> ArchiveOptionsWithValue = new(StringComparer.Ordinal)
    {
        "-o", "--output", "--remote", "--exec", "--format", "--prefix", "--add-file",
        "--add-virtual-file", "--mtime",
    };

    private static string? ArchiveRevision(string[] tokens)
    {
        for (var index = 0; index < tokens.Length; index++)
        {
            var token = tokens[index];
            if (token == "--")
            {
                // `git archive -- <tree-ish>`: the tree-ish may follow the separator.
                var treeIsh = index + 1 < tokens.Length ? tokens[index + 1] : null;
                return treeIsh is null
                    ? "without an explicit HEAD tree-ish is fail-closed"
                    : treeIsh == Head ? null : $"'{treeIsh}' materializes another revision's tree";
            }

            if (ArchiveOptionsWithValue.Contains(token))
            {
                index++;
                continue;
            }

            if (ArchiveFlags.Contains(token) || HasKnownValuePrefix(token, ArchiveOptionsWithValue))
            {
                continue;
            }

            if (token.StartsWith('-'))
            {
                return $"option '{token}' is not in the closed option table (fail-closed)";
            }

            return token == Head ? null : $"'{token}' materializes another revision's tree";
        }

        return "without an explicit HEAD tree-ish is fail-closed";
    }

    // `--opt=value` and the attached short form `-oVALUE` both carry their value in the token.
    private static bool HasKnownValuePrefix(string token, HashSet<string> optionsWithValue)
    {
        var separator = token.IndexOf('=', StringComparison.Ordinal);
        if (separator > 0 && optionsWithValue.Contains(token[..separator]))
        {
            return true;
        }

        return token.Length > 2
            && token[0] == '-'
            && token[1] != '-'
            && optionsWithValue.Contains(token[..2]);
    }

    // `git show`: only a `<rev>:<path>` operand materializes a file; the revision must be literal HEAD.
    // Operands without a colon (`HEAD^1`, `--format=…`) print metadata or a patch, not a file.
    private static string? RevisionPathOperand(string[] tokens)
    {
        foreach (var token in tokens)
        {
            if (token == "--")
            {
                // Everything after `--` is a path, never a revision (`git show HEAD -- docs:notes`).
                break;
            }

            if (token.StartsWith('-'))
            {
                continue;
            }

            var colon = token.IndexOf(':', StringComparison.Ordinal);
            if (colon <= 0)
            {
                continue;
            }

            var revision = token[..colon];
            if (revision != Head)
            {
                return $"'{token}' materializes a file of revision '{revision}'";
            }
        }

        return null;
    }

    // `git cat-file`: the FIRST mode token decides. Metadata modes (-e/-t/-s) never materialize;
    // --batch* reads objects of unknown provenance; content modes (-p, blob/tree/commit/tag,
    // --textconv, --filters) must name a literal HEAD object.
    // cat-file options that take a value; their value must not be mistaken for a mode
    // (review round 6: `--path -e --filters HEAD^1:p` is a filters read, not an existence check).
    private static readonly HashSet<string> CatFileOptionsWithValue = new(StringComparer.Ordinal)
    {
        "--path",
    };

    private static string? CatFileOperand(string[] arguments)
    {
        var tokens = new List<string>();
        for (var index = 0; index < arguments.Length; index++)
        {
            if (CatFileOptionsWithValue.Contains(arguments[index]))
            {
                index++;
                continue;
            }

            if (HasKnownValuePrefix(arguments[index], CatFileOptionsWithValue))
            {
                continue;
            }

            tokens.Add(arguments[index]);
        }

        return CatFileMode(tokens.ToArray());
    }

    private static string? CatFileMode(string[] tokens)
    {
        var modeIndex = Array.FindIndex(tokens, static token => IsCatFileMode(token));
        if (modeIndex < 0)
        {
            return RevisionPathOperand(tokens);
        }

        var mode = tokens[modeIndex];
        if (mode.StartsWith("--batch", StringComparison.Ordinal))
        {
            return "--batch reads objects of unknown provenance (fail-closed)";
        }

        if (mode is "-e" or "-t" or "-s")
        {
            return null;
        }

        var foundOperand = false;
        for (var index = 0; index < tokens.Length; index++)
        {
            var token = tokens[index];
            if (index == modeIndex || token.StartsWith('-'))
            {
                continue;
            }

            foundOperand = true;
            if (!IsLiteralHeadObject(token))
            {
                return $"operand '{token}' materializes an object of another revision";
            }
        }

        return foundOperand ? null : $"content mode '{mode}' without an operand is fail-closed";
    }

    private static bool IsCatFileMode(string token) =>
        token is "-e" or "-t" or "-s" or "-p" or "blob" or "tree" or "commit" or "tag"
            or "--textconv" or "--filters"
        || token.StartsWith("--batch", StringComparison.Ordinal);

    // Exact allow-list: `HEAD^{/regex}` and `HEAD^{…}` in general can walk history
    // (`HEAD^{/derive}` resolved to an ancestor in review round 3), so only the two peel forms
    // that cannot leave the checked object are literal HEAD here.
    private static bool IsLiteralHeadObject(string operand) =>
        operand == Head
        || operand == "HEAD^{tree}"
        || operand == "HEAD^{commit}"
        || (operand.StartsWith("HEAD:", StringComparison.Ordinal) && operand.Length > "HEAD:".Length);
}

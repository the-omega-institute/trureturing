namespace StrataLint.Engine;

// Per-verb judgement over a parsed argument vector: which operand is the revision, and whether
// it is literal HEAD. Option arity comes from the generated tables, so a value-taking option can
// never be mistaken for the revision and an unknown option never shifts it (review rounds 3–11).
internal static partial class JudgeSurfaceRevisionScanner
{
    private static string? JudgeVerb(string verb, string[] arguments) => verb switch
    {
        "show" => ShowOperands(arguments),
        "cat-file" => CatFileOperands(arguments),
        "archive" => ArchiveTreeIsh(arguments),
        "worktree" => WorktreeAddCommitIsh(arguments),
        "checkout" => CheckoutRevision(arguments),
        "restore" => RestoreSource(arguments),
        "read-tree" => ReadTreeOperands(arguments),
        "checkout-index" => "materializes index contents whose provenance is not a revision (fail-closed)",
        _ => null,
    };

    // `git show <object>…`: a `<rev>:<path>` operand materializes that revision's file; a bare
    // revision prints a log/diff and is not a file read. Operands after `--` are pathspecs.
    private static string? ShowOperands(string[] arguments)
    {
        var parsed = ParseOptions(arguments, ShowOptions);
        if (parsed.Error is not null)
        {
            return parsed.Error;
        }

        for (var index = 0; index < parsed.PositionalsBeforeTerminator; index++)
        {
            var reason = RevisionPathOperand(parsed.Positionals[index]);
            if (reason is not null)
            {
                return reason;
            }
        }

        return null;
    }

    private static string? RevisionPathOperand(string operand)
    {
        var colon = operand.IndexOf(':', StringComparison.Ordinal);
        var revision = colon < 0 ? operand : operand[..colon];
        if (revision.Contains('$'))
        {
            // `$rev:p`, `"$obj"`, `$(printf %s HEAD^1:p)`: the lexer keeps `$` for a variable and a
            // placeholder for a substitution — a dynamic revision fails closed (review round 13);
            // `HEAD:$path` is fine, its revision is the literal HEAD.
            return $"operand '{operand}' names a revision of unknown provenance (fail-closed)";
        }

        if (colon < 0)
        {
            return null;
        }

        if (colon == 0)
        {
            return $"operand '{operand}' reads index contents whose provenance is not a revision (fail-closed)";
        }

        return revision == Head ? null : $"operand '{operand}' materializes another revision's file";
    }

    // `git cat-file`: `-e`/`-t`/`-s` are metadata; `-p`, `--textconv`, `--filters` and the
    // `<type> <object>` form emit contents and need a literal HEAD object; `--batch*` reads
    // objects named on stdin, so its provenance is unknown.
    private static string? CatFileOperands(string[] arguments)
    {
        var parsed = ParseOptions(arguments, CatFileOptions);
        if (parsed.Error is not null)
        {
            return parsed.Error;
        }

        if (parsed.Options.Any(option => option.Name.StartsWith("--batch", StringComparison.Ordinal)))
        {
            return "--batch reads objects of unknown provenance (fail-closed)";
        }

        var content = parsed.Has("-p") || parsed.Has("--textconv") || parsed.Has("--filters");
        var metadata = parsed.Has("-e") || parsed.Has("-t") || parsed.Has("-s");
        if (metadata && !content)
        {
            return null;
        }

        var operands = parsed.Positionals;
        if (!content)
        {
            if (operands.Length >= 2 && operands[0] is "blob" or "tree" or "commit" or "tag")
            {
                operands = operands[1..];
            }
            else
            {
                return "without a recognized mode is fail-closed";
            }
        }

        if (operands.Length == 0)
        {
            return "content mode without an operand is fail-closed";
        }

        foreach (var operand in operands)
        {
            if (!IsLiteralHeadObject(operand))
            {
                return $"operand '{operand}' materializes an object of another revision";
            }
        }

        return null;
    }

    // `git archive <tree-ish> [<path>…]`: the first operand is the tree-ish (it may follow `--`);
    // `--remote` archives another repository altogether.
    private static string? ArchiveTreeIsh(string[] arguments)
    {
        var parsed = ParseOptions(arguments, ArchiveOptions);
        if (parsed.Error is not null)
        {
            return parsed.Error;
        }

        if (parsed.Effective("--list", "-l"))
        {
            return null;
        }

        if (parsed.Has("--remote"))
        {
            return "--remote archives another repository's tree (fail-closed)";
        }

        if (parsed.Positionals.Length == 0)
        {
            return "without an explicit HEAD tree-ish is fail-closed";
        }

        var treeIsh = parsed.Positionals[0];
        return treeIsh == Head ? null : $"'{treeIsh}' materializes another revision's tree";
    }

    // `git worktree add <path> [<commit-ish>]`: the second operand is the revision checked out.
    private static string? WorktreeAddCommitIsh(string[] arguments)
    {
        if (arguments.Length == 0 || arguments[0] != "add")
        {
            return null;
        }

        var parsed = ParseOptions(arguments[1..], WorktreeAddOptions);
        if (parsed.Error is not null)
        {
            return "add " + parsed.Error;
        }

        if (parsed.Positionals.Length < 2 || parsed.Positionals[1] == Head)
        {
            return null;
        }

        return $"add commit-ish '{parsed.Positionals[1]}' materializes another revision's tree";
    }

    // `git checkout [<revision>] [-- <path>…]`: the first operand before `--` is the revision
    // (or a path restored from the index, whose provenance is not a revision either).
    private static string? CheckoutRevision(string[] arguments)
    {
        var parsed = ParseOptions(arguments, CheckoutOptions);
        if (parsed.Error is not null)
        {
            return parsed.Error;
        }

        if (parsed.PositionalsBeforeTerminator == 0)
        {
            return null;
        }

        var revision = parsed.Positionals[0];
        return revision == Head ? null : $"'{revision}' materializes another revision";
    }

    // `git restore [--source=<tree-ish>] <path>…`: only the source names a revision.
    private static string? RestoreSource(string[] arguments)
    {
        var parsed = ParseOptions(arguments, RestoreOptions);
        if (parsed.Error is not null)
        {
            return parsed.Error;
        }

        foreach (var (name, value) in parsed.Options)
        {
            if (name is "--source" or "-s" && value != Head)
            {
                return $"--source '{value}' materializes another revision's files";
            }
        }

        return null;
    }

    // `git read-tree <tree-ish>…`: every tree-ish is read into the index.
    private static string? ReadTreeOperands(string[] arguments)
    {
        var parsed = ParseOptions(arguments, ReadTreeOptions);
        if (parsed.Error is not null)
        {
            return parsed.Error;
        }

        if (parsed.Effective("--empty"))
        {
            return null;
        }

        if (parsed.Positionals.Length == 0)
        {
            return "without a tree-ish is fail-closed";
        }

        foreach (var treeIsh in parsed.Positionals)
        {
            if (treeIsh != Head && treeIsh != "HEAD^{tree}")
            {
                return $"tree-ish '{treeIsh}' materializes another revision into the index";
            }
        }

        return null;
    }

    // Exact allow-list: `HEAD^{/regex}` and `HEAD^{…}` in general can walk history
    // (`HEAD^{/derive}` resolved to an ancestor in review round 3), so only the two peel forms
    // that cannot leave the checked object are literal HEAD here.
    private static bool IsLiteralHeadObject(string operand) =>
        operand == Head
        || operand == "HEAD^{tree}"
        || operand == "HEAD^{commit}"
        || (operand.StartsWith("HEAD:", StringComparison.Ordinal) && operand.Length > "HEAD:".Length);
}

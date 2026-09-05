using System.Collections.Immutable;

namespace StrataLint.Engine;

internal enum OptionArity
{
    // `--quiet`, `-q`: never takes a value.
    Flag,

    // `--source <tree-ish>`, `-s <tree-ish>`: the value is the next word, or attached
    // (`--source=HEAD`, `-sHEAD`).
    Required,

    // `--recurse-submodules[=<checkout>]`, `-M[<n>]`: a value only when attached; the bare
    // option is a flag and never consumes the next word.
    OptionalAttached,
}

internal sealed record OptionSpec(OptionArity Arity, bool Negatable);

// One verb's option model, generated from `git <verb> -h` (see JudgeSurfaceGitOptionTables.cs).
// `NumericShort`: `-NUM` compression levels / `-<n>` counts. `UnknownLongIsFlag` /
// `UnknownShortIsFlag`: `git show` accepts the whole revision + diff option space, so an option the
// table does not know is read as a flag — it can only add operands to judge, never hide one.
internal sealed record OptionModel(
    IReadOnlyDictionary<string, OptionSpec> Long,
    IReadOnlyDictionary<char, OptionArity> Short,
    bool NumericShort,
    bool UnknownLongIsFlag,
    bool UnknownShortIsFlag);

internal sealed record ParsedOptions(
    ImmutableArray<(string Name, string? Value)> Options,
    ImmutableArray<string> Positionals,
    int PositionalsBeforeTerminator,
    string? Error)
{
    internal bool Has(string name) => Options.Any(option => option.Name == name);

    // The effective state of a boolean option: git applies `--x` / `--no-x` in order, the last
    // one wins (review round 13: `archive --list --no-list HEAD^1` archives HEAD^1).
    internal bool Effective(string name, params string[] aliases)
    {
        var negation = "--no-" + name[2..];
        var state = false;
        foreach (var (optionName, _) in Options)
        {
            if (optionName == name || aliases.Contains(optionName))
            {
                state = true;
            }
            else if (optionName == negation)
            {
                state = false;
            }
        }

        return state;
    }
}

internal static partial class JudgeSurfaceRevisionScanner
{
    // Git's argument grammar as parse-options implements it: `--` ends options; a long option is
    // exact, an unambiguous prefix (`--sour=HEAD^1`), or the `--no-` form of a negatable one; a
    // short cluster (`-WSsHEAD`) carries flags until the first option that takes a value, which
    // takes the rest of the word or the next word. Anything outside the model is an error — the
    // caller reports it as a fail-closed finding — except where the model says unknown is a flag.
    private static ParsedOptions ParseOptions(string[] tokens, OptionModel model)
    {
        var options = ImmutableArray.CreateBuilder<(string Name, string? Value)>();
        var positionals = ImmutableArray.CreateBuilder<string>();
        var beforeTerminator = -1;
        for (var index = 0; index < tokens.Length; index++)
        {
            var token = tokens[index];
            if (token == "--")
            {
                beforeTerminator = positionals.Count;
                positionals.AddRange(tokens[(index + 1)..]);
                break;
            }

            if (token.StartsWith("--", StringComparison.Ordinal))
            {
                var separator = token.IndexOf('=', StringComparison.Ordinal);
                var name = separator > 0 ? token[2..separator] : token[2..];
                var attached = separator > 0 ? token[(separator + 1)..] : null;
                var (spec, canonical, negated, error) = ResolveLong(name, model);
                if (error is not null)
                {
                    return Fail(error);
                }

                if (spec is null)
                {
                    if (!model.UnknownLongIsFlag)
                    {
                        return Fail($"option '--{name}' is not in git's option table");
                    }

                    options.Add(("--" + name, attached));
                    continue;
                }

                if (negated)
                {
                    if (attached is not null)
                    {
                        return Fail($"option '--no-{canonical}' takes no value");
                    }

                    options.Add(("--no-" + canonical, null));
                    continue;
                }

                switch (spec.Arity)
                {
                    case OptionArity.Flag:
                        if (attached is not null)
                        {
                            return Fail($"option '--{canonical}' takes no value");
                        }

                        options.Add(("--" + canonical, null));
                        break;
                    case OptionArity.Required:
                        if (attached is null)
                        {
                            if (index + 1 >= tokens.Length)
                            {
                                return Fail($"option '--{canonical}' is missing its value");
                            }

                            attached = tokens[++index];
                        }

                        options.Add(("--" + canonical, attached));
                        break;
                    default:
                        options.Add(("--" + canonical, attached));
                        break;
                }

                continue;
            }

            if (token.Length > 1 && token[0] == '-')
            {
                if (model.NumericShort && char.IsAsciiDigit(token[1]))
                {
                    options.Add(("-NUM", token[1..]));
                    continue;
                }

                for (var position = 1; position < token.Length; position++)
                {
                    var letter = token[position];
                    if (!model.Short.TryGetValue(letter, out var arity))
                    {
                        if (!model.UnknownShortIsFlag)
                        {
                            return Fail($"option '-{letter}' is not in git's option table");
                        }

                        options.Add(("-" + letter, null));
                        continue;
                    }

                    if (arity == OptionArity.Flag)
                    {
                        options.Add(("-" + letter, null));
                        continue;
                    }

                    var rest = position + 1 < token.Length ? token[(position + 1)..] : null;
                    if (arity == OptionArity.Required && rest is null)
                    {
                        if (index + 1 >= tokens.Length)
                        {
                            return Fail($"option '-{letter}' is missing its value");
                        }

                        rest = tokens[++index];
                    }

                    options.Add(("-" + letter, rest));
                    break;
                }

                continue;
            }

            positionals.Add(token);
        }

        return new ParsedOptions(
            options.ToImmutable(),
            positionals.ToImmutable(),
            beforeTerminator < 0 ? positionals.Count : beforeTerminator,
            null);

        static ParsedOptions Fail(string error) =>
            new(ImmutableArray<(string, string?)>.Empty, ImmutableArray<string>.Empty, 0, error + " (fail-closed)");
    }

    private static (OptionSpec? Spec, string Name, bool Negated, string? Error) ResolveLong(string name, OptionModel model)
    {
        if (model.Long.TryGetValue(name, out var exact))
        {
            return (exact, name, false, null);
        }

        if (name.StartsWith("no-", StringComparison.Ordinal)
            && model.Long.TryGetValue(name[3..], out var negated)
            && negated.Negatable)
        {
            return (negated, name[3..], true, null);
        }

        // parse-options accepts any unambiguous prefix of a long option or of its `--no-` form.
        var candidates = new List<(OptionSpec Spec, string Name, bool Negated)>();
        foreach (var (key, spec) in model.Long)
        {
            if (key.StartsWith(name, StringComparison.Ordinal))
            {
                candidates.Add((spec, key, false));
            }

            if (spec.Negatable && ("no-" + key).StartsWith(name, StringComparison.Ordinal))
            {
                candidates.Add((spec, key, true));
            }
        }

        return candidates.Count switch
        {
            1 => (candidates[0].Spec, candidates[0].Name, candidates[0].Negated, null),
            0 => (null, name, false, null),
            _ => (null, name, false, $"option '--{name}' is an ambiguous abbreviation"),
        };
    }
}

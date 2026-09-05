using System.Collections.Immutable;
using System.Text;

namespace StrataLint.Engine;

/// <summary>
/// The smallest shell lexer SL-030 needs: it turns one logical line into simple commands, each a
/// list of words. Quotes group and are removed (contents kept verbatim, nothing is expanded),
/// backslash escapes the next character outside single quotes, an unquoted word-initial <c>#</c>
/// ends the line, <c>|</c> <c>;</c> <c>&amp;</c> <c>&amp;&amp;</c> <c>||</c> and unquoted grouping
/// (<c>(</c> <c>)</c> <c>{</c> <c>}</c>) end a command, and a redirection (<c>&gt;</c>, <c>&gt;&gt;</c>,
/// <c>&lt;</c>, <c>2&gt;</c>, <c>&amp;&gt;</c>, <c>2&gt;&amp;1</c>, …) consumes only itself and its
/// target word — the arguments after it are still arguments. A command substitution
/// <c>$(…)</c> or <c>`…`</c> (also inside double quotes) is lexed recursively and its commands are
/// emitted as commands of their own; the enclosing word keeps a placeholder. Nesting deeper than
/// <see cref="MaximumDepth"/> stops lexing and is reported through <c>Truncated</c> so the rule can
/// fail closed. This is deliberately not a Bash evaluator: no expansion, no heredoc bodies.
/// </summary>
internal static class JudgeSurfaceShellLexer
{
    internal const int MaximumDepth = 16;

    private const string SubstitutionPlaceholder = "$(...)";

    internal sealed record Result(ImmutableArray<ImmutableArray<string>> Commands, bool Truncated);

    internal static Result Commands(string line)
    {
        var commands = ImmutableArray.CreateBuilder<ImmutableArray<string>>();
        var truncated = false;
        Lex(line, 0, line.Length, 0, commands, ref truncated);
        return new Result(commands.ToImmutable(), truncated);
    }

    private static void Lex(
        string text,
        int start,
        int end,
        int depth,
        ImmutableArray<ImmutableArray<string>>.Builder commands,
        ref bool truncated)
    {
        if (depth > MaximumDepth)
        {
            truncated = true;
            return;
        }

        var words = new List<string>();
        var word = new StringBuilder();
        var inWord = false;
        var pendingRedirectionTarget = false;
        // Set only when an UNQUOTED `>`/`<` starts (or extends a descriptor prefix of) the current
        // word; a quoted or escaped `>` is an ordinary argument (review round 6: `-d '>' HEAD^1`).
        var wordIsRedirection = false;
        // Set when any quoted or escaped text entered the current word: a quoted `'2'` before `>`
        // is a path, not a descriptor (review round 7: `-d '2'>out HEAD^1`).
        var wordHasQuotedContent = false;

        void EndWord()
        {
            if (!inWord)
            {
                return;
            }

            var value = word.ToString();
            var redirection = wordIsRedirection;
            word.Clear();
            inWord = false;
            wordIsRedirection = false;
            wordHasQuotedContent = false;
            if (pendingRedirectionTarget)
            {
                pendingRedirectionTarget = false;
                return;
            }

            if (redirection && IsRedirectionOperator(value, out var hasGluedTarget))
            {
                pendingRedirectionTarget = !hasGluedTarget;
                return;
            }

            words.Add(value);
        }

        void EndCommand()
        {
            EndWord();
            pendingRedirectionTarget = false;
            if (words.Count > 0)
            {
                commands.Add(words.ToImmutableArray());
                words.Clear();
            }
        }

        var index = start;
        while (index < end)
        {
            var character = text[index];
            switch (character)
            {
                case '\'':
                {
                    var close = text.IndexOf('\'', index + 1, end - index - 1);
                    if (close < 0)
                    {
                        close = end;
                    }

                    word.Append(text, index + 1, close - index - 1);
                    inWord = true;
                    wordHasQuotedContent = true;
                    index = close + 1;
                    continue;
                }

                case '"':
                {
                    index++;
                    inWord = true;
                    wordHasQuotedContent = true;
                    while (index < end && text[index] != '"')
                    {
                        if (text[index] == '\\' && index + 1 < end)
                        {
                            word.Append(text[index + 1]);
                            index += 2;
                            continue;
                        }

                        if (text[index] == '$' && index + 1 < end && text[index + 1] == '(')
                        {
                            index = LexDollarSubstitution(text, index, end, depth, commands, word, ref truncated);
                            continue;
                        }

                        if (text[index] == '`')
                        {
                            index = LexBacktickSubstitution(text, index, end, depth, commands, word, ref truncated);
                            continue;
                        }

                        word.Append(text[index]);
                        index++;
                    }

                    index++;
                    continue;
                }

                case '\\':
                    if (index + 1 < end)
                    {
                        word.Append(text[index + 1]);
                        inWord = true;
                        wordHasQuotedContent = true;
                    }

                    index += 2;
                    continue;

                case '$' when index + 1 < end && text[index + 1] == '(':
                    inWord = true;
                    index = LexDollarSubstitution(text, index, end, depth, commands, word, ref truncated);
                    continue;

                case '`':
                    inWord = true;
                    index = LexBacktickSubstitution(text, index, end, depth, commands, word, ref truncated);
                    continue;

                case '#' when !inWord:
                    EndCommand();
                    return;

                case '&' when inWord && word.Length > 0 && word[^1] is '>' or '<':
                    // `2>&1`, `>&2`: the descriptor duplication belongs to the redirection word.
                    word.Append('&');
                    index++;
                    continue;

                case '&' when !inWord && index + 1 < end && text[index + 1] is '>' or '<':
                    // `&>file`: a redirection word that starts with '&'.
                    word.Append('&');
                    inWord = true;
                    wordIsRedirection = true;
                    index++;
                    continue;

                case '>' when index + 1 < end && text[index + 1] == '(':
                case '<' when index + 1 < end && text[index + 1] == '(':
                    // Process substitution `<(…)` / `>(…)`: the inner command runs (review round 6);
                    // lex it as its own command and keep a placeholder word outside.
                    EndWord();
                    inWord = true;
                    index = LexDollarSubstitution(text, index, end, depth, commands, word, ref truncated);
                    continue;

                case '>':
                case '<':
                    // Shell splits `HEAD>out` into `HEAD` and `>out`; only a descriptor prefix
                    // (`2>`, `&>`) or a repeated operator (`>>`) stays glued to the operator.
                    if (inWord && !(wordIsRedirection || (IsAllDigits(word) && !wordHasQuotedContent)))
                    {
                        EndWord();
                    }

                    word.Append(character);
                    inWord = true;
                    wordIsRedirection = true;
                    index++;
                    continue;

                case '(':
                case ')':
                    // Unquoted subshell boundaries: `( git show … )` runs git show.
                    EndCommand();
                    index++;
                    continue;

                case '{' when !inWord && IsWordBoundary(text, index + 1, end):
                case '}' when !inWord && IsWordBoundary(text, index + 1, end):
                    // Unquoted group boundaries: `{ git show …; }` runs git show. Braces inside a
                    // word (`${X}`, `HEAD^{tree}`) are ordinary characters.
                    EndCommand();
                    index++;
                    continue;

                case '|':
                case ';':
                case '&':
                case '\n':
                case '\r':
                    EndCommand();
                    index++;
                    continue;

                case ' ':
                case '\t':
                    EndWord();
                    index++;
                    continue;

                default:
                    word.Append(character);
                    inWord = true;
                    index++;
                    continue;
            }
        }

        EndCommand();
    }

    private static bool IsWordBoundary(string text, int index, int end) =>
        index >= end || text[index] is ' ' or '\t' or '\n' or '\r' or ';' or '&' or '|' or ')' or '(';

    // `$(` … `)` with the closing parenthesis found by a quote-aware walk: parentheses inside
    // single or double quotes do not count, backslash escapes the next character, nested `$(`
    // and bare `(` raise the depth (review round 5: `"$(printf '%s' ')'; git show …)"`).
    private static int LexDollarSubstitution(
        string text,
        int index,
        int end,
        int depth,
        ImmutableArray<ImmutableArray<string>>.Builder commands,
        StringBuilder word,
        ref bool truncated)
    {
        var cursor = index + 2;
        var nesting = 1;
        var inSingle = false;
        var inDouble = false;
        while (cursor < end)
        {
            var character = text[cursor];
            if (character == '\\' && !inSingle)
            {
                cursor += 2;
                continue;
            }

            if (inSingle)
            {
                inSingle = character != '\'';
            }
            else if (inDouble)
            {
                inDouble = character != '"';
            }
            else if (character == '\'')
            {
                inSingle = true;
            }
            else if (character == '"')
            {
                inDouble = true;
            }
            else if (character == '(')
            {
                nesting++;
            }
            else if (character == ')')
            {
                nesting--;
                if (nesting == 0)
                {
                    break;
                }
            }

            cursor++;
        }

        var close = cursor < end ? cursor : end;
        Lex(text, index + 2, close, depth + 1, commands, ref truncated);
        word.Append(SubstitutionPlaceholder);
        return close + 1;
    }

    private static int LexBacktickSubstitution(
        string text,
        int index,
        int end,
        int depth,
        ImmutableArray<ImmutableArray<string>>.Builder commands,
        StringBuilder word,
        ref bool truncated)
    {
        var close = text.IndexOf('`', index + 1, end - index - 1);
        if (close < 0)
        {
            close = end;
        }

        Lex(text, index + 1, close, depth + 1, commands, ref truncated);
        word.Append(SubstitutionPlaceholder);
        return close + 1;
    }

    private static bool IsAllDigits(StringBuilder word)
    {
        for (var index = 0; index < word.Length; index++)
        {
            if (!char.IsAsciiDigit(word[index]))
            {
                return false;
            }
        }

        return true;
    }

    private static bool IsRedirectionOperator(string value, out bool hasGluedTarget)
    {
        hasGluedTarget = false;
        var index = 0;
        while (index < value.Length && char.IsAsciiDigit(value[index]))
        {
            index++;
        }

        if (index < value.Length && value[index] == '&' && index + 1 < value.Length
            && value[index + 1] is '>' or '<')
        {
            index++;
        }

        if (index >= value.Length || value[index] is not ('>' or '<'))
        {
            return false;
        }

        while (index < value.Length && value[index] is '>' or '<' or '&' or '|')
        {
            index++;
        }

        // `2>&1`, `>&2`, `>out`: the target is glued to the operator.
        hasGluedTarget = index < value.Length;
        return true;
    }
}

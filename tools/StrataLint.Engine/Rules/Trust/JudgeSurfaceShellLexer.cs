using System.Collections.Immutable;
using System.Text;

namespace StrataLint.Engine;

/// <summary>
/// The smallest shell lexer SL-030 needs: it turns one line into simple commands, each a list of
/// words. Quotes group and are removed (contents kept verbatim, nothing is expanded), backslash
/// escapes the next character outside single quotes, an unquoted word-initial <c>#</c> ends the
/// line, <c>|</c> <c>;</c> <c>&amp;</c> <c>&amp;&amp;</c> <c>||</c> end a command, and a redirection
/// (<c>&gt;</c>, <c>&gt;&gt;</c>, <c>&lt;</c>, <c>2&gt;</c>, <c>&amp;&gt;</c>, <c>2&gt;&amp;1</c>, …)
/// consumes only itself and its target word — the arguments after it are still arguments
/// (<c>git worktree add /tmp/h 2&gt;log HEAD^1</c> still names <c>HEAD^1</c>). A command substitution
/// <c>$(…)</c> or <c>`…`</c> is lexed recursively and its commands are emitted as commands of their
/// own; the enclosing word keeps a placeholder so the outer command's arity is preserved.
/// This is deliberately not a Bash evaluator: no expansion, no heredoc bodies, no arithmetic.
/// </summary>
internal static class JudgeSurfaceShellLexer
{
    private const string SubstitutionPlaceholder = "$(...)";

    internal static ImmutableArray<ImmutableArray<string>> Commands(string line)
    {
        var commands = ImmutableArray.CreateBuilder<ImmutableArray<string>>();
        Lex(line, 0, line.Length, commands);
        return commands.ToImmutable();
    }

    private static void Lex(
        string text,
        int start,
        int end,
        ImmutableArray<ImmutableArray<string>>.Builder commands)
    {
        var words = new List<string>();
        var word = new StringBuilder();
        var inWord = false;
        var pendingRedirectionTarget = false;

        void EndWord()
        {
            if (!inWord)
            {
                return;
            }

            var value = word.ToString();
            word.Clear();
            inWord = false;
            if (pendingRedirectionTarget)
            {
                pendingRedirectionTarget = false;
                return;
            }

            if (IsRedirectionOperator(value, out var hasGluedTarget))
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
                    index = close + 1;
                    continue;
                }

                case '"':
                {
                    index++;
                    inWord = true;
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
                            index = LexSubstitution(text, index, end, commands, word);
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
                    }

                    index += 2;
                    continue;

                case '$' when index + 1 < end && text[index + 1] == '(':
                    inWord = true;
                    index = LexSubstitution(text, index, end, commands, word);
                    continue;

                case '`':
                {
                    var close = text.IndexOf('`', index + 1, end - index - 1);
                    if (close < 0)
                    {
                        close = end;
                    }

                    Lex(text, index + 1, close, commands);
                    word.Append(SubstitutionPlaceholder);
                    inWord = true;
                    index = close + 1;
                    continue;
                }

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
                    index++;
                    continue;

                case '>':
                case '<':
                    // Shell splits `HEAD>out` into `HEAD` and `>out`; only a descriptor prefix
                    // (`2>`, `&>`) or a repeated operator (`>>`) stays glued to the operator.
                    if (inWord && !IsRedirectionPrefix(word))
                    {
                        EndWord();
                    }

                    word.Append(character);
                    inWord = true;
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

    private static int LexSubstitution(
        string text,
        int index,
        int end,
        ImmutableArray<ImmutableArray<string>>.Builder commands,
        StringBuilder word)
    {
        var depth = 0;
        var cursor = index + 1;
        while (cursor < end)
        {
            var character = text[cursor];
            if (character == '(')
            {
                depth++;
            }
            else if (character == ')')
            {
                depth--;
                if (depth == 0)
                {
                    break;
                }
            }

            cursor++;
        }

        var close = cursor < end ? cursor : end;
        Lex(text, index + 2, close, commands);
        word.Append(SubstitutionPlaceholder);
        return close + 1;
    }

    private static bool IsRedirectionPrefix(StringBuilder word)
    {
        for (var index = 0; index < word.Length; index++)
        {
            if (!(char.IsAsciiDigit(word[index]) || word[index] is '&' or '>' or '<'))
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

        // `2>&1`, `>&2`: the descriptor is the target and it is glued.
        hasGluedTarget = index < value.Length;
        return true;
    }
}

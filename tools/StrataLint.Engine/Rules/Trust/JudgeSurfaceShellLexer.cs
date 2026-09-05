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
        // Length of the operator prefix of a redirection word (`2>`, `{fd}>`, `>>`, `>&`, `>|`);
        // anything appended after it — quoted, escaped or plain — is the glued target, so the
        // quoted `>` in `>'>'` is a file name and cannot re-open the operator (review round 9).
        var redirectionOperatorLength = 0;

        void EndWord()
        {
            if (!inWord)
            {
                return;
            }

            var value = word.ToString();
            var redirection = wordIsRedirection;
            var hasGluedTarget = word.Length > redirectionOperatorLength;
            word.Clear();
            inWord = false;
            wordIsRedirection = false;
            wordHasQuotedContent = false;
            redirectionOperatorLength = 0;
            if (pendingRedirectionTarget)
            {
                pendingRedirectionTarget = false;
                return;
            }

            if (redirection)
            {
                // `2>&1`, `>&2`, `>out`, `>'>'`: the target is glued to the operator; a bare
                // operator takes the next word as its target.
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
                            // Inside double quotes a backslash escapes only `$`, `` ` ``, `"`, `\`
                            // and newline; before any other character it stays (`g"\i"t` is `g\it`,
                            // not git; review round 10).
                            if (text[index + 1] is not ('$' or '`' or '"' or '\\' or '\n'))
                            {
                                word.Append('\\');
                            }

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

                case '$' when index + 1 < end && text[index + 1] == '\'':
                {
                    // ANSI-C quoting `$'…'`: a quoted word whose backslash escapes decode
                    // (review round 8: `$'git' show …` runs git).
                    index += 2;
                    inWord = true;
                    wordHasQuotedContent = true;
                    while (index < end && text[index] != '\'')
                    {
                        if (text[index] == '\\' && index + 1 < end)
                        {
                            index = AppendAnsiCEscape(text, index, end, word);
                            continue;
                        }

                        word.Append(text[index]);
                        index++;
                    }

                    index++;
                    continue;
                }

                case '`':
                    inWord = true;
                    index = LexBacktickSubstitution(text, index, end, depth, commands, word, ref truncated);
                    continue;

                case '#' when !inWord:
                    // A comment runs to the end of its line only; the lines after it (a decoded
                    // YAML `\n`, a folded block) are still shell (review round 11).
                    EndCommand();
                    index = text.IndexOf('\n', index, end - index);
                    if (index < 0)
                    {
                        return;
                    }

                    continue;

                case '&' when inWord && wordIsRedirection && word.Length == redirectionOperatorLength && word[^1] is '>' or '<':
                    // `2>&1`, `>&2`: the descriptor duplication belongs to the redirection operator.
                    word.Append('&');
                    redirectionOperatorLength = word.Length;
                    index++;
                    continue;

                case '&' when !inWord && index + 1 < end && text[index + 1] is '>' or '<':
                    // `&>file`: a redirection word that starts with '&'.
                    word.Append('&');
                    inWord = true;
                    wordIsRedirection = true;
                    redirectionOperatorLength = word.Length;
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
                    // (`2>`, `{fd}>`, `&>`) or a repeated operator (`>>`) stays glued to the
                    // operator; a redirection that already has its target (`>out>x`) is complete.
                    if (inWord
                        && !((wordIsRedirection && word.Length == redirectionOperatorLength)
                            || (!wordHasQuotedContent && (IsAllDigits(word) || IsDescriptorVariable(word)))))
                    {
                        EndWord();
                    }

                    word.Append(character);
                    inWord = true;
                    wordIsRedirection = true;
                    redirectionOperatorLength = word.Length;
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

                case '|' when inWord && wordIsRedirection && word.Length == redirectionOperatorLength && word[^1] == '>':
                    // `>|file` (clobber) is one redirection operator, not a pipe (review round 8).
                    word.Append('|');
                    redirectionOperatorLength = word.Length;
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
        // Old-style substitution: the closing backtick is the first UNESCAPED one; an escaped
        // backtick inside is a nested substitution, so the inner text is lexed with `\`` unescaped
        // (review round 8: x=`echo \`git show HEAD^1:p\``).
        var cursor = index + 1;
        while (cursor < end && text[cursor] != '`')
        {
            cursor += text[cursor] == '\\' ? 2 : 1;
        }

        var close = cursor < end ? cursor : end;
        var inner = text[(index + 1)..close].Replace("\\`", "`", StringComparison.Ordinal);
        Lex(inner, 0, inner.Length, depth + 1, commands, ref truncated);
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

    // Bash allocates a descriptor into a variable with `{name}>file` / `{name}<file`; the braces
    // word is the descriptor prefix of that redirection, not a command word (review round 9:
    // `{fd}>/tmp/out git show HEAD^1:p` runs git).
    private static bool IsDescriptorVariable(StringBuilder word)
    {
        if (word.Length < 3 || word[0] != '{' || word[^1] != '}' || !(char.IsAsciiLetter(word[1]) || word[1] == '_'))
        {
            return false;
        }

        for (var index = 2; index < word.Length - 1; index++)
        {
            if (!(char.IsAsciiLetterOrDigit(word[index]) || word[index] == '_'))
            {
                return false;
            }
        }

        return true;
    }

    // `$'…'` escapes as Bash decodes them: `\xHH` (one or two hex digits), `\NNN` (one to three
    // octal digits), the C escapes and `\\` / `\'` / `\"`; `$'\x67it'` is `git` (review round 9).
    private static int AppendAnsiCEscape(string text, int index, int end, StringBuilder word)
    {
        var escape = text[index + 1];
        if (escape == 'x')
        {
            var digits = 0;
            while (digits < 2 && index + 2 + digits < end && char.IsAsciiHexDigit(text[index + 2 + digits]))
            {
                digits++;
            }

            if (digits > 0)
            {
                word.Append((char)Convert.ToInt32(text.Substring(index + 2, digits), 16));
                return index + 2 + digits;
            }
        }
        else if (escape is >= '0' and <= '7')
        {
            var digits = 1;
            while (digits < 3 && index + 1 + digits < end && text[index + 1 + digits] is >= '0' and <= '7')
            {
                digits++;
            }

            word.Append((char)Convert.ToInt32(text.Substring(index + 1, digits), 8));
            return index + 1 + digits;
        }

        word.Append(escape switch
        {
            'n' => '\n',
            't' => '\t',
            'r' => '\r',
            'a' => '\a',
            'b' => '\b',
            'e' or 'E' => '\u001b',
            'f' => '\f',
            'v' => '\v',
            var other => other,
        });
        return index + 2;
    }
}

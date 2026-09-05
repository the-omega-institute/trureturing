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

    // A simple command and the line (1-based within the lexed text) where its first word starts.
    internal sealed record LexedCommand(int Line, ImmutableArray<string> Words);

    internal sealed record Result(ImmutableArray<LexedCommand> Commands, bool Truncated);

    // The whole text of a script or scalar is lexed at once: line continuations, comments and
    // newlines are the lexer's business alone (review round 14: a comment ending in a backslash
    // does not continue onto the next line — bash drops the rest of the physical line).
    internal static Result Commands(string text)
    {
        var commands = ImmutableArray.CreateBuilder<LexedCommand>();
        var truncated = false;
        Lex(text, 0, text.Length, 0, 0, commands, ref truncated);
        return new Result(commands.ToImmutable(), truncated);
    }

    private static void Lex(
        string text,
        int start,
        int end,
        int depth,
        int lineOffset,
        ImmutableArray<LexedCommand>.Builder commands,
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
        // Index of the first character of the current command, for its line number.
        var commandStart = -1;

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
                commands.Add(new LexedCommand(lineOffset + 1 + CountNewlines(text, commandStart), words.ToImmutableArray()));
                words.Clear();
            }

            commandStart = -1;
        }

        var index = start;
        while (index < end)
        {
            var character = text[index];
            if (commandStart < 0
                && character is not (' ' or '\t' or '\n' or '\r' or ';' or '&' or '|' or '(' or ')')
                && !(character == '\\' && index + 1 < end && text[index + 1] == '\n'))
            {
                commandStart = index;
            }

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
                            // not git; review round 10). Backslash-newline vanishes (round 12).
                            if (text[index + 1] == '\n')
                            {
                                index += 2;
                                continue;
                            }

                            if (text[index + 1] is not ('$' or '`' or '"' or '\\'))
                            {
                                word.Append('\\');
                            }

                            word.Append(text[index + 1]);
                            index += 2;
                            continue;
                        }

                        if (text[index] == '$' && index + 1 < end && text[index + 1] == '(')
                        {
                            index = LexDollarSubstitution(text, index, end, depth, lineOffset, commands, word, ref truncated);
                            continue;
                        }

                        if (text[index] == '`')
                        {
                            index = LexBacktickSubstitution(text, index, end, depth, lineOffset, commands, word, ref truncated);
                            continue;
                        }

                        word.Append(text[index]);
                        index++;
                    }

                    index++;
                    continue;
                }

                case '\\' when index + 1 < end && text[index + 1] == '\n':
                    // Backslash-newline is removed outright: a line continuation, also inside a
                    // YAML block scalar handed over whole (review round 12: `git \` + `show …`).
                    index += 2;
                    continue;

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
                    index = LexDollarSubstitution(text, index, end, depth, lineOffset, commands, word, ref truncated);
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
                            index = AppendAnsiCEscape(text, index, end, word, out var nul);
                            if (nul)
                            {
                                // Bash cuts an ANSI-C string at its first NUL: the rest of the
                                // segment up to the closing quote is dropped (review round 14:
                                // `$'git\000tail' show …` runs git).
                                while (index < end && text[index] != '\'')
                                {
                                    index += text[index] == '\\' ? 2 : 1;
                                }
                            }

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
                    index = LexBacktickSubstitution(text, index, end, depth, lineOffset, commands, word, ref truncated);
                    continue;

                case '#' when IsCommentStart(character, inWord):
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
                    index = LexDollarSubstitution(text, index, end, depth, lineOffset, commands, word, ref truncated);
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

    private static bool IsCommentStart(char character, bool inWord) => character == '#' && !inWord;

    // `$(` … `)` with the closing parenthesis found by the same comment/quote state as command
    // lexing: parentheses in quotes or word-initial comments do not count, backslash escapes the
    // next character, and nested `$(` or bare `(` raise the depth.
    private static int LexDollarSubstitution(
        string text,
        int index,
        int end,
        int depth,
        int lineOffset,
        ImmutableArray<LexedCommand>.Builder commands,
        StringBuilder word,
        ref bool truncated)
    {
        var cursor = index + 2;
        var nesting = 1;
        var inSingle = false;
        var inDouble = false;
        var inWord = false;
        while (cursor < end)
        {
            var character = text[cursor];
            if (character == '\\' && !inSingle)
            {
                inWord |= cursor + 1 >= end || text[cursor + 1] != '\n';
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
            else if (IsCommentStart(character, inWord))
            {
                cursor = text.IndexOf('\n', cursor, end - cursor);
                if (cursor < 0)
                {
                    cursor = end;
                    break;
                }

                inWord = false;
            }
            else if (character == '\'')
            {
                inSingle = true;
                inWord = true;
            }
            else if (character == '"')
            {
                inDouble = true;
                inWord = true;
            }
            else if (character == '(')
            {
                nesting++;
                inWord = false;
            }
            else if (character == ')')
            {
                nesting--;
                if (nesting == 0)
                {
                    break;
                }

                inWord = false;
            }
            else
            {
                inWord = character is not (' ' or '\t' or '\n' or '\r' or ';' or '&' or '|');
            }

            cursor++;
        }

        var close = cursor < end ? cursor : end;
        Lex(text, index + 2, close, depth + 1, lineOffset, commands, ref truncated);
        word.Append(SubstitutionPlaceholder);
        return close + 1;
    }

    private static int LexBacktickSubstitution(
        string text,
        int index,
        int end,
        int depth,
        int lineOffset,
        ImmutableArray<LexedCommand>.Builder commands,
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
        Lex(inner, 0, inner.Length, depth + 1, lineOffset + CountNewlines(text, index), commands, ref truncated);
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
    private static int AppendAnsiCEscape(string text, int index, int end, StringBuilder word, out bool nul)
    {
        nul = false;
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
                nul = AppendByte(word, Convert.ToInt32(text.Substring(index + 2, digits), 16));
                return index + 2 + digits;
            }
        }
        else if (escape == 'c' && index + 2 < end)
        {
            // Bash's quote parser makes the escaped backslash pair the operand of `\c\\`; consume
            // both before looking for the closing quote. Bash 3.2 and 5 differ only in whether an
            // extra backslash byte survives, not in where the word ends.
            var operand = text[index + 2];
            nul = AppendByte(word, char.ToUpperInvariant(operand) & 0x1F);
            return operand == '\\' && index + 3 < end ? index + 4 : index + 3;
        }
        else if (escape is >= '0' and <= '7')
        {
            var digits = 1;
            while (digits < 3 && index + 1 + digits < end && text[index + 1 + digits] is >= '0' and <= '7')
            {
                digits++;
            }

            // Bash keeps the low byte of an octal escape (`\547` is 359 → 103 = `g`; review round 13).
            nul = AppendByte(word, Convert.ToInt32(text.Substring(index + 1, digits), 8) & 0xFF);
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

    // A NUL byte ends an ANSI-C string in bash; nothing after it survives. Returns true for NUL.
    private static bool AppendByte(StringBuilder word, int value)
    {
        if (value == 0)
        {
            return true;
        }

        word.Append((char)value);
        return false;
    }

    private static int CountNewlines(string text, int upTo)
    {
        var count = 0;
        for (var index = 0; index < upTo && index < text.Length; index++)
        {
            if (text[index] == '\n')
            {
                count++;
            }
        }

        return count;
    }
}

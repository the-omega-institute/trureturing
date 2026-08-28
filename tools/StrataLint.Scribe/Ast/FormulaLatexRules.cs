using System.Collections.Immutable;

namespace StrataLint.Scribe;

/// <summary>
/// What the raw LaTeX escape hatch must satisfy before it becomes a formula: a script
/// mark and an argument-taking macro each have their one token, and no base is scripted
/// twice the same way. Every violation is a KaTeX parse error that nothing downstream of
/// these constructors can detect, so the rules run where the formula is built.
/// </summary>
internal static class FormulaLatexRules
{
    /// <summary>The script marks a base already carries.</summary>
    [Flags]
    private enum ScriptMarks
    {
        None = 0,
        Superscript = 1,
        Subscript = 2,
    }

    /// <summary>
    /// The three item rules, in the order that makes each one's precondition hold.
    /// </summary>
    internal static ImmutableArray<Formula> RequireItems(
        ImmutableArray<Formula> items,
        string parameterName)
    {
        RequireBoundScripts(items, parameterName);
        RequireMacroArguments(items, parameterName);
        RequireScriptChains(items, parameterName);
        return items;
    }

    /// <summary>
    /// The applied function is emitted immediately before <c>\left(</c>, so a macro still
    /// waiting for its own argument would take that delimiter as its argument and KaTeX
    /// would refuse the formula ("Expected group as argument to '\operatorname'"). Name
    /// the operator first: <c>Seq(Operatorname, Grp(Id("NeZero")))</c>.
    /// </summary>
    internal static Formula RequireApplicableFunction(Formula function, string parameterName)
    {
        ArgumentNullException.ThrowIfNull(function, parameterName);
        if (function is Formula.LatexMacro macro && FormulaScriptAtom.TakesArgument(macro.Value))
        {
            throw new ArgumentException(
                "A LaTeX macro that takes an argument cannot be applied as a function; "
                    + "name it first, for example Seq(Operatorname, Grp(Id(\"f\"))).",
                parameterName);
        }

        return function;
    }

    /// <summary>
    /// A raw <c>^</c> or <c>_</c> binds exactly one following token, so its argument must
    /// emit exactly one. A wider argument either strands the macro that follows it
    /// (KaTeX: "Got function ... with no arguments as superscript") or silently drops its
    /// tail out of the script, and neither is detectable downstream of this rule.
    /// </summary>
    private static void RequireBoundScripts(ImmutableArray<Formula> items, string parameterName)
    {
        for (var index = 0; index < items.Length; index++)
        {
            if (items[index] is not Formula.LatexSymbol
                {
                    Value: FormulaLatexSymbol.Caret or FormulaLatexSymbol.Underscore,
                })
            {
                continue;
            }

            var argument = SkipDiscardedSpace(items, index + 1);
            if (argument >= items.Length || !FormulaScriptAtom.IsScriptArgument(items[argument]))
            {
                throw new ArgumentException(
                    "A LaTeX '^' or '_' binds exactly one token; wrap a wider script "
                        + "argument in a group.",
                    parameterName);
            }
        }
    }

    /// <summary>
    /// A macro that takes an argument binds the token that follows it, so it must be
    /// given one. Emitted bare it is stranded, and KaTeX refuses the whole formula.
    /// </summary>
    private static void RequireMacroArguments(
        ImmutableArray<Formula> items,
        string parameterName)
    {
        for (var index = 0; index < items.Length; index++)
        {
            if (items[index] is not Formula.LatexMacro macro
                || !FormulaScriptAtom.TakesArgument(macro.Value))
            {
                continue;
            }

            var argument = SkipDiscardedSpace(items, index + 1);
            if (argument >= items.Length || !FormulaScriptAtom.IsScriptArgument(items[argument]))
            {
                throw new ArgumentException(
                    "A LaTeX macro that takes an argument binds exactly one following "
                        + "token; give it a group.",
                    parameterName);
            }
        }
    }

    /// <summary>
    /// A TeX base carries one <c>^</c> and one <c>_</c>; scripting it a second time the
    /// same way is a parse error (KaTeX: "Double superscript"), not a nested script. The
    /// scripted base is usually a nested sequence — <c>Seq(Seq(T, Caret, Grp(Star)),
    /// Caret, Grp(k))</c> emits <c>T^{*}^{k}</c> — so the tail of each item decides, and
    /// a group is what closes a base and makes a second script legal.
    /// </summary>
    private static void RequireScriptChains(
        ImmutableArray<Formula> items,
        string parameterName) =>
        WalkScriptMarks(items, parameterName);

    private static ScriptMarks WalkScriptMarks(
        ImmutableArray<Formula> items,
        string parameterName)
    {
        var carried = ScriptMarks.None;
        for (var index = 0; index < items.Length; index++)
        {
            if (items[index] is Formula.LatexSpace or Formula.LatexNewline)
            {
                continue;
            }

            if (items[index] is not Formula.LatexSymbol
                {
                    Value: FormulaLatexSymbol.Caret or FormulaLatexSymbol.Underscore,
                } mark)
            {
                carried = TailScriptMarks(items[index], parameterName);
                continue;
            }

            var script = mark.Value == FormulaLatexSymbol.Caret
                ? ScriptMarks.Superscript
                : ScriptMarks.Subscript;
            if (carried.HasFlag(script))
            {
                throw new ArgumentException(
                    "A LaTeX base carries one '^' and one '_'; wrap a scripted base in a "
                        + "group before scripting it again.",
                    parameterName);
            }

            // RequireBoundScripts has already established that the argument is one token,
            // and one token cannot open a base of its own.
            index = SkipDiscardedSpace(items, index + 1);
            carried |= script;
        }

        return carried;
    }

    /// <summary>
    /// The script marks left exposed by the last token <paramref name="formula"/> emits.
    /// </summary>
    private static ScriptMarks TailScriptMarks(Formula formula, string parameterName) =>
        formula switch
        {
            // Braces close the base, which is why grouping is the stated remedy.
            Formula.LatexGroup => ScriptMarks.None,

            // Already validated by its own constructor, so this walk cannot throw.
            Formula.LatexSequence sequence => WalkScriptMarks(sequence.Items, parameterName),
            Formula.Layout layout => TailScriptMarks(layout.Content, parameterName),

            // The structured nodes that end in a script of their own.
            Formula.Power => ScriptMarks.Superscript,
            Formula.Subscript or Formula.Sequence => ScriptMarks.Subscript,

            // A node whose tail is decided by a sub-expression is left to the
            // emission-time check in LatexWriter, which reads the finished bytes.
            _ => ScriptMarks.None,
        };

    /// <summary>TeX discards the whitespace between a binder and its argument.</summary>
    private static int SkipDiscardedSpace(ImmutableArray<Formula> items, int index)
    {
        while (index < items.Length && items[index] is Formula.LatexSpace or Formula.LatexNewline)
        {
            index++;
        }

        return index;
    }
}

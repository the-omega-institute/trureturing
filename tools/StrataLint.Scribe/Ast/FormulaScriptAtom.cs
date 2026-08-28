using System.Diagnostics;

namespace StrataLint.Scribe;

/// <summary>
/// A <c>^</c> or <c>_</c> in a LaTeX token stream binds exactly one following token.
/// Anything wider must be wrapped in a group, otherwise the argument-taking macro that
/// follows loses its argument (KaTeX: "Got function '\operatorname@' with no arguments
/// as superscript") or the tail silently drops out of the script (<c>_alpha</c> renders
/// as <c>_{a}lpha</c>). The structured <see cref="Formula.Power"/> and
/// <see cref="Formula.Subscript"/> nodes emit their own braces and are unaffected; this
/// classification exists for the raw LaTeX escape hatch, where the author writes the
/// script mark by hand.
/// </summary>
internal static class FormulaScriptAtom
{
    /// <summary>Whether <paramref name="formula"/> emits exactly one LaTeX token.</summary>
    internal static bool IsScriptArgument(Formula formula) => formula switch
    {
        Formula.LatexGroup => true,
        Formula.LatexWord word => word.Value.Value.Length == 1,
        Formula.LatexDigits digits => digits.Digits.Length == 1,
        Formula.Number number => number.Value <= 9,
        Formula.LatexSymbol symbol => IsScriptArgument(symbol.Value),
        Formula.LatexMacro macro => IsScriptArgument(macro.Value),

        // Emitted as \varphi, \psi, \mathbb{Z} and \mathrm{name}: one token each.
        Formula.Phi or Formula.Psi or Formula.Integers or Formula.NamedConstant => true,

        // Everything else expands to a multi-token expression.
        _ => false,
    };

    /// <summary>
    /// Whether <paramref name="macro"/> binds exactly one following argument token.
    /// <c>\frac</c> is deliberately absent: it binds two, and <c>\frac12</c> spends a
    /// single digit pair on both, so a one-token rule would misjudge it.
    /// </summary>
    internal static bool TakesArgument(FormulaLatexMacro macro) => macro switch
    {
        FormulaLatexMacro.Begin
            or FormulaLatexMacro.End
            or FormulaLatexMacro.Mathbb
            or FormulaLatexMacro.Mathbf
            or FormulaLatexMacro.Mathcal
            or FormulaLatexMacro.Mathrm
            or FormulaLatexMacro.Operatorname
            or FormulaLatexMacro.Overline
            or FormulaLatexMacro.Sqrt
            or FormulaLatexMacro.Text
            or FormulaLatexMacro.Widehat
            or FormulaLatexMacro.Widetilde => true,

        // Every other macro is a symbol, an operator name, a delimiter mark or spacing:
        // it stands complete on its own and binds nothing.
        _ => false,
    };

    private static bool IsScriptArgument(FormulaLatexSymbol symbol) => symbol switch
    {
        // `&` is an alignment tab, `'` is a prime, and a script mark cannot carry
        // another script mark; KaTeX rejects all four in a script position.
        FormulaLatexSymbol.Ampersand
            or FormulaLatexSymbol.Apostrophe
            or FormulaLatexSymbol.Caret
            or FormulaLatexSymbol.Underscore => false,

        FormulaLatexSymbol.Exclamation
            or FormulaLatexSymbol.OpenParenthesis
            or FormulaLatexSymbol.CloseParenthesis
            or FormulaLatexSymbol.Asterisk
            or FormulaLatexSymbol.Plus
            or FormulaLatexSymbol.Comma
            or FormulaLatexSymbol.Minus
            or FormulaLatexSymbol.Period
            or FormulaLatexSymbol.Slash
            or FormulaLatexSymbol.Colon
            or FormulaLatexSymbol.Semicolon
            or FormulaLatexSymbol.LessThan
            or FormulaLatexSymbol.Equal
            or FormulaLatexSymbol.GreaterThan
            or FormulaLatexSymbol.OpenBracket
            or FormulaLatexSymbol.CloseBracket
            or FormulaLatexSymbol.VerticalBar => true,

        _ => throw new UnreachableException("Unclassified LaTeX symbol."),
    };

    private static bool IsScriptArgument(FormulaLatexMacro macro) => macro switch
    {
        // Measured against KaTeX by rendering `x^<macro><minimal legal argument>`: each
        // of these raises a parse error on the bare form and renders once grouped.
        // Operators and spacing macros are refused even though they take no argument.
        FormulaLatexMacro.Begin
            or FormulaLatexMacro.End
            or FormulaLatexMacro.Exp
            or FormulaLatexMacro.Gcd
            or FormulaLatexMacro.Iff
            or FormulaLatexMacro.Implies
            or FormulaLatexMacro.Ker
            or FormulaLatexMacro.Left
            or FormulaLatexMacro.Lim
            or FormulaLatexMacro.Log
            or FormulaLatexMacro.Max
            or FormulaLatexMacro.Middle
            or FormulaLatexMacro.Min
            or FormulaLatexMacro.NegativeThinSpace
            or FormulaLatexMacro.Operatorname
            or FormulaLatexMacro.Overline
            or FormulaLatexMacro.Prod
            or FormulaLatexMacro.Qquad
            or FormulaLatexMacro.Quad
            or FormulaLatexMacro.Right
            or FormulaLatexMacro.RowBreak
            or FormulaLatexMacro.SemicolonSpace
            or FormulaLatexMacro.Sin
            or FormulaLatexMacro.Sqrt
            or FormulaLatexMacro.Sum
            or FormulaLatexMacro.ThinSpace
            or FormulaLatexMacro.Widehat
            or FormulaLatexMacro.Widetilde => false,

        // Symbol macros, plus the argument-taking macros KaTeX permits in an argument
        // position (\frac, \mathbb, \mathbf, \mathcal, \mathrm, \text).
        FormulaLatexMacro.Delta
            or FormulaLatexMacro.Gamma
            or FormulaLatexMacro.Lambda
            or FormulaLatexMacro.Leftrightarrow
            or FormulaLatexMacro.Re
            or FormulaLatexMacro.Rightarrow
            or FormulaLatexMacro.Sigma
            or FormulaLatexMacro.Vert
            or FormulaLatexMacro.Alpha
            or FormulaLatexMacro.Beta
            or FormulaLatexMacro.Cdot
            or FormulaLatexMacro.Circ
            or FormulaLatexMacro.DeltaLower
            or FormulaLatexMacro.Ell
            or FormulaLatexMacro.Emptyset
            or FormulaLatexMacro.Equiv
            or FormulaLatexMacro.Exists
            or FormulaLatexMacro.Forall
            or FormulaLatexMacro.Frac
            or FormulaLatexMacro.GammaLower
            or FormulaLatexMacro.Ge
            or FormulaLatexMacro.Geq
            or FormulaLatexMacro.In
            or FormulaLatexMacro.Infty
            or FormulaLatexMacro.Int
            or FormulaLatexMacro.Iota
            or FormulaLatexMacro.Kappa
            or FormulaLatexMacro.LambdaLower
            or FormulaLatexMacro.Land
            or FormulaLatexMacro.Langle
            or FormulaLatexMacro.Le
            or FormulaLatexMacro.Leq
            or FormulaLatexMacro.Lfloor
            or FormulaLatexMacro.Longrightarrow
            or FormulaLatexMacro.Lor
            or FormulaLatexMacro.Lvert
            or FormulaLatexMacro.Mapsto
            or FormulaLatexMacro.Mathbb
            or FormulaLatexMacro.Mathbf
            or FormulaLatexMacro.Mathcal
            or FormulaLatexMacro.Mathrm
            or FormulaLatexMacro.Mid
            or FormulaLatexMacro.Mu
            or FormulaLatexMacro.Neg
            or FormulaLatexMacro.Neq
            or FormulaLatexMacro.Nu
            or FormulaLatexMacro.Omega
            or FormulaLatexMacro.Perp
            or FormulaLatexMacro.Phi
            or FormulaLatexMacro.Pi
            or FormulaLatexMacro.Pm
            or FormulaLatexMacro.Psi
            or FormulaLatexMacro.Rangle
            or FormulaLatexMacro.Rfloor
            or FormulaLatexMacro.Rho
            or FormulaLatexMacro.Rvert
            or FormulaLatexMacro.Setminus
            or FormulaLatexMacro.SigmaLower
            or FormulaLatexMacro.Sim
            or FormulaLatexMacro.Subset
            or FormulaLatexMacro.Subseteq
            or FormulaLatexMacro.Tau
            or FormulaLatexMacro.Text
            or FormulaLatexMacro.Theta
            or FormulaLatexMacro.Times
            or FormulaLatexMacro.To
            or FormulaLatexMacro.Varepsilon
            or FormulaLatexMacro.Varnothing
            or FormulaLatexMacro.Varphi
            or FormulaLatexMacro.Xi
            or FormulaLatexMacro.Zeta
            or FormulaLatexMacro.EscapedSpace
            or FormulaLatexMacro.OpenBrace
            or FormulaLatexMacro.CloseBrace => true,

        _ => throw new UnreachableException("Unclassified LaTeX macro."),
    };
}

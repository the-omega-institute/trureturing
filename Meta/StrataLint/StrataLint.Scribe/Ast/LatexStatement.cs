using System.Text.RegularExpressions;

namespace StrataLint.Scribe;

public sealed record LatexStatement
{
    private static readonly Regex EnvironmentPattern = new(
        "\\\\(?<operation>begin|end)\\{(?<name>[A-Za-z]+\\*?)\\}",
        RegexOptions.CultureInvariant);

    private static readonly HashSet<string> AllowedMacros = new(StringComparer.Ordinal)
    {
        "Alpha", "Beta", "Chi", "Delta", "Epsilon", "Eta", "Gamma", "Iota",
        "Kappa", "Lambda", "Mu", "Nu", "Omega", "Omicron", "Phi", "Pi", "Psi",
        "Re", "Rho", "Sigma", "Tau", "Theta", "Upsilon", "Xi", "Zeta",
        "alpha", "beta", "chi", "delta", "epsilon", "eta", "gamma", "iota",
        "kappa", "lambda", "mu", "nu", "omega", "omicron", "phi", "pi", "psi",
        "rho", "sigma", "tau", "theta", "upsilon", "varepsilon", "varphi", "varrho",
        "varsigma", "vartheta", "xi", "zeta",
        "Im", "Pr", "abs", "arg", "arccos", "arcsin", "arctan", "cos", "cosh",
        "cot", "coth", "csc", "deg", "det", "dim", "exp", "gcd", "hom", "inf",
        "ker", "lg", "lim", "liminf", "limsup", "ln", "log", "max", "min", "mod",
        "operatorname", "sec", "sin", "sinh", "sup", "tan", "tanh",
        "begin", "end", "frac", "sqrt", "text", "mathrm", "mathbf", "mathbb",
        "mathcal", "mathfrak", "mathit", "mathsf", "mathtt", "boldsymbol",
        "left", "right", "middle", "langle", "rangle", "lbrace", "rbrace", "lvert",
        "rvert", "lfloor", "rfloor", "lceil", "rceil", "vert", "Vert", "mid",
        "overline", "underline", "bar", "hat", "widehat", "tilde", "widetilde", "vec",
        "dot", "ddot", "overset", "underset", "underbrace", "overbrace",
        "cdot", "circ", "ast", "star", "times", "div", "pm", "mp", "oplus",
        "ominus", "otimes", "oslash", "odot", "cap", "cup", "sqcap", "sqcup",
        "wedge", "vee", "setminus", "wr",
        "le", "leq", "ge", "geq", "neq", "equiv", "approx", "sim", "simeq",
        "cong", "propto", "in", "notin", "ni", "subset", "subseteq", "supset",
        "supseteq", "parallel", "perp", "models", "vdash", "dashv",
        "to", "mapsto", "gets", "leftrightarrow", "Rightarrow", "Leftarrow",
        "Leftrightarrow", "implies", "iff", "hookrightarrow", "longrightarrow",
        "longmapsto", "uparrow", "downarrow",
        "sum", "prod", "coprod", "int", "iint", "iiint", "oint", "bigcap", "bigcup",
        "bigoplus", "bigotimes", "partial", "nabla", "infty", "forall", "exists",
        "neg", "land", "lor", "top", "bot", "emptyset", "varnothing", "ell", "hbar",
        "prime", "angle", "triangle", "square", "Box", "Diamond",
        "quad", "qquad", ",", ";", ":", "!", " ", "\\", "{", "}", "|",
    };

    private static readonly HashSet<string> AllowedEnvironments = new(StringComparer.Ordinal)
    {
        "aligned", "alignedat", "array", "bmatrix", "cases", "gathered", "matrix",
        "pmatrix", "smallmatrix", "split", "vmatrix", "Vmatrix",
    };

    private LatexStatement(string value) => Value = value;

    public string Value { get; }

    public static LatexStatement Create(string value)
    {
        ArgumentNullException.ThrowIfNull(value);
        Validate(value);
        return new LatexStatement(value);
    }

    public override string ToString() => Value;

    private static void Validate(string value)
    {
        if (value.Length == 0
            || !string.Equals(value, value.Trim(), StringComparison.Ordinal)
            || value.Contains('\r')
            || value.Contains('%')
            || value.Contains('#'))
        {
            throw Invalid();
        }

        var delimiterLength = value.StartsWith("$$", StringComparison.Ordinal) ? 2 : 1;
        var delimiter = delimiterLength == 2 ? "$$" : "$";
        if (!value.StartsWith(delimiter, StringComparison.Ordinal)
            || !value.EndsWith(delimiter, StringComparison.Ordinal)
            || value.Length <= delimiterLength * 2)
        {
            throw Invalid();
        }

        var body = value[delimiterLength..^delimiterLength];
        if (string.IsNullOrWhiteSpace(body) || body.Contains('$'))
        {
            throw Invalid();
        }

        ValidateBraces(body);
        ValidateMacros(body);
        ValidateEnvironments(body);
    }

    private static void ValidateBraces(string body)
    {
        var depth = 0;
        for (var index = 0; index < body.Length; index++)
        {
            if (body[index] is not ('{' or '}') || IsEscaped(body, index))
            {
                continue;
            }

            depth += body[index] == '{' ? 1 : -1;
            if (depth < 0)
            {
                throw Invalid();
            }
        }

        if (depth != 0)
        {
            throw Invalid();
        }
    }

    private static void ValidateMacros(string body)
    {
        for (var index = 0; index < body.Length; index++)
        {
            if (body[index] != '\\')
            {
                continue;
            }

            if (++index >= body.Length)
            {
                throw Invalid();
            }

            var start = index;
            if (char.IsAsciiLetter(body[index]))
            {
                while (index + 1 < body.Length && char.IsAsciiLetter(body[index + 1]))
                {
                    index++;
                }
            }

            var macro = body[start..(index + 1)];
            if (!AllowedMacros.Contains(macro))
            {
                throw new ArgumentException($"LaTeX statement uses unsupported macro \\{macro}.");
            }
        }
    }

    private static void ValidateEnvironments(string body)
    {
        var environments = new Stack<string>();
        foreach (Match match in EnvironmentPattern.Matches(body))
        {
            var name = match.Groups["name"].Value;
            if (!AllowedEnvironments.Contains(name))
            {
                throw new ArgumentException($"LaTeX statement uses unsupported environment {name}.");
            }

            if (match.Groups["operation"].Value == "begin")
            {
                environments.Push(name);
            }
            else if (environments.Count == 0 || environments.Pop() != name)
            {
                throw Invalid();
            }
        }

        if (environments.Count != 0)
        {
            throw Invalid();
        }
    }

    private static bool IsEscaped(string value, int index)
    {
        var slashes = 0;
        while (index > 0 && value[--index] == '\\')
        {
            slashes++;
        }
        return slashes % 2 != 0;
    }

    private static ArgumentException Invalid() =>
        new("LaTeX statement must be non-empty, canonically $-delimited, and balanced.");
}

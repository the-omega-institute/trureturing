using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class PrefixCylinderDensityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/PrefixCylinderDensity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed Zeckendorf prefixes have bounded counting discrepancy and positive density.",
        H("Natural Density of Canonical Fibonacci Prefixes"),
        Blocks(
            Node("legal-prefix", "Legal occupied prefix indices", "LegalPrefix",
                Disp(Seq(Call("LegalPrefix", F.Id("m"), F.Id("w")), Leftrightarrow,
                    Call("IsZeckendorfRep", F.Id("w")), Land, Forall, Sp, F.Id("k"),
                    InMacro, Sp, F.Id("w"), Comma, F.Id("k"), Lt, F.Id("m"), Plus, D(2))),
                "A prefix of length m is represented by its descending list w of occupied "
                    + "Fibonacci indices. All indices are at least two, successive occupied "
                    + "indices differ by at least two, and every index is less than m+2. "
                    + "Index j+2 is the low-first binary digit j. The length retains high zero "
                    + "digits, including the empty prefix at m=0.", DescribeRole.Definition),
            Node("seam-depth", "The seam-adjusted free tail depth", "seamDepth",
                Disp(Equal(F.Id("h"), Seq(F.Id("m"), Plus, F.Id("sigma")))),
                "Write sigma=1 when m+1 belongs to w, and sigma=0 otherwise; h=m+sigma. "
                    + "Thus an occupied final prefix digit forces one extra zero before the "
                    + "free tail. The value of the fixed prefix is V=sum over k in w of F_k.",
                DescribeRole.Definition),
            Node("cylinder", "The canonical integer cylinder", "cylinder",
                Disp(Equal(Call("C", F.Id("m"), F.Id("w")),
                    Seq(OpenBrace, F.Id("n"), InMacro, Seq(Mathbb, Grp(F.Id("N"))), Mid,
                        Call("filter", Seq(F.Id("k"), Lt, F.Id("m"), Plus, D(2)),
                            Call("wdigits", F.Id("n"))), Eq, F.Id("w"), CloseBrace))),
                "C(m,w) consists of the natural integers whose canonical occupied indices "
                    + "below m+2 are exactly w. All higher digits are read with zero padding. "
                    + "The Fibonacci convention is F_0=0 and F_1=1.", DescribeRole.Definition),
            Node("counting", "Counting below a real cutoff", "counting",
                Disp(Equal(Call("N", F.Id("m"), F.Id("w"), F.Id("X")),
                    Abs(Seq(OpenBrace, F.Id("n"), InMacro, Call("C", F.Id("m"), F.Id("w")),
                        Mid, Sp, F.Id("n"), Lt, F.Id("X"), CloseBrace)))),
                "N(m,w,X) counts cylinder members n with n<X, where X is any real number. "
                    + "The set is finite and empty when X is nonpositive.", DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("prefix-cylinder-density"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Bounded discrepancy, natural density, and refinement ratios"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every legal prefix (m,w), the map t to V+s^h(t) is "
                        + "strictly increasing and has image C(m,w), where s shifts every "
                        + "occupied Fibonacci index up by one. In particular t=0 is retained.")),
                    Paragraph(Text("There is a real constant C depending only on this prefix "
                        + "such that, for every real X>=0, |N(m,w,X)-phi^(-h)X|<=C. "
                        + "As X tends to positive infinity through real cutoffs, N(m,w,X)/X "
                        + "tends to phi^(-h), which is positive.")),
                    Paragraph(Text("For every legal longer prefix (m',w') with m<=m' and "
                        + "w' restricted below m+2 equal to w, its counting ratio "
                        + "N(m',w',X)/N(m,w,X) tends to phi^(h-h'). If m'=m+r and its "
                        + "last digit is tau, this exponent is -(r+tau-sigma). When r=0, "
                        + "tau=sigma and the ratio tends to one.")),
                    Paragraph(Text("Zeckendorf uniqueness identifies the free tail after "
                        + "the fixed prefix and the forced seam zero are removed. The golden "
                        + "Beatty floor formula for s gives |s(t)-phi*t|<=1. Iteration gives "
                        + "|s^h(t)-phi^h*t|<=h*phi^h. The first tail index whose image reaches "
                        + "X is exactly the cylinder count. Its image and its predecessor "
                        + "bound that count within a constant of X/phi^h. Dividing by X "
                        + "gives the density, and dividing the two positive density limits "
                        + "gives the refinement ratio.")),
                    Paragraph(Text("This is a result in the classical Zeckendorf and golden "
                        + "Beatty setting. Background on the unique nonconsecutive expansion "
                        + "is J. L. Brown, Jr., Zeckendorf's Theorem and Some Applications, "
                        + "The Fibonacci Quarterly 2 (1964), 163-168. "
                        + "The error bound is for each fixed prefix; it is not uniform over "
                        + "all prefix lengths. No composition-coordinate lifting formula "
                        + "or specific three-digit or six-digit weight table is asserted."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Pow(Formula b, Formula e) => new Formula.Power(b, e);
    private static Formula Abs(Formula x) => Seq(Lvert, x, Rvert);
    private static Formula Limit(Formula x, Formula target, Formula value) =>
        Seq(new Formula.Subscript(F.Lim, Seq(x, To, target)), value);

    private static Formula ResultFormula()
    {
        var x = F.Id("X"); var h = F.Id("h"); var hp = F.Id("hPrime");
        Formula n = Call("N", F.Id("m"), F.Id("w"), x);
        Formula np = Call("N", F.Id("mPrime"), F.Id("wPrime"), x);
        return Disp(Seq(Forall, Sp, F.Id("m"), Comma, F.Id("w"), Comma,
            Call("LegalPrefix", F.Id("m"), F.Id("w")), Rightarrow,
            Call("StrictMono", Seq(F.Id("t"), Mapsto, Sp, F.Id("V"), Plus,
                Seq(Pow(F.Id("s"), h), Open, F.Id("t"), Close))), Land,
            Call("range", Seq(F.Id("t"), Mapsto, Sp, F.Id("V"), Plus,
                Seq(Pow(F.Id("s"), h), Open, F.Id("t"), Close))), Eq,
            Call("C", F.Id("m"), F.Id("w")), Land,
            Exists, Sp, F.Id("C"), Comma, Forall, Sp, x, Ge, D(0), Comma,
            Abs(Seq(n, Minus, Pow(Varphi, Seq(Minus, h)), Cdot, Sp, x)), Le, Sp, F.Id("C"), Land,
            Limit(x, Infty, new Formula.Fraction(n, x)), Eq, Pow(Varphi, Seq(Minus, h)), Land,
            Forall, Sp, F.Id("mPrime"), Comma, F.Id("wPrime"), Comma,
            Call("LegalExtension", F.Id("m"), F.Id("w"), F.Id("mPrime"), F.Id("wPrime")),
            Rightarrow, Limit(x, Infty, new Formula.Fraction(np, n)), Eq,
            Pow(Varphi, Seq(h, Minus, hp))));
    }
}

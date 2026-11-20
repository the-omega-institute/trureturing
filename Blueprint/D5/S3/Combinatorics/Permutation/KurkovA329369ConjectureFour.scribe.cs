using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permutation;

internal sealed class KurkovA329369ConjectureFourDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Permutation/KurkovA329369ConjectureFour";
    private static readonly LibraryNoteRef Excedances =
        LibraryNoteRef.Create("D5/L/Arith/oeis2024a329369");
    private static readonly LibraryNoteRef Coefficients =
        LibraryNoteRef.Create("D5/L/Digit/kurkov2024a358612");

    private static Formula W => F.Id("w");
    private static Formula N => F.Id("n");
    private static Formula J => F.Id("j");
    private static Formula M => F.Id("m");
    private static Formula K => F.Id("k");
    private static Formula I => F.Id("i");
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Rationals => Seq(Mathbb, Grp(F.Id("Q")));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Kurkov's signed factorial-power formula for the exact strict-excedance count.",
        H("OEIS A329369 Conjecture 4"),
        Blocks(
            Node("binary-excedances", "binaryExcedances", "The prescribed excedance set",
                ExcedanceFormula(), DescribeRole.Definition, AssessedProvenance.FromLiterature(Excedances),
                "The width w counts binary positions. There are w+1 permutation positions, "
                + "numbered from zero. For j below w, bit w−1−j fixes whether j is a strict "
                + "excedance. In the one-based OEIS wording, M=w+1 and j+1=M−i, "
                + "so this is bit i−1. The final position cannot be a strict excedance."),
            Node("padded-count", "paddedCount", "The number of actual permutations",
                CountFormula(), DescribeRole.Definition, AssessedProvenance.FromLiterature(Excedances),
                "The count is the finite cardinality of the permutations whose complete strict "
                + "excedance set is the prescribed set. The width is admissible when n<2^w."),
            Node("conjecture-four", "conjecture4", "The signed factorial-power identity",
                IdentityFormula(), DescribeRole.Theorem, AssessedProvenance.FromRepo(Excedances, Coefficients),
                "Here wt is the binary popcount and T is the literal rational array A358612, "
                + "revision 52. Equality is over the rationals and the sign exponent is an integer. "
                + "The source uses exponent wt(k)−i in A329369 revision 239 and adds two in A358612. "
                + "These exponents give the same sign, including at the two highest columns.",
                "A prepended zero forces the first position and value to agree, so deleting both "
                + "preserves the cardinality. The all-zero word consequently has the identity "
                + "as its unique permutation. A trailing one forces the greatest value at the "
                + "penultimate position, which gives the odd step by deletion. For a positive "
                + "even step, apply Ehrenborg and Steingrímsson's adjacent swap and two deletion "
                + "identity at the lowest one and the next zero. If r is the two-adic valuation "
                + "of n, the three terms for 2n have indices 2n−2^r, n and n−2^r. Their widths "
                + "are respectively w+1, w and w when 2n uses width w+1. The guard on each "
                + "recursive call follows from these indices. Strong induction identifies the "
                + "count with the row polynomial evaluated at one for every admissible width. "
                + "The bracket identities are Proposition 2.1 and Lemma 2.3 of "
                + "The excedance set of a permutation, DOI 10.1006/aama.1999.0671.",
                "The literal A358612 coefficient theorem gives the ascending Pochhammer "
                + "coordinates of x R(k,x), including the initial row. The index 2k+1 "
                + "starts at this polynomial. Each doubling multiplies its coordinate "
                + "in degree i by i, and evaluation at one gives i factorial. The zero-fold "
                + "iteration covers m=0, and the initial row gives the two terms at k=0."))));

    private static DocumentBlock Node(string id, string declaration, string title, Formula formula,
        DescribeRole role, AssessedProvenance provenance, params string[] paragraphs) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration), H(title),
        StatementSource.FromAuthor(Disp(formula)), provenance,
        Blocks(paragraphs.Select(p => Paragraph(Text(p))).ToArray()), role);

    private static Formula ExcedanceFormula() => Seq(NatBind(W, N),
        Call("binaryExcedances", W, N), Sp, Eq, Sp, OpenBrace, Sp,
        J, Colon, Sp, FinSize(), Sp, Mid, Sp,
        J, Sp, Lt, Sp, W, Sp, Land, Sp,
        Call("testBit", N, Seq(W, Minus, D(1), Minus, J)), Sp, Eq, Sp,
        Mathrm, Grp(F.Id("true")), Sp, CloseBrace);

    private static Formula CountFormula() => Seq(NatBind(W, N),
        Call("paddedCount", W, N), Sp, Eq, Sp, Left, Lvert, OpenBrace, Sp,
        F.Id("p"), Colon, Sp, Call("Perm", FinSize()), Sp, Mid, Sp,
        Forall, Sp, J, Colon, Sp, FinSize(), Comma, Sp,
        J, Sp, Lt, Sp, Call("p", J), Sp, Iff, Sp, J, Sp, InMacro, Sp,
        Call("binaryExcedances", W, N), Sp, CloseBrace, Right, Rvert);

    private static Formula IdentityFormula()
    {
        var weight = Call("wt", K);
        var index = Seq(Pow(D(2), M), Sp, Cdot, Sp, Parens(Seq(D(2), Sp, Cdot, Sp, K, Plus, D(1))));
        var sign = Pow(Parens(Seq(Minus, D(1))), Seq(Typed(weight, Integers), Minus,
            Typed(I, Integers)));
        return Seq(NatBind(M, K, W), index, Sp, Lt, Sp, Pow(D(2), W), Sp, Implies, Sp,
            Typed(Call("paddedCount", W, index), Rationals), Sp, Eq, Sp,
            new Formula.Subscript(Sum, Grp(Seq(D(1), Sp, Le, Sp, I, Sp, Le, Sp, weight, Plus, D(2)))),
            Sp, Typed(Seq(I, Bang), Rationals), Sp, Cdot, Sp, Pow(Typed(I, Rationals), M),
            Sp, Cdot, Sp, Call("T", K, I), Sp, Cdot, Sp, sign);
    }

    private static Formula FinSize() => Call("Fin", Seq(W, Plus, D(1)));
    private static Formula NatBind(params Formula[] names) => Seq(Forall, Sp,
        Seq(names.SelectMany((name, i) => i == 0 ? new[] { name } : new[] { Comma, Sp, name }).ToArray()),
        Sp, InMacro, Sp, Naturals, Comma, Sp);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);

    private static Formula Typed(Formula value, Formula type) => Parens(Seq(value, Colon, Sp, type));
    private static Formula Parens(Formula value) => Seq(Open, value, Close);
    private static Formula Pow(Formula b, Formula e) => new Formula.Power(b, e);
}

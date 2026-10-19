using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Hamming;

internal sealed class AtashpendarKappaAlternatingRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Hamming/AtashpendarKappaAlternatingRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/atashpendar2018deletionentropy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A period-six binary word has smaller positional autocorrelation than the alternating word at length 348.",
        H("Alternating words need not minimize positional autocorrelation"),
        Blocks(
            Paragraph(Text("Equation (11) of arXiv:1807.11609v1, p. 7, defines the natural-number "
                + "coefficient κ²(x) = Σ₁≤ᵣ,ₛ≤ₘ C(r+s−2,r−1) C(2m−r−s,m−r) [[xᵣ=xₛ]]. "
                + "Here positions are Fin m, with val taking values from zero to m minus one. "
                + "Bool.true represents 1 and Bool.false represents 0. Natural subtraction truncates "
                + "at zero; the binomial arguments are nonnegative for these positions. The percent "
                + "operator is natural remainder. Each ordered pair of positions is counted once.")),
            Node("claim", "The alternating-minimizer conjecture",
                Disp(Equal(F.Id("claim"), Parenthesized(ClaimBody()))),
                "Conjecture IV.4, p. 7: “The alternating subsequence of length m, i.e., x = 1010..., "
                + "minimizes the autocorrelation coefficient κ².” For every positive natural length "
                + "m, the formula compares the coefficient of 1010... with that of every binary word "
                + "x of length m. Its two sums are Equation (11), with the source positions shifted "
                + "down by one. The first word has true at precisely the even zero-based positions.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "A strict counterexample at length 348",
                Disp(Seq(Neg, Sp, Parenthesized(ClaimBody()))),
                "At length 348, the word (011001) repeated 58 times has strictly smaller coefficient "
                + "than 1010.... The natural difference, alternating minus period-six, is "
                + "72205957507799609560655006349961851153741188979911147028434625522749530872921557830312745632696473970699075168094975823625414930530038291298408559098670303166362893884742404955920795949372113567213277960. "
                + "A finite factorial table computes the two binomial factors. Each of the 348 row "
                + "sums is checked for both words, in 29 groups of 12 rows, and their totals give "
                + "this positive difference. The calculation proves the displayed negation. It "
                + "does not determine the smallest counterexample length, the minimizers at other "
                + "lengths, or an entropy ordering.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("kappa-alternating-" + name),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula NatType() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Word(Formula m) => new Formula.TypeArrow(Call("Fin", m), Named("Bool"));
    private static Formula Qualified(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Seq(Named(owner), Dot, Named(name)), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Parity(Formula index) =>
        Call("decide", Equal(new Formula.Modulo(Call("val", index), D(2)), D(0)));

    private static Formula Coefficient(Formula m, bool alternating)
    {
        Formula r = F.Id("r"), s = F.Id("s");
        Formula rv = Call("val", r), sv = Call("val", s);
        Formula same = alternating
            ? Equal(Parenthesized(Seq(Parity(r), Colon, Sp, Named("Bool"))), Parity(s))
            : Equal(Call("x", r), Call("x", s));
        Formula weight = Multiply(Qualified("Nat", "choose", Add(rv, sv), rv),
            Qualified("Nat", "choose", Subtract(Subtract(Subtract(Multiply(D(2), m), D(2)), rv), sv),
                Subtract(Subtract(m, D(1)), rv)));
        Formula term = Parenthesized(Seq(Named("if"), Sp, same, Sp, Named("then"), Sp, weight,
            Sp, Named("else"), Sp, D(0)));
        return Parenthesized(Seq(Sum, Underscore, Grp(r, Colon, Sp, Call("Fin", m)), Sp,
            Sum, Underscore, Grp(s, Colon, Sp, Call("Fin", m)), Sp, term));
    }

    private static Formula ClaimBody()
    {
        Formula m = F.Id("m");
        Formula comparison = Seq(Coefficient(m, true), Sp, Le, Sp, Coefficient(m, false));
        return All("m", NatType(), Seq(D(1), Sp, Le, Sp, m, Sp, Rightarrow, Sp,
            Parenthesized(All("x", Word(m), comparison))));
    }
}

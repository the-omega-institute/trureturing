using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class PellCompanionGcdDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/PellCompanionGcd.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/oeis2025a084068");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coprimality and oddness of companion Pell numbers prove the gcd formula in OEIS A084068.",
        H("Pell and Companion Pell Gcd"),
        Blocks(
            Paragraph(Text("All indices and sequence values are natural numbers. "
                + "The companion convention is Q(0)=Q(1)=1. OEIS A084068 records "
                + "Joseph A. Stocke's July 28, 2025 conjecture that its n-th term equals "
                + "gcd(A001108(n), A001109(n)), for n at least one.")),
            Node("P", "Pell numbers", Recurrence("P", D(0)),
                "These are the Pell numbers A000129, beginning 0, 1, 2, 5, 12.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("Q", "Companion Pell numbers", Recurrence("Q", D(1)),
                "These are the companion Pell numbers A001333, beginning 1, 1, 3, 7, 17.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("pell_companion_step", "The coupled recurrence", StepFormula(),
                "Induct on n. The initial pair gives the base case. Substitute the two "
                + "second-order recurrences at n+2 and the two induction identities; "
                + "both equalities follow by addition. The same coupled recurrence is "
                + "recorded in the Stephenson and Koch comment on A001108.",
                DescribeRole.Lemma, AssessedProvenance.FromLiterature(Source)),
            Node("pell_companion_coprime", "Coprimality at every index",
                Universal(Seq(Call("gcd", P(), Q()), Sp, Eq, Sp, D(1))),
                "The initial pair (0,1) is coprime. The coupled step sends (p,q) to "
                + "(p+q,2p+q). Subtracting the first coordinate from the second, and "
                + "then p from p+q, shows gcd(p+q,2p+q)=gcd(q,p). Induction gives "
                + "coprimality for every index.", DescribeRole.Lemma,
                AssessedProvenance.FromRepo(Source)),
            Node("companion_odd", "Oddness at every index",
                Universal(Seq(Exists, Sp, F.Id("k"), Sp, InMacro, Sp, Naturals(), Comma, Sp,
                    Q(), Sp, Eq, Sp, D(2), Sp, Cdot, Sp, F.Id("k"), Plus, D(1))),
                "Q(0)=1 is odd. If Q(n)=2k+1, then Q(n+1)=2P(n)+Q(n) "
                + "equals 2(P(n)+k)+1, so the next value is odd too.",
                DescribeRole.Lemma, AssessedProvenance.FromRepo(Source)),
            Node("pell_companion_gcd", "The A084068 gcd formula", GcdFormula(),
                "For even n, extract P(n) from both gcd arguments. Since Q(n) is "
                + "odd, it is coprime to 2; since it is coprime to P(n), it is "
                + "coprime to 2P(n). The remaining gcd is therefore 1. For odd n, "
                + "extract Q(n); the remaining gcd is gcd(Q(n),P(n))=1. "
                + "A001108 gives the first gcd argument by parity, A001109 gives "
                + "the product P(n)Q(n), and A084068 gives P(n) at even indices "
                + "and Q(n) at odd indices. Thus this proves the conjecture at every "
                + "positive index; the displayed equality also holds at zero.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a084068-pell-companion-gcd"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("pell-gcd-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula N() => F.Id("n");
    private static Formula P() => Call("P", N());
    private static Formula Q() => Call("Q", N());
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Named(name), [.. args]);
    private static Formula Add(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Mul(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Square(Formula x) => new Formula.Power(x, D(2));
    private static Formula Bound() =>
        Seq(Forall, Sp, N(), Sp, InMacro, Sp, Naturals(), Comma, Sp);
    private static Formula Universal(Formula body) => Disp(Seq(Bound(), body));

    private static Formula Recurrence(string name, Formula initial) =>
        Disp(new Formula.Aligned([
            Seq(Call(name, D(0)), Sp, Eq, Sp, initial, Comma, Sp,
                Call(name, D(1)), Sp, Eq, Sp, D(1), Comma),
            Seq(Bound(), Call(name, Add(N(), D(2))), Sp, Eq, Sp,
                Add(Mul(D(2), Call(name, Add(N(), D(1)))), Call(name, N())))
        ]));

    private static Formula StepFormula() => Universal(Seq(
        Call("P", Add(N(), D(1))), Sp, Eq, Sp, Add(P(), Q()), Sp, Land, Sp,
        Call("Q", Add(N(), D(1))), Sp, Eq, Sp, Add(Mul(D(2), P()), Q())));

    private static Formula Choice(Formula even, Formula odd) => Seq(
        Named("if"), Sp, D(2), Sp, Mid, Sp, N(), Sp, Named("then"), Sp, even,
        Sp, Named("else"), Sp, odd);

    private static Formula GcdFormula() => Disp(new Formula.Aligned([
        Bound(),
        Seq(Call("gcd", Choice(Mul(D(2), Square(P())), Square(Q())), Mul(P(), Q())),
            Sp, Eq, Sp, Choice(P(), Q()))
    ]));
}

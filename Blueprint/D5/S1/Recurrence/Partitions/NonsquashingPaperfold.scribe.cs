using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Partitions;

internal sealed class NonsquashingPaperfoldDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Partitions/NonsquashingPaperfold.";
    private static readonly LibraryNoteRef Paper = LibraryNoteRef.Create("D5/L/Words/sloane2003nonsquashing");
    private static readonly LibraryNoteRef Oeis = LibraryNoteRef.Create("D5/L/Words/oeis2025a110037");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The signed parity of distinct non-squashing partitions equals the adjacent difference of A073089.",
        H("Non-Squashing Parity and a Paperfold Difference"),
        Blocks(
            Paragraph(Text("Let B(n) be the cardinality of nonsquashingDistinctPartitions(n), "
                + "the direct finite family in NonsquashingCounting. Let c(n) denote paperfoldVariant(n). "
                + "All indices are natural numbers. The final equality is in the integers; "
                + "B(n) mod 2 is computed in the naturals before casting. No finite cutoff is used.")),
            Node("paperfoldVariant", "The independent paperfold recurrence", Definition(),
                "This is OEIS A073089's branch recurrence. The helper ite selects its second "
                + "argument when the condition holds and its third otherwise. At indices zero and "
                + "one the value is zero; zero only totalizes the source's offset-one sequence. "
                + "The remaining recursive branch halves n+1 and strictly decreases n. "
                + "It does not use B or the desired difference identity.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Oeis)),
            Node("SloaneSellersParity", "The eight parity conditions", ParityDefinition(),
                "For any natural-valued sequence F, Parity(F) denotes these eight quantified "
                + "conditions. Every unqualified m ranges over all natural numbers; the odd "
                + "and sixteen-zero clauses require m>0. The two thirty-two clauses include m=0.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Paper)),
            Node("sloane_sellers_parity", "The conditions hold for the direct count",
                Disp(Call("Parity", V("B"))),
                "The maximum-part bijection gives the exact count recurrence. Pairing two "
                + "successive even steps with the odd increment proves, by induction, "
                + "B(4m+2) mod 2=(m+1) mod 2. One more even step gives "
                + "B(4m) mod 2=(m+B(2m)) mod 2 for m>0. Substituting the appropriate "
                + "indices yields all eight clauses, including the small boundaries.", DescribeRole.Theorem,
                AssessedProvenance.FromLiterature(Paper)),
            Node("signed_nonsquashing_diff", "The A110037 difference conjecture", MainFormula(),
                "Put f(r)=B(4r) mod 2. The parity clauses give f(2r)=f(r) for positive r, "
                + "f(4s+1)=0, and f(4s+3)=1. Strong induction, using the independent "
                + "paperfold branches, proves f(r)+c(4r+1)=1 for every r>0. "
                + "For n congruent to zero or one modulo four this complement identity "
                + "gives the difference. For the other two residues the eight-index parity "
                + "clauses and the c(8s+3), c(8s+7) branches suffice. The sign is positive "
                + "in the first two residues and negative in the last two. This proves the "
                + "conjecture credited to Alan Michael Gómez Calderón on August 19, 2025, "
                + "throughout its stated domain n>=2.", DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Oeis, Paper)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance source) => Describe.Lean(
        DescribeId.Create("nonsquashing-paperfold-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        source, Blocks(Paragraph(Text(prose))), role);
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Eqn(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Mod(Formula x, Formula d) => new Formula.Modulo(x, d);
    private static Formula Half(Formula x) => new Formula.Floor(new Formula.Fraction(x, D(2)));
    private static Formula C(Formula x) => Call("c", x);
    private static Formula NatBound(string x) => Seq(Forall, Sp, V(x), Colon, Sp, Mathbb, Grp(V("N")), Comma, Sp);
    private static Formula If(Formula p, Formula x, Formula y) => Call("ite", p, x, y);
    private static Formula Case(int modulus, int residue, int value, Formula rest) =>
        If(Eqn(Mod(V("n"), Number(modulus)), Number(residue)), Number(value), rest);
    private static Formula Number(int n) => n switch
    {
        0 => D(0), 1 => D(1), 2 => D(2), 3 => D(3), 4 => D(4), 5 => D(5), 6 => D(6),
        7 => D(7), 8 => D(8), 12 => D(1, 2), 13 => D(1, 3), 16 => D(1, 6),
        24 => D(2, 4), 32 => D(3, 2),
        _ => throw new System.ArgumentOutOfRangeException(nameof(n)),
    };
    private static Formula Definition() => Disp(Seq(NatBound("n"), Eqn(C(V("n")),
        If(Seq(V("n"), Sp, Leq, Sp, D(1)), D(0),
            Case(4, 0, 1, Case(4, 2, 0, Case(8, 3, 1, Case(8, 7, 0,
                Case(16, 5, 1, Case(16, 13, 0, C(Half(Add(V("n"), D(1))))))))))))));
    private static Formula FAt(int a, int b) => Call("F", Add(Mul(Number(a), V("m")), Number(b)));
    private static Formula Clause(int a, int b, Formula value, bool positive = false) => Seq(
        NatBound("m"), positive ? Seq(D(0), Sp, Lt, Sp, V("m"), Sp, Rightarrow, Sp) : Sp,
        Eqn(Mod(FAt(a, b), D(2)), value));
    private static Formula ParityDefinition() => Disp(new Formula.Aligned([
        Seq(Call("Parity", V("F")), Sp, Iff),
        Par(Clause(2, 1, Mod(Add(Mod(FAt(2, 0), D(2)), D(1)), D(2)), true)),
        Seq(Land, Sp, Par(Clause(8, 2, D(1)))), Seq(Land, Sp, Par(Clause(8, 6, D(0)))),
        Seq(Land, Sp, Par(Clause(16, 4, D(0)))), Seq(Land, Sp, Par(Clause(16, 12, D(1)))),
        Seq(Land, Sp, Par(Clause(16, 0, Mod(FAt(8, 0), D(2)), true))),
        Seq(Land, Sp, Par(Clause(32, 8, D(0)))), Seq(Land, Sp, Par(Clause(32, 24, D(1)))),
    ]));
    private static Formula MainFormula() => Disp(Seq(NatBound("n"), D(2), Sp, Leq, Sp, V("n"),
        Sp, Rightarrow, Sp, Eqn(Mul(new Formula.Power(Par(Sub(D(0), D(1))), Half(V("n"))),
            Par(Mod(Call("B", V("n")), D(2)))), Sub(C(V("n")), C(Add(V("n"), D(1)))))));
}

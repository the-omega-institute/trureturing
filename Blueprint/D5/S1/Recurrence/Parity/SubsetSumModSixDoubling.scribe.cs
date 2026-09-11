using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Parity;

internal sealed class SubsetSumModSixDoublingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Parity/SubsetSumModSixDoubling.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/oeis2025a068012");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Subset complementation and a three-period symmetry prove the A068012 doubling conjecture.",
        H("Subset Sums Modulo Six"),
        Blocks(
            Paragraph(Text("OEIS A068012 counts subsets of the interval from one to n whose "
                + "sum is zero modulo six. David A. Corneth's September 13, 2025 comment "
                + "conjectures doubling when n exceeds two and three does not divide n-1. "
                + "The argument below proves that assertion for every such n.")),
            Paragraph(Text("Indices n and m are natural numbers. Residues r lie in ZMod 6, "
                + "and iota6 denotes the natural-number map into that ring. Cardinalities "
                + "are natural numbers; subtraction of indices is natural subtraction. "
                + "The powerset consists of all finite subsets, including the empty set.")),
            Node("C", "The residue counts", CountFormula(),
                "Each subset contributes once, in the residue of its element sum. "
                + "Using the powerset makes this the subset count in the OEIS definition.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("a", "The zero residue", Disp(Seq(Bound("n"), Sp,
                Call("a", N()), Sp, Eq, Sp, Count(N(), D(0)))),
                "The sequence is the zero-residue coordinate, including index zero.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("count_succ", "Splitting at the last element", RecurrenceFormula(),
                "A subset either omits n+1, or is obtained by adjoining n+1 to a unique "
                + "subset of the preceding interval. In the second case its preceding "
                + "sum must be r-iota6(n+1). Mathlib's sum_powerset_insert gives this "
                + "partition, applied to the indicator of the prescribed residue.",
                DescribeRole.Lemma, AssessedProvenance.FromRepo(Source)),
            Node("count_three_periodic", "Three-periodic residue counts", PeriodFormula(),
                "For m at least three, split off element three from the interval. "
                + "The two contributions to residue r have preceding sums r and r-3. "
                + "Since -3=3 modulo six, shifting r by three exchanges these terms. "
                + "The threshold ensures that the element being split off is present.",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("count_zero_eq_one", "Equality in the residue-one phase", PhaseFormula(),
                "Complementation is a bijection on the subsets of the interval. If its "
                + "total sum is T, the bijection sends a sum r to T-r. Induction on m "
                + "gives 2T=m(m+1). When m is one modulo three, this forces T to be "
                + "one or four modulo six. Complementation therefore identifies the "
                + "zero count with one of those two counts, and three-periodicity "
                + "identifies both with the count at one.",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("subset_sum_mod_six_doubling", "The doubling conjecture", DoublingFormula(),
                "Put m=n-1. The recurrence reduces doubling to equality of the counts "
                + "at -n and zero. The allowed residues of m modulo six are 1, 2, 4, "
                + "and 5. The corresponding residues of -n are 4, 3, 1, and 0. "
                + "Three-periodicity and the residue-one equality handle all four. "
                + "The boundary n=3 is checked directly within the proof. The result "
                + "has no upper bound on n.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a068012-subset-sum-doubling"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a068012-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula CountFormula() => Disp(Seq(Bound("n"), Sp, ResidueBound(), Sp,
        Count(N(), R()), Sp, Eq, Sp, Call("card", Seq(OpenBrace, Sp, F.Id("S"), Sp,
            InMacro, Sp, Call("powerset", Call("Icc", D(1), N())), Sp, Mid, Sp,
            new Formula.Subscript(F.Sum, Seq(F.Id("x"), Sp, InMacro, Sp, F.Id("S"))),
            Sp, Call("iota6", F.Id("x")), Sp, Eq, Sp, R(), Sp, CloseBrace))));

    private static Formula RecurrenceFormula() => Disp(Seq(Bound("n"), Sp, ResidueBound(), Sp,
        Count(Add(N(), D(1)), R()), Sp, Eq, Sp,
        Add(Count(N(), R()), Count(N(), Sub(R(), Call("iota6", Add(N(), D(1))))))));

    private static Formula PeriodFormula() => Disp(Seq(Bound("m"), Sp, D(3), Sp, Le, Sp,
        M(), Sp, Implies, Sp, ResidueBound(), Sp, Count(M(), R()), Sp, Eq, Sp,
        Count(M(), Add(R(), D(3)))));

    private static Formula PhaseFormula() => Disp(Seq(Bound("m"), Sp, D(4), Sp, Le, Sp,
        M(), Sp, Implies, Sp, new Formula.Modulo(M(), D(3)), Sp, Eq, Sp, D(1), Sp,
        Implies, Sp, Count(M(), D(0)), Sp, Eq, Sp, Count(M(), D(1))));

    private static Formula DoublingFormula() => Disp(Seq(Bound("n"), Sp, D(2), Sp, Lt, Sp,
        N(), Sp, Implies, Sp, Neg, Sp, Open, D(3), Sp, Mid, Sp, Sub(N(), D(1)), Close,
        Sp, Implies, Sp, Call("a", N()), Sp, Eq, Sp, D(2), Sp, Times, Sp,
        Call("a", Sub(N(), D(1)))));

    private static Formula N() => F.Id("n");
    private static Formula M() => F.Id("m");
    private static Formula R() => F.Id("r");
    private static Formula Count(Formula n, Formula r) => Call("C", n, r);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Add(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Bound(string name) => Seq(Forall, Sp, F.Id(name), Sp, InMacro, Sp,
        Mathbb, Grp(F.Id("N")), Comma);
    private static Formula ResidueBound() => Seq(Forall, Sp, R(), Sp, InMacro, Sp,
        Call("ZMod", D(6)), Comma);
}

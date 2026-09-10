using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class OmegaGreedyPermutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/OmegaGreedyPermutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/shannon2023a363956");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The greedy sequence A363956 is a permutation of the positive integers.",
        H("A363956 is a permutation"),
        Blocks(
            Paragraph(Text(
                "All variables are natural numbers. omega(x) counts distinct prime factors. "
                + "prime(r) is the (r+1)-st prime, with prime(0)=2. The tail state starts at "
                + "(2,{1,2}). Its next term is the natural infimum of positive unused "
                + "multiples of prime(omega(current)-1), which is then inserted into the used "
                + "set. seq(1)=1 and seq(n+2) reads tail term n. The auxiliary index 0 is 1. "
                + "No coverage assumption occurs in this definition.")),
            Node("sequence_initial", "The prescribed seeds", Initial(),
                "The two seed values follow from the initial state and the index convention."),
            Node("sequence_positive", "Every term is positive", Positive(),
                "For a positive queue prime p and a finite used set U, the multiple "
                + "p times (max(U)+1) is positive and outside U. Thus the candidate set "
                + "is nonempty and its infimum belongs to it. Every tail term is at least 2."),
            Node("sequence_injective", "Positive indices have distinct values", Injective(),
                "The stored history contains every previous tail term. The next minimum "
                + "lies outside that history, so tail indices have distinct values. All tail "
                + "terms are at least 2, separating them from the initial 1."),
            Node("sequence_greedy", "The original minimum rule", Greedy(),
                "candidates(k) is exactly the set of positive y different from seq(i+1) "
                + "for every 0<=i<k+2, and divisible by prime(omega(seq(k+2))-1). "
                + "Induction identifies the stored used set with those prior terms, "
                + "so the displayed equality is the original smallest-unused rule."),
            Node("a363956_surjective", "Every positive integer occurs", Surjective(),
                "If a prime queue is selected infinitely often, each positive multiple "
                + "appears: otherwise that missing multiple bounds infinitely many distinct "
                + "outputs in a finite interval. Suppose queue 2 is selected only finitely "
                + "often. Every prime output has omega=1 and selects queue 2, so only "
                + "finitely many primes are output. Any selected prime has already appeared "
                + "or is the next minimum itself. Thus the selected queues form a finite "
                + "set, as do the omega values by injectivity of prime enumeration. Some "
                + "queue is selected infinitely often, but its multiples have arbitrarily "
                + "many distinct prime factors, a contradiction. Queue 2 therefore exhausts "
                + "all positive even numbers. For each r, multiply the product of the first r+1 "
                + "primes by successive positive powers of 2: these are distinct even "
                + "numbers with exactly r+1 prime factors. Their occurrence forces infinitely "
                + "many selections of prime(r). Every integer greater than 1 has a prime "
                + "divisor, whose queue outputs it. The seed supplies 1.",
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a363956-positive-permutation"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("a363956-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))),
            DescribeRole.Theorem, resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula S(Formula n) => Call("seq", n);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Bound(string name) => Seq(
        Forall, Sp, V(name), Sp, InMacro, Sp, Mathbb, Grp(V("N")), Comma, Sp);
    private static Formula Initial() => Disp(Seq(
        S(D(1)), Sp, Eq, Sp, D(1), Sp, Land, Sp, S(D(2)), Sp, Eq, Sp, D(2)));
    private static Formula Positive() => Disp(Seq(Bound("n"), D(0), Sp, Lt, Sp, S(V("n"))));
    private static Formula Injective() => Disp(Seq(Bound("i"), Bound("j"),
        D(0), Sp, Lt, Sp, V("i"), Sp, Implies, Sp,
        D(0), Sp, Lt, Sp, V("j"), Sp, Implies, Sp,
        S(V("i")), Sp, Eq, Sp, S(V("j")), Sp, Implies, Sp,
        V("i"), Sp, Eq, Sp, V("j")));
    private static Formula Greedy() => Disp(Seq(Bound("k"),
        S(Add(V("k"), D(3))), Sp, Eq, Sp, Call("sInf", Call("candidates", V("k")))));
    private static Formula Surjective() => Disp(Seq(Bound("m"),
        D(0), Sp, Lt, Sp, V("m"), Sp, Implies, Sp,
        Exists, Sp, V("n"), Sp, InMacro, Sp, Mathbb, Grp(V("N")), Comma, Sp,
        D(0), Sp, Lt, Sp, V("n"), Sp, Land, Sp, S(V("n")), Sp, Eq, Sp, V("m")));
}

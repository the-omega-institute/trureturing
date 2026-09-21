using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns.Separable;

internal sealed class CutFactorizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Patterns/Separable/CutFactorization.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Words/fu2019two");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual direct and skew fixed-cut factors preserve classical avoidance and ordinary descents.",
        H("Actual fixed-cut factorization"),
        Blocks(
            Paragraph(Text(
                "These are source-attested supporting contracts for the classical separable "
                + "permutation decomposition in Proposition 2.1 and the descent correspondence "
                + "in Theorem 2.3 of the cited source. They do not resolve Conjecture 5.2. "
                + "All permutations are bijections of Fin(n); Contains uses increasing position "
                + "embeddings and exact relative value comparisons. In the formulas, "
                + "Perm(n) means Equiv.Perm(Fin(n)); Bool has the values false and true; "
                + "ite(e,x,y) selects x when e is true and y otherwise. Permutations "
                + "are evaluated at zero-based positions, and subtype factors are "
                + "evaluated through their underlying permutations.")),
            Node("Avoids", "The literal avoidance class", DescribeRole.Definition,
                Disp(Seq(Forall, Sp, F.Id("n"), InMacro, Mathbb, Grp(F.Id("N")), Comma,
                    Forall, Sp, F.Id("p"), InMacro, Call("Perm", F.Id("n")), Comma,
                    Call("Avoids", F.Id("p")), Iff, Neg, Sp,
                    Call("Contains", F.Id("pattern2413"), F.Id("p")), Land, Neg, Sp,
                    Call("Contains", F.Id("pattern3142"), F.Id("p")))),
                "Avoids(p) is the conjunction of the two original negated containment "
                + "predicates. Avoider(n) is the subtype of actual permutations satisfying it."),
            Node("Avoider", "Actual avoiding permutations", DescribeRole.Definition,
                Disp(Seq(Forall, Sp, F.Id("n"), InMacro, Mathbb, Grp(F.Id("N")), Comma,
                    Call("Avoider", F.Id("n")), Eq, OpenBrace, F.Id("p"), InMacro,
                    Call("Perm", F.Id("n")), Mid, Call("Avoids", F.Id("p")), CloseBrace)),
                "This subtype retains each actual permutation and a proof that it avoids "
                + "the two literal patterns. It does not replace the class by a recurrence."),
            Node("blockSum", "Two actual block sums", DescribeRole.Definition,
                Disp(Seq(Forall, Sp, F.Id("m"), Comma, F.Id("k"), InMacro,
                    Mathbb, Grp(F.Id("N")), Comma, Forall, Sp, F.Id("e"), InMacro, Sp,
                    F.Id("Bool"), Comma, Forall, Sp, F.Id("a"), InMacro,
                    Call("Perm", F.Id("m")), Comma, Forall, Sp, F.Id("b"), InMacro,
                    Call("Perm", F.Id("k")), Comma,
                    Call("blockSum", F.Id("e"), F.Id("a"), F.Id("b")), InMacro,
                    Call("Perm", Seq(F.Id("m"), Plus, F.Id("k"))), Land,
                    Open, Forall, Sp, F.Id("i"), InMacro, Call("Fin", F.Id("m")), Comma,
                    Call("blockSum", F.Id("e"), F.Id("a"), F.Id("b")), Open, F.Id("i"), Close,
                    Eq, Call("ite", F.Id("e"), F.Id("k"), D(0)), Plus,
                    Call("a", F.Id("i")), Close, Land,
                    Open, Forall, Sp, F.Id("j"), InMacro, Call("Fin", F.Id("k")), Comma,
                    Call("blockSum", F.Id("e"), F.Id("a"), F.Id("b")), Open,
                    F.Id("m"), Plus, F.Id("j"), Close, Eq,
                    Call("ite", F.Id("e"), D(0), F.Id("m")), Plus,
                    Call("b", F.Id("j")), Close)),
                "For a in Perm(m) and b in Perm(k), false selects direct sum and true selects "
                + "skew sum. At a left position i<m, the values are a(i) and k+a(i), "
                + "respectively. At position m+j, they are m+b(j) and b(j). Neither "
                + "orientation reverses either factor. The constructor uses finSumFinEquiv "
                + "and Equiv.sumCongr, with a swap of value blocks for skew sum."),
            Node("Cut", "An oriented fixed cut", DescribeRole.Definition,
                Disp(Seq(Forall, Sp, F.Id("n"), Comma, F.Id("m"), InMacro,
                    Mathbb, Grp(F.Id("N")), Comma, Forall, Sp, F.Id("e"), InMacro, Sp,
                    F.Id("Bool"), Comma, Forall, Sp, F.Id("p"), InMacro,
                    Call("Perm", F.Id("n")), Comma,
                    Call("Cut", F.Id("e"), F.Id("p"), F.Id("m")), Iff,
                    Forall, Sp, F.Id("i"), Comma, F.Id("j"), InMacro,
                    Call("Fin", F.Id("n")), Comma,
                    Open, F.Id("i"), Lt, F.Id("m"), Land, Sp, F.Id("m"), Le, Sp,
                    F.Id("j"), Close, Rightarrow,
                    Call("ite", F.Id("e"),
                        Seq(Call("p", F.Id("j")), Lt, Call("p", F.Id("i"))),
                        Seq(Call("p", F.Id("i")), Lt, Call("p", F.Id("j")))))),
                "The cut compares every prefix value with every suffix value. "
                + "The factorization theorem requires m,k>0."),
            Node("avoids_block_sum_iff", "Exact avoidance in both directions", DescribeRole.Theorem,
                Disp(Seq(Forall, Sp, F.Id("m"), Comma, F.Id("k"), InMacro,
                    Mathbb, Grp(F.Id("N")), Comma, Forall, Sp, F.Id("e"), InMacro, Sp,
                    F.Id("Bool"), Comma, Forall, Sp, F.Id("a"), InMacro,
                    Call("Perm", F.Id("m")), Comma, Forall, Sp, F.Id("b"), InMacro,
                    Call("Perm", F.Id("k")), Comma,
                    Call("Avoids", Call("blockSum", F.Id("e"), F.Id("a"), F.Id("b"))),
                    Iff, Call("Avoids", F.Id("a")), Land, Call("Avoids", F.Id("b")))),
                "For all natural m,k, both orientations, and arbitrary factors a,b, "
                + "the block sum avoids both literal patterns exactly when both factors do. "
                + "An occurrence crossing the boundary would force a forbidden comparison "
                + "at one of the three proper splits of 2413 or 3142. Whole-factor "
                + "occurrences transfer through increasing position embeddings."),
            Node("fixed_cut_factorization", "Unique actual inverse factors", DescribeRole.Theorem,
                Disp(Seq(Forall, Sp, F.Id("m"), Comma, F.Id("k"), InMacro,
                    Mathbb, Grp(F.Id("N")), Comma,
                    Open, D(0), Lt, F.Id("m"), Land, D(0), Lt, F.Id("k"), Close,
                    Rightarrow, Forall, Sp, F.Id("e"), InMacro, Sp, F.Id("Bool"), Comma,
                    Forall, Sp, F.Id("p"), InMacro,
                    Call("Avoider", Seq(F.Id("m"), Plus, F.Id("k"))), Comma,
                    Call("Cut", F.Id("e"), F.Id("p"), F.Id("m")), Iff,
                    Exists, Bang, Sp, F.Id("q"), InMacro,
                    Call("Avoider", F.Id("m")), Times, Call("Avoider", F.Id("k")), Comma,
                    Call("blockSum", F.Id("e"), Call("fst", F.Id("q")),
                        Call("snd", F.Id("q"))), Eq, F.Id("p"))),
                "For every positive m,k, each orientation e, and p in Avoider(m+k), "
                + "Cut(e,p,m) holds exactly when there is a unique pair q in "
                + "Avoider(m) times Avoider(k) whose literal block sum is p. "
                + "Tuple.sort constructs the factor ranks. Internal comparisons together "
                + "with the actual crossing inequalities make the reconstructed permutation "
                + "have the same full value order as p. A monotone permutation is the "
                + "identity, proving equality of actual values, not just their ranks. "
                + "The two block evaluation formulas give uniqueness."),
            Node("descentAt", "An adjacent-descent indicator", DescribeRole.Definition,
                Disp(Seq(Forall, Sp, F.Id("n"), InMacro, Mathbb, Grp(F.Id("N")), Comma,
                    Forall, Sp, F.Id("p"), InMacro, Call("Perm", F.Id("n")), Comma,
                    Forall, Sp, F.Id("i"), InMacro, Call("Fin", F.Id("n")), Comma,
                    Call("descentAt", F.Id("p"), F.Id("i")), Eq,
                    Call("ite", Seq(F.Id("i"), Plus, D(1), Lt, F.Id("n")),
                        Call("ite", Seq(Call("p", Seq(F.Id("i"), Plus, D(1))), Lt,
                            Call("p", F.Id("i"))), D(1), D(0)), D(0)))),
                "At position i this is one exactly when i+1<n and p(i+1)<p(i). "
                + "The inner comparison is evaluated only when i+1<n, so its "
                + "successor index belongs to Fin(n). It is zero otherwise, including "
                + "at the final position."),
            Node("descents", "Ordinary adjacent descents", DescribeRole.Definition,
                Disp(Seq(Forall, Sp, F.Id("n"), InMacro, Mathbb, Grp(F.Id("N")), Comma,
                    Forall, Sp, F.Id("p"), InMacro, Call("Perm", F.Id("n")), Comma,
                    Call("descents", F.Id("p")), Eq, Sum, Underscore,
                    Grp(F.Id("i"), InMacro, Call("Fin", F.Id("n"))),
                    Call("descentAt", F.Id("p"), F.Id("i")))),
                "The sum runs over every position in Fin(n). Thus descents counts "
                + "ordinary adjacent descents; in particular a singleton has zero descents."),
            Node("descents_block_sum", "The exact boundary weight", DescribeRole.Theorem,
                Disp(Seq(Forall, Sp, F.Id("m"), Comma, F.Id("k"), InMacro,
                    Mathbb, Grp(F.Id("N")), Comma,
                    Open, D(0), Lt, F.Id("m"), Land, D(0), Lt, F.Id("k"), Close,
                    Rightarrow, Forall, Sp, F.Id("e"), InMacro, Sp, F.Id("Bool"), Comma,
                    Forall, Sp, F.Id("a"), InMacro, Call("Perm", F.Id("m")), Comma,
                    Forall, Sp, F.Id("b"), InMacro, Call("Perm", F.Id("k")), Comma,
                    Call("descents", Call("blockSum", F.Id("e"), F.Id("a"), F.Id("b"))),
                    Eq, Call("descents", F.Id("a")), Plus, Call("descents", F.Id("b")), Plus,
                    Call("ite", F.Id("e"), D(1), D(0)))),
                "For arbitrary positive m,k and factors a,b, the number of descents "
                + "is des(a)+des(b)+boundary(e), where boundary(false)=0 and "
                + "boundary(true)=1. The proof partitions adjacent positions into left "
                + "interior, boundary, and right interior. It applies when either "
                + "factor is a singleton and when the factor lengths differ."),
            Paragraph(Text(
                "The greatest-cut choice, its right-factor sign condition, weighted "
                + "enumeration, generating-function equations, and real-rootedness "
                + "remain separate obligations. The actual blockSum constructor is "
                + "also used in the fixed-bottom A398542 minimum decomposition. "
                + "This support unit carries no open-problem resolution claim.")))));

    private static DocumentBlock Node(
        string name, string title, DescribeRole role, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))), role);
}

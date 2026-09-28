using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Budget;

internal sealed class FiniteCutoffProtocolRecursionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact identification before a finite deadline is characterized by the first read "
            + "and the continuation on each actual response fiber.",
        H("Finite Cutoff and First-Read Recursion"),
        Blocks(
            Paragraph(Text(
                "Fix natural numbers p>=2 and P>=1, an initial block b in Fin(p), "
                    + "and a nonempty finite set A of original residues r with 0<=r<P. "
                    + "At elapsed time t the physical symbol is "
                    + "R(t,r)=((bP+r+t) mod (pP)) div P. Put "
                    + "Y(A,t)={R(t,r):r in A} and fiber(A,t,y)=A_y(t)={r in A:R(t,r)=y}. "
                    + "These fibers retain the same original residue throughout execution.")),
            Paragraph(Text(
                "A protocol either stops with an original-residue label or waits a natural "
                    + "number of forward unit events, reads once, and selects its continuation "
                    + "from the observed symbol. The known initial block and clock determine "
                    + "the uncarried label (b+t div P) mod p. A read is encoded as zero when "
                    + "it equals this label and as one otherwise. Indeed its symbol is "
                    + "(b+t div P+c) mod p, where c is the decoded binary sensor, equal to "
                    + "zero for r<P-(t mod P) and one otherwise. Since p>=2, these two "
                    + "labels are distinct. Encoding and decoding therefore preserve every "
                    + "actual branch, query count, output, and completion time.")),
            Paragraph(Text(
                "For arbitrary natural n, D, q with n<=D, F(q,A,n,D) means that some protocol with at most q further "
                    + "reads, begun at time n, outputs r and finishes by D for every r in A. "
                    + "The protocol is one common decision tree; its waits and continuations "
                    + "have no direct access to the unknown residue. Leaves can occur before "
                    + "the query budget is exhausted. Zero waiting and immediate rereading "
                    + "are allowed, since the current read need not have been acquired.")),
            Describe.Lean(
                DescribeId.Create("finite-cutoff-branch-recursion"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Budget/FiniteCutoffProtocolRecursion.finite_cutoff_branch_recursion"),
                H("Exact decomposition at every query budget"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A stopped controller returns the same label on all candidates, so "
                            + "zero-query success is equivalent to a singleton. For a successful "
                            + "query node, its first read time t is common to all candidates. "
                            + "Forward execution makes t no later than any completion time, "
                            + "hence t<=D. All candidates with the same physical response "
                            + "select the same continuation, which has one fewer available read.")),
                    Paragraph(Text(
                        "Conversely, choose a successful continuation for every actual "
                            + "response fiber, wait t-n events, and attach these continuations "
                            + "to the corresponding observed bits. Unreachable branches may "
                            + "stop arbitrarily. Every original candidate follows its own fiber, "
                            + "is identified correctly, and meets the same deadline. The argument "
                            + "includes t=n, singleton fibers, and all nonempty finite candidate "
                            + "sets, without requiring an interval or a power-of-p block length."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula q = F.Id("q"), a = F.Id("A"), n = F.Id("n"), d = F.Id("D"),
            t = F.Id("t"), y = F.Id("y");
        Formula singleton = Seq(Call("card", a), Sp, Eq, Sp, D(1));
        Formula branches = Seq(Forall, Sp, y, Sp, InMacro, Sp, Call("Y", a, t), Comma, Sp,
            Call("F", q, Call("fiber", a, t, y), t, d));
        Formula step = Seq(singleton, Sp, Lor, Sp, Open,
            Exists, Sp, t, Sp, InMacro, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp,
            n, Sp, Leq, Sp, t, Sp, Land, Sp, t, Sp, Leq, Sp, d, Sp, Land, Sp,
            Open, branches, Close, Close);
        return Disp(Seq(
            Open, Call("F", D(0), a, n, d), Sp, Iff, Sp, singleton, Close, Sp, Land, Sp,
            Open, Call("F", Seq(q, Plus, D(1)), a, n, d), Sp, Iff, Sp, step, Close));
    }
}

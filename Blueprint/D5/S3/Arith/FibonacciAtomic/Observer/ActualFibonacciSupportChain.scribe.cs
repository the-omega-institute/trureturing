using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;

internal sealed class ActualFibonacciSupportChainDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "ActualFibonacciSupportChain", H("Actual Fibonacci support chain"), Blocks(
            Paragraph(Text("Sources are finite nonempty ordered Boolean trees. False addresses mean left and true addresses mean right. The initial source is the true-labelled leaf alpha, and substitution sends alpha to beta and beta to the ordered pair of beta and alpha. Pos denotes the set of all literal addresses whose native readout is not absent; it records only presence, without requiring agreement of leaf labels or branch replies.")),
            Describe.Lean(
                DescribeId.Create("actual-fibonacci-support-chain"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/ActualFibonacciSupportChain.actual_fibonacci_support_chain"),
                H("Strict inclusions and bounded support agreement"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every natural k at least one, the support of the even orbit tree is strictly contained in the next odd support, which is strictly contained in the support of the ordered pair of two copies of the even tree. Both adjacent membership equivalences hold at every address of length at most k, including the empty address.")),
                    Paragraph(Text("The orbit recurrence gives left and right children with ranks one and two below the parent rank. Induction on an arbitrary address proves that every address of length d is present at every orbit rank at least twice d. Applying this fact to rank twice k makes all three support bits equal to one throughout the stated radius. Original subtree transport gives the global inclusions. The words consisting of k minus one right edges followed by two left edges, and of k right edges followed by one left edge, respectively establish strictness.")),
                    Paragraph(Text("The statement has no source-size bound, selected-word restriction or image-positivity premise. It concerns support bits on the actual trees; it gives neither complete reply equality nor a protocol cost bound."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var k = V("k");
        var q = V("q");
        var even = Orbit(Seq(D(2), k));
        var odd = Orbit(Seq(D(2), k, Sp, Plus, Sp, D(1)));
        var pair = Call("mul", even, even);
        return All("k", V("Nat"), Imp(Le(D(1), k), And(
            Strict(Call("Pos", even), Call("Pos", odd)),
            Strict(Call("Pos", odd), Call("Pos", pair)),
            All("q", V("Address"), Imp(Le(Call("length", q), k), And(
                IffOf(Present(q, even), Present(q, odd)),
                IffOf(Present(q, odd), Present(q, pair))))))));
    }
    private static Formula Orbit(Formula n) => Call("iterate", V("substitution"), n,
        Call("of", V("true")));
    private static Formula Present(Formula q, Formula t) =>
        Seq(Call("readout", q, t), Sp, Neq, Sp, V("absent"));
    private static Formula Strict(Formula a, Formula b) => And(
        Seq(a, Sp, Subseteq, Sp, b), Seq(a, Sp, Neq, Sp, b));
    private static Formula V(string n) => F.Id(n);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string n, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(n))), [.. args]);
    private static Formula And(params Formula[] fs) => Seq(fs.Select((f, i) =>
        i == 0 ? Par(f) : Seq(Sp, Land, Sp, Par(f))).ToArray());
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula IffOf(Formula a, Formula b) => Seq(Par(a), Sp, Iff, Sp, Par(b));
    private static Formula Le(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula All(string n, Formula t, Formula b) =>
        Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Par(b));
}

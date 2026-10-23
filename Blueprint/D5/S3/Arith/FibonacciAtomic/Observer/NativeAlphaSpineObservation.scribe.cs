using System.Linq;
using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;

internal sealed class NativeAlphaSpineObservationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativeAlphaSpineObservation", H("Native alpha-spine observation locality"), Blocks(
            Describe.Lean(
                DescribeId.Create("native-alpha-spine-at"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/NativeAlphaSpineObservation.native_alpha_spine_at"),
                H("The original reached hole"),
                StatementSource.FromAuthor(Disp(All("p", V("Address"), All("x", V("Source"),
                    Eq(Call("subtree", V("p"), E(V("p"), V("x"))), Call("some", V("x"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every original address p and actual Source x, the alpha-sibling path context E(p,x) reaches precisely x at p. The identity includes the empty path. Originally-present transport therefore applies at this hole at every natural epoch, even when a selected strict extension is initially absent."))), DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("native-alpha-spine-observation"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/NativeAlphaSpineObservation.native_alpha_spine_observation"),
                H("Three-source native observation boundary"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Sources form FreeMagma Bool: finite nonempty ordered Boolean trees with source leaves alpha=of(true) and beta=of(false). Addresses are finite Boolean lists, with false=L and true=R. The readout values alpha, beta, branch, and absent are replies, distinct from source trees. Write rho for substitution, which sends alpha to beta, beta to mul(beta,alpha), and mul(x,y) to mul(rho(x),rho(y)). For every address p, the alpha-spine source is defined by E([],x)=x, E(L::p,x)=mul(E(p,x),alpha), and E(R::p,x)=mul(alpha,E(p,x)).")),
                    Paragraph(Text("The original sources E(p,alpha), E(p,beta), and E(p,mul(alpha,alpha)) have replies alpha, beta, and branch at p. Their current sources are obtained by applying rho 2k times. At every arbitrary address q for which p is not a prefix of q, the current raw replies agree. This includes proper ancestors of p and every divergent continuation; equality of these replies does not assert equality of the corresponding subtrees.")),
                    Paragraph(Text("For a query q=p++r inside the prefix cone, the current readout of E(p,x) equals the readout at r of rho iterated 2k on x. Writing T(j)=rho iterated j on alpha, the three transported fillings are T(2k), T(2k+1), and mul(T(2k),T(2k)). For k at least one, the Fibonacci support chain gives equal non-absence bits at every suffix of length at most k. Combining this with raw reply equality outside the cone gives both adjacent support equivalences at every arbitrary q of length at most |p|+k. Each adjacent support distinction therefore requires |q| at least |p|+k+1.")),
                    Paragraph(Text("The bounds include p=[] and k=1 and quantify over all finite addresses. Inside the prefix cone, equal non-absence bits do not assert equal raw replies or equal subtrees. The conclusion concerns literal query length; it supplies no protocol optimum or extension to a fourth source."))
                ), DescribeRole.Theorem)
        )));

    private static Formula Statement()
    {
        var p = V("p");
        var k = V("k");
        var q = V("q");
        var alpha = Call("of", V("true"));
        var beta = Call("of", V("false"));
        var branch = Call("mul", alpha, alpha);
        var eAlpha = E(p, alpha);
        var eBeta = E(p, beta);
        var eBranch = E(p, branch);
        var current = (Formula source) => Call("iterate", V("substitution"), Mul(D(2), k), source);
        var support = (Formula source) => Ne(Call("readout", q, current(source)), V("absent"));
        var raw = (Formula a, Formula b) => Eq(Call("readout", q, current(a)), Call("readout", q, current(b)));
        var supportDiff = (Formula a, Formula b) => Not(IffOf(support(a), support(b)));
        var clauses = And(
            Eq(Call("readout", p, eAlpha), V("alpha")),
            Eq(Call("readout", p, eBeta), V("beta")),
            Eq(Call("readout", p, eBranch), V("branch")),
            AllQ(q, Imp(Not(Prefix(p, q)), And(raw(eAlpha, eBeta), raw(eBeta, eBranch)))),
            AllQ(q, Imp(Le(Len(q), Add(Len(p), k)),
                And(IffOf(support(eAlpha), support(eBeta)), IffOf(support(eBeta), support(eBranch))))),
            AllQ(q, Imp(supportDiff(eAlpha, eBeta), Le(Add(Add(Len(p), k), D(1)), Len(q)))),
            AllQ(q, Imp(supportDiff(eBeta, eBranch), Le(Add(Add(Len(p), k), D(1)), Len(q)))));
        return All("p", V("Address"), All("k", V("Nat"), Imp(Le(D(1), k), clauses)));
    }

    private static Formula E(Formula p, Formula x) => Call("E", p, x);
    private static Formula Prefix(Formula p, Formula q) => Call("IsPrefix", p, q);
    private static Formula Len(Formula x) => Call("length", x);
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Mul(Formula a, Formula b) => Seq(a, Sp, Times, Sp, b);
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula Ne(Formula a, Formula b) => Seq(a, Sp, Neq, Sp, b);
    private static Formula Not(Formula a) => Seq(Neg, Sp, Par(a));
    private static Formula IffOf(Formula a, Formula b) => Seq(Par(a), Sp, Iff, Sp, Par(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula Le(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula AllQ(Formula q, Formula body) => Seq(Forall, Sp, V("q"), Colon, Sp, V("Address"), Comma, Sp, Par(body));
    private static Formula All(string n, Formula t, Formula body) =>
        Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Par(body));
    private static Formula And(params Formula[] fs) => Seq(fs.Select((f, i) => i == 0 ? Par(f) : Seq(Sp, Land, Sp, Par(f))).ToArray());
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula V(string n) => F.Id(n);
    private static Formula Call(string n, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(V(n))), [.. args]);
}

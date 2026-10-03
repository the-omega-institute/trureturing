using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class SourceTransportCentralizerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/SourceTransportCentralizer.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every ordered source endomorphism commuting with Fibonacci substitution is one unique nonnegative iterate.",
        H("The Ordered Fibonacci Source Centralizer"),
        Blocks(
            Paragraph(Text("T is the free magma on the two Boolean generators: alpha is the leaf true "
                + "and beta is the leaf false. Its elements are actual nonempty finite ordered binary trees. "
                + "The operation pair(s,t) constructs an internal node with left child s and right child t. "
                + "There are no associative, commutative or quotient identifications. The substitution rho "
                + "sends alpha to beta, beta to pair(beta,alpha), and pair(s,t) to pair(rho(s),rho(t)).")),
            Paragraph(Text("All exponents belong to Nat={0,1,2,...}. Write R(k,t)=rho^k(t), "
                + "so R(0,t)=t, and Rpower(k) denotes the function t to R(k,t). C(F) means that "
                + "the total function F:T to T preserves every ordered pair "
                + "and satisfies F(rho(t))=rho(F(t)) for every source t. Pairing preservation and commutation are the only assumptions; "
                + "injectivity and a unique power representation follow, while bijectivity and inverse domains are classified below.")),
            Paragraph(Text("For each k, I(k) is the actual subtype consisting of trees in the range "
                + "of R(k,-). Write core(k,t) for R(k,t) regarded as an element of I(k), with t as its "
                + "preimage witness. A range inverse d:I(k) to T satisfies d(core(k,t))=t for every t "
                + "and core(k,d(y))=y for every y:I(k); the second equality is an equality in that subtype.")),
            Describe.Lean(DescribeId.Create("source-transport-centralizer"),
                DeclarationHandle.Create(Prefix + "source_transport_centralizer"),
                H("Complete Centralizer and Inverse Classification"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The stability equation rho(rho(u))=pair(rho(u),u) holds exactly "
                        + "on the alpha orbit. For every total F, C(F) holds if and only if there is exactly "
                        + "one natural k with F=R(k,-). Every F satisfying C(F) is injective. For each k, "
                        + "R(k,-):T to T is bijective if and only if k=0. For each positive k there is "
                        + "exactly one range inverse with both identities, and there is no total d:T to T "
                        + "satisfying both inverse identities on T.")),
                    Paragraph(Text("Composition counts alpha and beta leaves. The public fiber map "
                        + "transports composition by (a,b) to (b,a+b). Equal substituted trees therefore "
                        + "have equal source compositions. Appending alpha to both source trees puts them "
                        + "in one positive composition fiber; the injectivity of its one-step fiber map "
                        + "then cancels their images and the appended pair constructor. The same composition "
                        + "transport excludes alpha from the image of rho.")),
                    Paragraph(Text("Both leaves satisfy the stability equation. If pair(s,t) satisfies "
                        + "it, comparison of the two root children gives rho^2(t)=pair(s,t) and "
                        + "rho^2(s)=rho(pair(s,t))=rho^2(rho(t)). Injectivity gives s=rho(t), so t "
                        + "also satisfies the equation. Structural induction on the strictly smaller right "
                        + "subtree gives t=R(j,alpha), hence pair(s,t)=R(j+2,alpha). Conversely, applying "
                        + "the pairing-preserving rho to the equation preserves it, starting from alpha.")),
                    Paragraph(Text("Commutation forces F(beta)=rho(F(alpha)) and the stability equation "
                        + "for F(alpha). Its classification determines both generator images. The universal "
                        + "property of the free magma identifies F with the corresponding iterate. Every "
                        + "iterate preserves pairs and commutes with rho. Cancelling injective iterates "
                        + "and excluding alpha from every positive image shows that distinct exponents "
                        + "give distinct alpha images, establishing uniqueness.")),
                    Paragraph(Text("Every iterate is injective. Exponent zero gives the identity; every "
                        + "positive exponent omits alpha, so is not surjective. Corestriction to the actual "
                        + "image is a bijection and its inverse satisfies both typed identities. Injectivity "
                        + "makes that inverse unique. An arbitrary whole-source extension can satisfy a "
                        + "left-inverse identity, but cannot satisfy the right-inverse identity at alpha."))),
                DescribeRole.Theorem))));

    private static Formula V(string s) => F.Id(s);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula IffOf(Formula a, Formula b) => Seq(Par(a), Sp, Iff, Sp, Par(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula And(params Formula[] xs) => Seq(xs.Select((x, i) =>
        i == 0 ? Par(x) : Seq(Sp, Land, Sp, Par(x))).ToArray());
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula Map(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula R(Formula k, Formula t) => Call("R", k, t);
    private static Formula Core(Formula k, Formula t) => Call("core", k, t);

    private static Formula ResultFormula()
    {
        Formula t = V("t"), s = V("s"), u = V("u"), k = V("k"), j = V("j");
        Formula f = V("F"), d = V("d"), e = V("e"), y = V("y");
        Formula tree = V("T"), nat = Call("Nat"), image = Call("I", k);
        Formula centralizes = And(
            All("s", tree, All("t", tree,
                EqOf(Call("F", Call("pair", s, t)), Call("pair", Call("F", s), Call("F", t))))),
            All("t", tree, EqOf(Call("F", R(D(1), t)), R(D(1), Call("F", t)))));
        Formula Power(Formula n) => Call("Rpower", n);
        Formula RangeLaws(string name) => And(
            All("t", tree, EqOf(Call(name, Core(k, t)), t)),
            All("y", image, EqOf(Core(k, Call(name, y)), y)));
        Formula GlobalLaws = And(
            All("t", tree, EqOf(Call("d", R(k, t)), t)),
            All("t", tree, EqOf(R(k, Call("d", t)), t)));
        Formula stable = All("u", tree, IffOf(
            EqOf(R(D(2), u), Call("pair", R(D(1), u), u)),
            Some("k", nat, EqOf(R(k, V("alpha")), u))));
        Formula uniquePower = Some("k", nat, And(EqOf(f, Power(k)),
            All("j", nat, Imp(EqOf(f, Power(j)), EqOf(j, k)))));
        Formula uniqueInverse = Some("d", Map(image, tree), And(RangeLaws("d"),
            All("e", Map(image, tree), Imp(RangeLaws("e"), EqOf(e, d)))));
        Formula result = And(stable,
            All("F", Map(tree, tree), IffOf(centralizes, uniquePower)),
            All("F", Map(tree, tree), Imp(centralizes, Call("Injective", f))),
            All("k", nat, IffOf(Call("Bijective", Power(k)), EqOf(k, D(0)))),
            All("k", nat, Imp(Seq(D(0), Sp, Lt, Sp, k), And(uniqueInverse,
                Seq(Neg, Sp, Par(Some("d", Map(tree, tree), GlobalLaws)))))));
        return Disp(Seq(Begin, Grp(V("gathered")), result, End, Grp(V("gathered"))));
    }
}

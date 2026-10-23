using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.SourceCoordinates;

internal sealed class IntrinsicSubstitutionCoordinatesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/SourceCoordinates/IntrinsicSubstitutionCoordinates.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Maximal actual substitution ancestry determines a unique primitive endpoint and the full ordered-pair law.",
        H("Intrinsic Substitution Coordinates"),
        Blocks(
            Paragraph(Text("T is FreeMagma Bool, the actual nonempty finite ordered binary trees. "
                + "Alpha is the true leaf and beta the false leaf. Pair(s,t) retains its literal ordered children "
                + "and brackets. R(n,t) denotes the n-fold iterate of the original substitution rho, which "
                + "sends alpha to beta and beta to pair(beta,alpha), and preserves ordered pairing. "
                + "All exponents are natural numbers, including zero.")),
            Describe.Lean(DescribeId.Create("intrinsic-no-alpha"),
                DeclarationHandle.Create(Prefix + "no_alpha"), H("Alpha has no predecessor"),
                StatementSource.FromAuthor(Seq(Forall, Sp, V("t"), Colon, Sp, V("T"), Comma, Sp,
                    R(D(1), V("t")), Sp, Neq, Sp, V("alpha"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each substituted leaf is beta or the pair (beta,alpha), "
                    + "and each substituted internal node remains an internal node. Thus alpha is absent from the image."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("intrinsic-pair-image"),
                DeclarationHandle.Create(Prefix + "pair_image"), H("Exact Ordered Pair Image Grammar"),
                StatementSource.FromAuthor(All("s", Tree, All("t", Tree, IffOf(Some("x", Tree, EqOf(R(D(1), V("x")), Call("pair", V("s"), V("t")))), Seq(Par(And(EqOf(V("s"), V("beta")), EqOf(V("t"), Alpha))), Sp, Lor, Sp, Par(And(Some("x", Tree, EqOf(R(D(1), V("x")), V("s"))), Some("y", Tree, EqOf(R(D(1), V("y")), V("t")))))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("A substituted beta gives the special pair (beta,alpha). Every substituted compound gives a pair of substituted children. Conversely the alternatives have preimages beta and the ordered pair of the two child preimages."))), DescribeRole.Theorem),
            Definition("Primitive", "Primitive endpoint", All("p", Tree,
                IffOf(Call("Primitive", V("p")), NegOf(Some("x", Tree,
                    EqOf(R(D(1), V("x")), V("p")))))),
                "A primitive source has no actual one-step predecessor."),
            Definition("Ancestors", "Actual substitution ancestors", All("t", Tree,
                EqOf(Call("Ancestors", V("t")), Seq(OpenBrace, Pair(V("x"), V("k")), Sp,
                    Vert, Sp, V("x"), Colon, Tree, Comma, Sp, V("k"), Colon, Nat, Comma, Sp,
                    R(V("k"), V("x")), Sp, Eq, Sp, V("t"), CloseBrace))),
                "Ancestors(t) retains every actual source and legal exponent. For this fixed t, "
                + "the map (x,k) to (t,x,k) embeds it in the existing finite entrance fiber indexed by G(wd(t)). "
                + "That geometry is only an internal index establishing finiteness; it identifies no source or primitive root."),
            Definition("legalIndices", "Legal exponents", All("t", Tree,
                EqOf(Call("legalIndices", V("t")), Seq(OpenBrace, V("k"), Sp, Vert, Sp,
                    V("k"), Colon, Nat, Comma, Sp, Some("x", Tree, EqOf(R(V("k"), V("x")), V("t"))), CloseBrace))),
                "The finite set of actual legal exponents contains zero."),
            Definition("depth", "Maximal legal exponent", All("t", Tree,
                EqOf(Depth(V("t")), Call("max", Call("legalIndices", V("t"))))),
                "Depth directly reuses Geometry.AncestorAreaInstability.depth, the supremum of the original legal-exponent set. "
                + "Finiteness makes it the maximum displayed here. It is not address length or tree height."),
            Definition("root", "Actual maximal ancestor", All("t", Tree,
                EqOf(R(Depth(V("t")), Root(V("t"))), V("t"))),
                "Root(t) is an actual ancestor at the maximum exponent. Injectivity makes it unique, "
                + "and maximality excludes a further predecessor."),
            Definition("flag", "Alpha-ray flag", All("t", Tree,
                IffOf(EqOf(Flag(V("t")), One), EqOf(Root(V("t")), Alpha))),
                "The Boolean flag is true exactly when the primitive endpoint is alpha. In formulas, "
                + "Boolean true is written 1 and false is written 0."),
            Definition("Q", "Intrinsic coordinate", All("t", Tree,
                EqOf(Coord(V("t")), Pair(Depth(V("t")), Flag(V("t"))))),
                "The coordinate consists of intrinsic depth and the alpha-ray flag."),
            Describe.Lean(DescribeId.Create("intrinsic-coordinates"),
                DeclarationHandle.Create(Prefix + "intrinsic_coordinates"), H("Unique Primitive-Ray Coordinates"),
                StatementSource.FromAuthor(All("t", Tree, Intrinsic(V("t")))),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Every legal exponent is at most the actual maximum. Conversely, for k at most "
                        + "the maximum, applying the remaining depth to the primitive endpoint constructs a k-step ancestor. "
                        + "A predecessor of the maximal ancestor would increase the maximum. If t=R(n,p) with p primitive, "
                        + "any deeper ancestor cancels the injective n-fold iterate to give a positive predecessor of p. "
                        + "Thus n is exactly the maximum and p is exactly root(t)."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("all-source-coordinate-law"),
                DeclarationHandle.Create(Prefix + "all_source_coordinate_law"), H("Complete Substitution and Pairing Laws"),
                StatementSource.FromAuthor(FullLaw()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Substitution increases the intrinsic depth by one and preserves the primitive endpoint. "
                        + "For a pair with child depths a,b, remove m=min(a,b) common substitution steps. "
                        + "The residual children are R(a-m,root(s)) and R(b-m,root(t)). At least one is primitive. "
                        + "A pair lies in the one-step image precisely when it is (beta,alpha), or both children are images. "
                        + "The latter alternative is impossible for the residual pair.")),
                    Paragraph(Text("The exceptional residual (beta,alpha) occurs exactly when both child flags are true "
                        + "and a=b+1. It is R(2,alpha), so the pair has coordinate (b+2,1). Otherwise the residual pair "
                        + "is itself primitive and cannot be the leaf alpha; its coordinate is (m,0). "
                        + "This applies to both leaves, zero depths, equal depths and arbitrary children off the alpha ray. "
                        + "No quotient, inverse geometry or acquisition bound is asserted."))), DescribeRole.Theorem))));

    private static Formula V(string s) => F.Id(s);
    private static Formula Tree => V("T");
    private static Formula Nat => Call("Nat");
    private static Formula Alpha => V("alpha");
    private static Formula One => D(1);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Pair(Formula a, Formula b) => Par(Seq(a, Comma, Sp, b));
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula LeOf(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula NegOf(Formula f) => Seq(Neg, Sp, Par(f));
    private static Formula IffOf(Formula a, Formula b) => Seq(Par(a), Sp, Iff, Sp, Par(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula And(params Formula[] xs) => Seq(xs.Select((x, i) =>
        i == 0 ? Par(x) : Seq(Sp, Land, Sp, Par(x))).ToArray());
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula R(Formula n, Formula t) => Call("R", n, t);
    private static Formula Depth(Formula t) => Call("depth", t);
    private static Formula Root(Formula t) => Call("root", t);
    private static Formula Flag(Formula t) => Call("flag", t);
    private static Formula Coord(Formula t) => Call("Q", t);
    private static DocumentBlock Definition(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("intrinsic-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Intrinsic(Formula t) => And(
        All("k", Nat, IffOf(Some("x", Tree, EqOf(R(V("k"), V("x")), t)), LeOf(V("k"), Depth(t)))),
        Call("Primitive", Root(t)), EqOf(R(Depth(t), Root(t)), t),
        All("p", Tree, All("n", Nat, Imp(Call("Primitive", V("p")),
            Imp(EqOf(R(V("n"), V("p")), t), And(EqOf(V("n"), Depth(t)), EqOf(V("p"), Root(t))))))),
        IffOf(EqOf(Flag(t), One), EqOf(R(Depth(t), Alpha), t)));

    private static Formula FullLaw()
    {
        Formula t = V("t"), s = V("s");
        Formula special = And(EqOf(Flag(s), One), EqOf(Flag(t), One),
            EqOf(Depth(s), Add(Depth(t), One)));
        Formula exceptional = Pair(Add(Depth(t), D(2)), One);
        Formula ordinary = Pair(Call("min", Depth(s), Depth(t)), D(0));
        return And(All("t", Tree, Intrinsic(t)),
            All("t", Tree, EqOf(Coord(R(One, t)), Pair(Add(Depth(t), One), Flag(t)))),
            All("s", Tree, All("t", Tree, And(
                Imp(special, EqOf(Coord(Call("pair", s, t)), exceptional)),
                Imp(NegOf(special), EqOf(Coord(Call("pair", s, t)), ordinary))))),
            EqOf(Coord(Alpha), Pair(D(0), One)),
            EqOf(Coord(V("beta")), Pair(One, One)));
    }
}

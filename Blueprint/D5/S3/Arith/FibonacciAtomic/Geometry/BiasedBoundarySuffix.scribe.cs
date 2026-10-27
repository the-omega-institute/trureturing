using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Geometry;

internal sealed class BiasedBoundarySuffixDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundarySuffix.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict descendants of incomparable prefixes use disjoint coordinates of the original edge ell2, and their traces retain the common infinite biased boundary codomain.",
        H("Strict Suffix Energy"), Blocks(
            Def("descendant", "For an arbitrary finite prefix p and a nonempty edge address u, descendant(p,u) is the nonempty address obtained by appending u to p."),
            Def("suffixLinear", "The suffix restriction reads precisely the coordinates indexed by strict descendants. Append injectivity makes this a square-summable vector for every vector in H."),
            Def("S", "S(p) is the continuous linear suffix restriction on the original H, with norm at most one. It uses nonempty suffixes, so it omits p and every ancestor of p."),
            Def("suffixTrace", "The suffix trace is the composition J with S(p), where J is the original bounded trace into L2 of the fixed infinite golden biased Bernoulli law M."),
            Def("PrefixFree", "A finite family is prefix-free when two members can be comparable prefixes only if they are equal. The family may be empty or contain the empty address."),
            Describe.Lean(DescribeId.Create("biasedboundarysuffix-energy"),
                DeclarationHandle.Create(Prefix + "strict_suffix_energy"), H("Disjoint Energy and Infinite Suffix Traces"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Every suffix coordinate is the original coordinate at the concatenated address. Its length strictly exceeds the prefix length. For the empty prefix the suffix map is the identity on all of H.")),
                    Paragraph(Text("For every finite prefix-free family A and every z in H, the sum of the squared suffix norms is bounded by the squared norm of z. If two concatenated addresses coincide, their prefixes are comparable; prefix-freeness identifies the prefixes, and append cancellation then identifies the suffixes. Thus the entire family of strict descendant coordinates embeds injectively into the original edge set.")),
                    Paragraph(Text("For every prefix and every vector in H, the weighted cylinder-indicator series on the suffix boundary has L2 sum J(S(p)z). Applying the Hardy depth-tail estimate to each restricted vector and summing gives the same geometric coefficient times the single original energy. These conclusions use infinite square-summable increments without a finite-support restriction.")),
                    Paragraph(Text("This coordinate result does not identify composition by prepending a prefix with conditional restriction of the boundary law. That measure identity, its bounded L2 pullback, the prefix-constant trace identity, the stopping projection and the centered residual decomposition require further proofs. Spectral counting is outside these conclusions."))), DescribeRole.Theorem))));

    private static DocumentBlock Def(string name, string prose) => Describe.Lean(
        DescribeId.Create("biasedboundarysuffix-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(name),
        StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula V(string s) => F.Id(s);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Seq(Operatorname, Grp(V(s))), [.. xs]);
    private static Formula All(string s, Formula t, Formula x) => Seq(Forall, Sp, V(s), Colon, Sp, t, Comma, Sp, Par(x));
    private static Formula Mul(Formula x, Formula y) => Seq(Par(x), Sp, Cdot, Sp, Par(y));
    private static Formula Sub(Formula x, Formula y) => Seq(Par(x), Sp, Minus, Sp, Par(y));
    private static Formula Pow(Formula x, Formula y) => Seq(Par(x), Caret, Grp(y));
    private static Formula Norm(Formula x) => Seq(Vert, Sp, x, Sp, Vert);
    private static Formula Energy(Formula x) => Pow(Norm(x), D(2));
    private static Formula SumA(Formula x) => Seq(new Formula.Subscript(Sum, Seq(V("p"), InMacro, V("A"))), Sp, x);
    private static Formula ResultFormula()
    {
        Formula p=V("p"), z=V("z"), u=V("u"), h=V("h");
        Formula addr=Call("Address"), edge=Call("Edge"), hs=Call("H");
        Formula sz=Call("S",p,z), d=Call("descendant",p,u);
        Formula coeff=Seq(Frac,Grp(Pow(V("a"),Seq(h,Plus,D(1)))),Grp(Sub(D(1),V("a"))));
        Formula coordinates=All("p",addr,All("z",hs,All("u",edge,
            Seq(Call("coordinate",sz,u),Eq,Call("coordinate",z,d)))));
        Formula strict=All("p",addr,All("u",edge,Seq(Call("length",p),Lt,Call("length",d))));
        Formula empty=All("z",hs,Seq(Call("S",Call("empty"),z),Eq,z));
        Formula energy=All("A",Call("Finset",addr),Seq(Call("PrefixFree",V("A")),Implies,
            All("z",hs,Seq(SumA(Energy(sz)),Leq,Energy(z)))));
        Formula series=All("p",addr,All("z",hs,Call("HasSum",
            Par(Seq(u,Colon,edge,Mapsto,Mul(Call("coordinate",z,d),Call("indicator",u)))),Call("suffixTrace",p,z))));
        Formula tail=All("A",Call("Finset",addr),Seq(Call("PrefixFree",V("A")),Implies,
            All("h",Seq(Mathbb,Grp(V("N"))),All("z",hs,
                Seq(SumA(Energy(Call("J",Sub(sz,Call("P",h,sz))))),Leq,Mul(coeff,Energy(z)))))));
        return Seq(Par(coordinates),Land,Par(strict),Land,Par(empty),Land,Par(energy),Land,Par(series),Land,Par(tail));
    }
}

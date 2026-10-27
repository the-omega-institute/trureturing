using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Geometry;

internal sealed class BiasedBoundaryPathSplitDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryPathSplit.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual boundary path sum splits at every finite original prefix, for every square summable increment vector, in the common suffix L2 space.",
        H("Strict Suffixes and Conditional Path Sums"), Blocks(
            Def("descendant", "Appending a nonempty suffix to p gives a nonempty original edge. This address map is injective."),
            Def("S", "The suffix operator has coordinate S(p)z at u equal to z at p appended to u. Only nonempty u occur, so the edge p and its ancestors are excluded. Injective restriction of the square summable coordinates gives a contraction on the original H."),
            Def("prefixes", "The finite set consists of the nonempty original prefixes of p. It includes p when p is nonempty and is empty when p is empty."),
            Def("prefixSum", "The prefix functional sums the original increment coordinates over this finite set. It is continuous because every coordinate evaluation is continuous."),
            Def("constG", "The continuous constant embedding sends c to the actual constant function c in the same L2(M) that contains Jz."),
            Describe.Lean(DescribeId.Create("biasedboundarypathsplit-allh"),
                DeclarationHandle.Create(Prefix + "boundary_path_split"), H("The All Vector Path Split"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every finite p and every z in the original H, the conditional pullback of Jz equals the constant finite prefix sum plus J applied to the strict suffix vector. The equality is in the original suffix L2(M). The pullback uses the actual normalized restricted law; no ambient measure preservation is imposed on prepend.")),
                    Paragraph(Text("On a single increment at q, a prefix q of p contributes the constant increment. A strict descendant q of p contributes precisely the indicator of its nonempty suffix cylinder. Incomparable addresses contribute zero. These alternatives follow from the original address coordinates and include equality q=p in the prefix case.")),
                    Paragraph(Text("The identity on single increments extends by continuity of the pullback, J, the finite prefix functional and the suffix contraction. Continuous linear maps on ell2 are determined by the single increments, so this proves the identity for every square summable z. No finite support restriction remains, and an empty p gives a zero prefix sum and the unchanged suffix vector.")),
                    Paragraph(Text("The centered mass stopping projection and its weighted residual norm formula require additional results. No spectral operator, covariance or eigenvalue counting assertion is made here."))), DescribeRole.Theorem))));

    private static DocumentBlock Def(string name, string prose) => Describe.Lean(
        DescribeId.Create("biasedboundarypathsplit-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(name), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula V(string s) => F.Id(s);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Seq(Operatorname, Grp(V(s))), [.. xs]);
    private static Formula All(string s, Formula t, Formula x) => Seq(Forall, Sp, V(s), Colon, Sp, t, Comma, Sp, Par(x));
    private static Formula Norm(Formula x) => Seq(Vert, Sp, x, Sp, Vert);
    private static Formula ResultFormula()
    {
        Formula p=V("p"), z=V("z"), u=V("u"), c=V("c"), addr=Call("Address"), h=Call("H"), edge=Call("Edge");
        Formula coordinates=All("p",addr,All("z",h,All("u",edge,Seq(Call("S",p,z,u),Eq,Call("apply",z,Call("descendant",p,u))))));
        Formula bound=All("p",addr,All("z",h,Seq(Norm(Call("S",p,z)),Leq,Norm(z))));
        Formula prefix=All("p",addr,All("z",h,Seq(Call("prefixSum",p,z),Eq,Call("sum",Call("prefixes",p),z))));
        Formula constant=All("c",R,Call("aeEq",V("M"),Call("constG",c),Call("constant",c)));
        Formula split=All("p",addr,All("z",h,Seq(Call("pullback",p,Call("J",z)),Eq,Call("constG",Call("prefixSum",p,z)),Plus,Call("J",Call("S",p,z)))));
        return Seq(Par(coordinates),Land,Par(bound),Land,Par(prefix),Land,Par(constant),Land,Par(split));
    }
}

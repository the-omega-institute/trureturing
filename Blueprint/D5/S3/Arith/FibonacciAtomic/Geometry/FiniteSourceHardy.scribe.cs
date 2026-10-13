using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Geometry;

internal sealed class FiniteSourceHardyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceHardy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The common real edge ell2 maps into each actual source node L2 with a uniform geometric tail.", H("Uniform Native Hardy Tails"), Blocks(
            Def("Edge", "Edge consists precisely of nonempty original Bool addresses. The empty root is not a coordinate."),
            Def("H", "H is lp with exponent two over the real Edge coordinates, common to every source."),
            Def("NodeL2", "NodeL2(n) is the real Lp space with exponent two for the actual uniform all-occurrence measure mu(n). The codomain depends on n."),
            Def("edges", "edges(n) contains exactly the nonempty addresses occurring in vertices(n)."),
            Def("path", "path(n,h,x) contains actual nonempty prefixes of x whose length is greater than h."),
            Def("value", "value(n,h,z,x) is the sum of z over path(n,h,x). Missing addresses have no term. The value at the root is zero."),
            Def("trace", "trace(n,h,z) is that actual path function in NodeL2(n)."),
            Def("projectionLinear", "projectionLinear(h) retains coordinates of length at most h and sets all other coordinates to zero."),
            Def("P", "P(h) is the bounded coordinate projection induced by projectionLinear(h)."),
            Def("J", "J(n) is the actual root-path increment map into NodeL2(n). Its value is trace(n,0,z)."),
            Describe.Lean(DescribeId.Create("finitesourcehardy-result"),
                DeclarationHandle.Create(Prefix + "finite_source_hardy"), H("Uniform Native Hardy Tails"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The coefficient bound holds for every natural source index and every address. The trace and operator bounds hold for every natural n and h, including zero, on the same real edge ell2. The operator in the final clause is J(n) composed with I-P(h). Each J(n) retains its own actual node L2 codomain.")),
                    Paragraph(Text("A root path has at most one prefix of each length. Its weights a to the prefix length therefore sum to at most a to the power h+1 divided by 1-a. Weighted Cauchy-Schwarz bounds the square of the path sum by this weight sum times the sum of squared increments divided by their weights.")),
                    Paragraph(Text("Integrating over the actual node probability measure gives each increment its actual descendant mass. The native uniform mass envelope cancels the reciprocal weight. The remaining finite squared-coordinate sum is bounded by the ell2 energy. Taking square roots gives the operator-norm tail.")),
                    Paragraph(Text("This finite-source result supplies no boundary measure, limiting trace, compact extension, covariance convergence or screening formula."))), DescribeRole.Theorem))));

    private static DocumentBlock Def(string name, string prose) => Describe.Lean(
        DescribeId.Create("finitesourcehardy-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(name), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula V(string s) => F.Id(s);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Seq(Operatorname, Grp(V(s))), [.. xs]);
    private static Formula All(string s, Formula t, Formula x) => Seq(Forall, Sp, V(s), Colon, Sp, t, Comma, Sp, Par(x));
    private static Formula LeOf(Formula x, Formula y) => Seq(x, Sp, Leq, Sp, y);
    private static Formula And(Formula x, Formula y) => Seq(Par(x), Sp, Land, Sp, Par(y));
    private static Formula Add(Formula x, Formula y) => Seq(Par(x), Sp, Plus, Sp, Par(y));
    private static Formula Sub(Formula x, Formula y) => Seq(Par(x), Sp, Minus, Sp, Par(y));
    private static Formula Mul(Formula x, Formula y) => Seq(Par(x), Sp, Cdot, Sp, Par(y));
    private static Formula Div(Formula x, Formula y) => Seq(Frac, Grp(x), Grp(y));
    private static Formula Pow(Formula x, Formula y) => Seq(Par(x), Caret, Grp(y));
    private static Formula Norm(Formula x) => Seq(Vert, Sp, x, Sp, Vert);
    private static Formula NatType => Seq(Mathbb, Grp(V("N")));
    private static Formula Conj(params Formula[] xs) => xs.Aggregate(And);
    private static Formula Bounds(string[] names, Formula[] types, Formula body)
    {
        for (int i=names.Length-1; i>=0; --i) body=All(names[i], types[i], body);
        return body;
    }
    private static Formula ResultFormula()
    {
        Formula n=V("n"), h=V("h"), z=V("z"), p=V("p");
        Formula k=Mul(D(2),Call("goldenRatio"));
        Formula coeff=Div(Mul(k,Pow(V("a"),Add(h,D(1)))),Sub(D(1),V("a")));
        Formula first=Bounds(["n","p"],[NatType,Call("Address")],
            LeOf(Call("mass",n,p),Mul(k,Pow(V("a"),Call("length",p)))));
        Formula second=Bounds(["n","h","z"],[NatType,NatType,Call("H")],
            LeOf(Pow(Norm(Call("J",n,Sub(z,Call("P",h,z)))),D(2)),Mul(coeff,Pow(Norm(z),D(2)))));
        Formula third=Bounds(["n","h"],[NatType,NatType],
            LeOf(Norm(Call("comp",Call("J",n),Sub(Call("I"),Call("P",h)))),Seq(Sqrt,Grp(coeff))));
        return Conj(first,second,third);
    }
}

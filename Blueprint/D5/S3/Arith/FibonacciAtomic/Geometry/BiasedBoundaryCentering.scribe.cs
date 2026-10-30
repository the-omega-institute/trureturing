using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Geometry;

internal sealed class BiasedBoundaryCenteringDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCentering.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual integral centering on the biased boundary cancels both the finite prefix constant and the global centering constant in every conditional suffix trace.",
        H("Centering and Conditional Suffix Residuals"), Blocks(
            Def("mean", "The mean functional is the L2 inner product with the actual constant one. Since M is a probability measure, this constant has norm one and the functional equals the actual integral with respect to M."),
            Def("Pi", "Pi is the orthogonal projection onto the orthogonal complement of the span of the actual constant one. Its ambient formula is F minus the constant function with value mean(F)."),
            Def("C", "The centered trace is C=Pi composed with the original J. Its values are included in the original ambient G when conditional pullbacks are applied."),
            Describe.Lean(DescribeId.Create("biasedboundarycentering-constantnorm"),
                DeclarationHandle.Create(Prefix + "constG_norm_one"), H("The Boundary Constant Has Unit Norm"),
                StatementSource.FromAuthor(Seq(Norm(Call("constG",D(1))),Eq,D(1))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The original Bernoulli boundary law is a probability measure, so its constant one has L2 norm one."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("biasedboundarycentering-piconst"),
                DeclarationHandle.Create(Prefix + "Pi_const"), H("Constants Are Removed by Centering"),
                StatementSource.FromAuthor(All("c",Seq(Mathbb,Grp(V("R"))),
                    Seq(Call("Pi",Call("constG",V("c"))),Eq,D(0)))),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every real c, the original mean of constG(c) is c. The formula for Pi subtracts that same constant and gives zero. This identity removes constants in the centered suffix, free-root form and boundary operator."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("biasedboundarycentering-suffixresidual"),
                DeclarationHandle.Create(Prefix + "centered_suffix_residual"), H("The Actual Centered Suffix"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every F in G the mean equals its M integral, mean sends the constant c to c, and Pi subtracts that constant mean. Orthogonal projection makes Pi a contraction.")),
                    Paragraph(Text("For every original finite prefix p and every original z in H, first pulling back Cz and then centering in the suffix L2(M) gives exactly C applied to the strict suffix vector S(p)z. Conditional composition fixes constants. The all-vector path split therefore cancels both the finite prefix sum and the constant subtracted by global centering.")),
                    Paragraph(Text("The squared norm of this centered conditional suffix is at most the golden ratio times the squared norm of S(p)z. This follows from the contraction of Pi and the original all-vector Hardy bound for J, using the original golden biased parameter.")),
                    Paragraph(Text("This statement concerns centering in a fixed conditional suffix space for each p. Identifying the global stopping-cylinder atom-average operator, summing the weighted conditional norms, and proving the global threshold bound require further results. No covariance or spectral counting assertion is made."))), DescribeRole.Theorem))));
    private static DocumentBlock Def(string name, string prose) => Describe.Lean(
        DescribeId.Create("biasedboundarycentering-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(name), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula V(string s) => F.Id(s);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Seq(Operatorname, Grp(V(s))), [.. xs]);
    private static Formula All(string s, Formula t, Formula x) => Seq(Forall, Sp, V(s), Colon, Sp, t, Comma, Sp, Par(x));
    private static Formula Norm(Formula x) => Seq(Vert, Sp, x, Sp, Vert);
    private static Formula Sq(Formula x) => Seq(Par(x),Caret,Grp(D(2)));
    private static Formula Mul(Formula x, Formula y) => Seq(Par(x),Sp,Cdot,Sp,Par(y));
    private static Formula ResultFormula()
    {
        Formula f=V("F"), c=V("c"), p=V("p"), z=V("z"), g=Call("G"), h=Call("H"), addr=Call("Address");
        Formula integral=All("F",g,Seq(Call("mean",f),Eq,Call("integral",V("M"),f)));
        Formula constant=All("c",Seq(Mathbb,Grp(V("R"))),Seq(Call("mean",Call("constG",c)),Eq,c));
        Formula projection=All("F",g,Seq(Call("Pi",f),Eq,f,Minus,Call("constG",Call("mean",f))));
        Formula contraction=All("F",g,Seq(Norm(Call("Pi",f)),Leq,Norm(f)));
        Formula residual=Call("Pi",Call("pullback",p,Call("C",z)));
        Formula identity=All("p",addr,All("z",h,Seq(residual,Eq,Call("C",Call("S",p,z)))));
        Formula bound=All("p",addr,All("z",h,Seq(Sq(Norm(residual)),Leq,Mul(Call("goldenRatio"),Sq(Norm(Call("S",p,z)))))));
        return Seq(Par(integral),Land,Par(constant),Land,Par(projection),Land,Par(contraction),Land,Par(identity),Land,Par(bound));
    }
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Geometry;

internal sealed class BiasedBoundaryCylinderProjectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCylinderProjection.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual normalized cylinder integrals define a finite average operator on the original biased boundary Hilbert space. Prefix freedom makes it the orthogonal projection onto the cylinder span.",
        H("Actual Cylinder Averages"), Blocks(
            Def("atomMean", "For a nonempty original address p, atomMean(p) is the inner product with the actual cylinder indicator, divided by the actual M mass of that cylinder. It is a continuous real functional on the original L2(M)."),
            Def("Q", "For a finite set A of original nonempty addresses, Q(A) is the sum over p in A of the actual cylinder indicator multiplied by atomMean(p). The operator is constructed as a finite sum of continuous linear maps."),
            Def("V", "V(A) is the real linear span in the original L2(M) of the actual indicators of the cylinders with addresses in A."),
            Def("V0", "V0(A) is the kernel of the actual mean restricted to V(A). Its elements are exactly the vectors in the actual cylinder span whose original M mean is zero."),
            Describe.Lean(DescribeId.Create("biasedboundarycylinderprojection-average"),
                DeclarationHandle.Create(Prefix + "cylinder_average_projection"), H("Normalized Means and Orthogonal Projection"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every finite A whose original addresses are prefix-free, atomMean(p)(F) equals the integral of F over the actual cylinder divided by its actual positive M mass, for every original nonempty p and every F in the original G. It also equals the mean of the actual conditional pullback of F to suffix rays.")),
                    Paragraph(Text("For every original F, Q(A)F is exactly the orthogonal projection of F onto V(A). In particular Q(A) fixes each indicator indexed by A. The cylinder span is finite dimensional.")),
                    Paragraph(Text("Two distinct prefix-free addresses have disjoint actual cylinders. Their indicators are therefore orthogonal, their squared norms are their actual cylinder masses, and each normalized atom mean extracts its own indicator coefficient. Thus Q(A)F lies in the span and F minus Q(A)F is orthogonal to that span, which characterizes the projection.")),
                    Paragraph(Text("The actual normalized integral is related to suffix composition by the original measure-preserving map from M to the conditional cylinder law. No preservation of the ambient measure M by prepending is asserted."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("biasedboundarycylinderprojection-residual"),
                DeclarationHandle.Create(Prefix + "partition_centered_residual"), H("The Exact Partition Residual"),
                StatementSource.FromAuthor(ResidualFormula()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Suppose the finite prefix-free family A covers every original infinite ray. For every p in A and every F in G, the conditional pullback of Q(A)F is the actual constant with value atomMean(p)(F). Consequently, for every original z in H, the conditional pullback of Cz minus Q(A)Cz equals exactly C(S(p)z).")),
                    Paragraph(Text("For every F in the original G, its squared norm equals the sum over A of the actual cylinder mass times the squared norm of its conditional pullback. Apply the measure-preserving identification with the normalized restriction separately on each cylinder, then sum the disjoint cylinder integrals over the covering partition. Applying this identity to Cz minus Q(A)Cz gives exactly the weighted sum of the squared norms of C(S(p)z).")),
                    Paragraph(Text("The same constructed Q(A) fixes every actual constant and commutes with Pi. The constant identity follows by summing its actual atom values on the partition. Orthogonal symmetry then shows that Q(A) preserves the actual mean, and the formula for Pi gives commutation.")),
                    Paragraph(Text("The dimension of V(A) is exactly the number of addresses in A. Indeed applying each actual atom mean to a linear relation among the indicators extracts that indicator's coefficient, so the indicators are linearly independent. The actual mean restricted to V(A) is nonzero because the actual constant one lies in V(A) and has mean one. Rank-nullity therefore gives dimension card(A) minus one for the actual mean-zero subspace V0(A)."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("biasedboundarycylinderprojection-bound"),
                DeclarationHandle.Create(Prefix + "bounded_partition_residual"), H("An Actual Mass Threshold Bound"),
                StatementSource.FromAuthor(BoundFormula()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Let t be nonnegative. If every actual M cylinder mass in the finite prefix-free covering family A is at most t, then for every original z in H the squared norm of Cz minus Q(A)Cz is at most the golden ratio times t times the squared norm of z. This follows by applying the weighted disjoint-suffix estimate to the exact residual decomposition.")),
                    Paragraph(Text("The hypothesis is a bound on the actual cylinder masses. Applying this theorem to every weak first mass crossing for zero less than t less than one additionally requires identifying the actual Bernoulli cylinder masses with the frozen product-mass frontier. The all-threshold specialization, the covariance equality and the spectral counting conclusions are not asserted here."))), DescribeRole.Theorem))));
    private static DocumentBlock Def(string name, string prose) => Describe.Lean(
        DescribeId.Create("biasedboundarycylinderprojection-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(name), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula V(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Seq(Operatorname, Grp(V(s))), [.. xs]);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula All(string s, Formula t, Formula x) => Seq(Forall, Sp, V(s), Colon, Sp, t, Comma, Sp, Par(x));

    private static Formula SqNorm(Formula x) => Seq(Par(Seq(Vert, Sp,x,Vert)),Caret,Grp(D(2)));
    private static Formula SumA(Formula x) => Seq(Sum,Underscore,Grp(Seq(V("p"),InMacro, Sp,V("A"))),Sp,Par(x));
    private static Formula ResidualFormula()
    {
        Formula p=V("p"), f=V("F"), a=V("A"), z=V("z");
        Formula residual=Seq(Call("C",z),Minus,Call("Q",a,Call("C",z)));
        Formula onAtom=Seq(Forall,Sp,p,InMacro, Sp,a,Comma,Sp,All("F",Call("G"),
            Seq(Call("pullback",p,Call("Q",a,f)),Eq,Call("constG",Call("atomMean",p,f)))));
        Formula local=Seq(Forall,Sp,p,InMacro, Sp,a,Comma,Sp,All("z",Call("H"),
            Seq(Call("pullback",p,Par(residual)),Eq,Call("C",Call("S",p,z)))));
        Formula disintegration=All("F",Call("G"),Seq(SqNorm(f),Eq,
            SumA(Seq(Call("mass",V("M"),Call("cylinder",p)),Cdot, Sp,SqNorm(Call("pullback",p,f))))));
        Formula norm=All("z",Call("H"),Seq(SqNorm(Par(residual)),Eq,
            SumA(Seq(Call("mass",V("M"),Call("cylinder",p)),Cdot, Sp,SqNorm(Call("C",Call("S",p,z)))))));
        Formula constants=All("c",Call("Real"),Seq(Call("Q",a,Call("constG",V("c"))),Eq,Call("constG",V("c"))));
        Formula commutation=All("F",Call("G"),Seq(Call("Q",a,Call("Pi",f)),Eq,Call("Pi",Call("Q",a,f))));
        Formula dimensions=Seq(Call("dim",Call("V",a)),Eq,Call("card",a),Land, Sp,
            Call("dim",Call("V0",a)),Eq,Call("card",a),Minus,D(1));
        return Seq(Call("IsCylinderPartition",a),Implies, Sp,Par(onAtom),Land, Sp,Par(local),Land, Sp,
            Par(disintegration),Land, Sp,Par(norm),Land, Sp,Par(constants),Land, Sp,Par(commutation),Land, Sp,Par(dimensions));
    }
    private static Formula BoundFormula() => Seq(
        Call("IsCylinderPartition",V("A")),Land, Sp,D(0),Leq, Sp,V("t"),Land, Sp,
        Par(Seq(Forall,Sp,V("p"),InMacro, Sp,V("A"),Comma,Sp,Call("mass",V("M"),Call("cylinder",V("p"))),Leq, Sp,V("t"))),Implies, Sp,
        SqNorm(Par(Seq(Call("C",V("z")),Minus,Call("Q",V("A"),Call("C",V("z")))))),Leq, Sp,
        Call("goldenRatio"),Cdot, Sp,V("t"),Cdot, Sp,SqNorm(V("z")));
    private static Formula ResultFormula()
    {
        Formula p=V("p"), f=V("F"), a=V("A"), edge=Call("Edge"), g=Call("G");
        Formula normalized=All("p",edge,All("F",g,Seq(Call("atomMean",p,f),Eq,Call("normalizedSetIntegral",V("M"),Call("cylinder",p),f))));
        Formula pullback=All("p",edge,All("F",g,Seq(Call("atomMean",p,f),Eq,Call("mean",Call("pullback",p,f)))));
        Formula projection=All("F",g,Seq(Call("Q",a,f),Eq,Call("starProjection",Call("V",a),f)));
        Formula fixedAtoms=Seq(Forall,Sp,p,InMacro, Sp,a,Comma,Sp,Call("Q",a,Call("indicator",p)),Eq,Call("indicator",p));
        return Seq(Call("IsPrefixFree",Call("addresses",a)),Implies, Sp,Par(normalized),Land, Sp,Par(pullback),Land, Sp,Par(projection),Land, Sp,Par(fixedAtoms));
    }
}

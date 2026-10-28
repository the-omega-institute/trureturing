using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Geometry;

internal sealed class BiasedBoundaryStoppingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryStopping.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every weak mass threshold gives an actual finite cylinder projection and an all-vector residual bound.",
        H("Weak Stopping on the Original Biased Boundary"), Blocks(
            Def("Threshold", "A threshold t is any real number strictly between zero and one. The endpoints are excluded; equality of a cylinder mass with t is included as a stopping event."),
            Def("A", "A(t) is the finite first-crossing frontier, converted to the original edge type of nonempty addresses. An address p belongs exactly when mass(p) is at most t and the mass of p with its last letter deleted is strictly greater than t."),
            Def("Qt", "Qt(t) is Q(A(t)), the continuous linear sum of the actual stopping-cylinder indicators multiplied by their normalized actual M integrals. It acts on the original G=L2(M)."),
            Def("Vt", "Vt(t) is the span of those actual cylinder indicators in G, the finite cylinder-constant space."),
            Def("Vt0", "Vt0(t) is the kernel of the actual mean restricted to Vt(t)."),
            Def("G0", "G0 is the kernel of the actual M mean in G, with its inherited subspace structure."),
            Describe.Lean(DescribeId.Create("biasedboundarystopping-partition"),
                DeclarationHandle.Create(Prefix + "actual_stopping_partition"), H("The Actual Weak Crossing Partition"),
                StatementSource.FromAuthor(PartitionFormula()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every original address p, including the empty address, the real M mass of its cylinder equals wordMass(letterMass(a,b),p). Both products use a at false and b at true. Here a is the reciprocal golden ratio, b is its square, both are positive, b is at most a, a is less than one, and a+b=1.")),
                    Paragraph(Text("For every t between zero and one, the existing first-mass-frontier theorem supplies a finite prefix-free family with exactly the weak condition mass(p)<=t<mass(parent(p)). Every word in it is nonempty. Converting it to the original edge subtype preserves its words, cardinality, product masses and finite depth bound.")),
                    Paragraph(Text("An original ray lies in cylinder(p) exactly when p is its prefix of length length(p). The unique frontier prefix on every ray therefore gives a unique actual stopping cylinder. Thus the cylinders cover all of the original ray space and are disjoint.")),
                    Paragraph(Text("Every actual stopping mass is strictly greater than b*t and at most t. Their sum is exactly one, and the number k of stopping addresses satisfies 1/t<=k<1/(b*t). These are the same Bernoulli masses and the same nonempty original coordinates used by the boundary trace, including all threshold equality cases."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("biasedboundarystopping-residual"),
                DeclarationHandle.Create(Prefix + "actual_stopping_residual"), H("Actual Projection and Residual at Every Threshold"),
                StatementSource.FromAuthor(ResidualFormula()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every t between zero and one and every original F in G, Qt(t)F is exactly the orthogonal projection onto Vt(t). Its value on the conditional suffix copy of a stopping cylinder p is the constant atomMean(p)(F), namely the actual integral of F over that cylinder divided by its actual positive M mass.")),
                    Paragraph(Text("For every original z in H and every p in A(t), the actual conditional pullback of Cz-Qt(t)Cz is exactly C(S(p)z). The suffix map retains the coordinates z(p++u) for nonempty u only, hence only strict descendants of p. The original empty-prefix path-split identity and the actual centering map remain unchanged.")),
                    Paragraph(Text("For every F in the original G, its squared norm is exactly the sum over A(t) of the actual mass of cylinder(p) times the squared norm of its conditional pullback. Applied to Cz-Qt(t)Cz, this is exactly the mass-weighted sum of the squared norms of C(S(p)z). No finite-support restriction on z is imposed.")),
                    Paragraph(Text("For every original z in H, the resulting squared residual norm is at most goldenRatio*t times the squared norm of z. The actual stopping masses are at most t, the centered trace bound gives the golden-ratio factor, and the strict-descendant coordinate sets are disjoint. Their total squared edge norm is at most the original squared edge norm, so no additional factor of two occurs.")),
                    Paragraph(Text("The same Qt(t) fixes every actual constant and commutes with Pi. Vt(t) has dimension card(A(t)); Vt0(t) has dimension card(A(t))-1. Restricting the domain of Qt(t) to the actual mean-zero subspace G0 gives range exactly Vt(t) intersect G0. Indeed commutation with Pi keeps the output centered, and each centered vector in Vt(t) is fixed by the projection and is its own centered preimage.")),
                    Paragraph(Text("The mass-frontier and finite-partition results are applied with their original hypotheses and actual measure. The covariance quadratic-form equality, the comparison operator H, and the spectral and counting statements require separate identifications and are not conclusions of this result."))), DescribeRole.Theorem),
            Paragraph(Text("Compactness and the later spectral counting statements require separate identifications and are not conclusions of this result."))));

    private static DocumentBlock Def(string name, string prose) => Describe.Lean(
        DescribeId.Create("biasedboundarystopping-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(name), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula V(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Seq(Operatorname, Grp(V(s))), [.. xs]);
    private static Formula Par(Formula x) => Seq(Open,x,Close);
    private static Formula All(string s, Formula type, Formula x) => Seq(Forall,Sp,V(s),Colon,Sp,type,Comma,Sp,Par(x));
    private static Formula SqNorm(Formula x) => Seq(Par(Seq(Vert,x,Vert)),Caret,Grp(D(2)));
    private static Formula SumA(Formula x) => Seq(Sum,Underscore,Grp(Seq(V("p"),InMacro,Sp,Call("A",V("t")))),Sp,Par(x));
    private static Formula PartitionFormula() => All("t",Call("Threshold"),Seq(
        Call("IsPrefixFree",Call("A",V("t"))),Land,Sp,
        Call("UniqueCylinderCover",Call("A",V("t")),V("M")),Land,Sp,
        SumA(Call("mass",V("p"))),Eq,D(1),Land,Sp,
        D(1),Slash,V("t"),Leq,Sp,Call("card",Call("A",V("t"))),Lt,Sp,
        D(1),Slash,Par(Seq(V("b"),Cdot,Sp,V("t")))));
    private static Formula ResidualFormula()
    {
        Formula t=V("t"), z=V("z"), p=V("p"), f=V("F");
        Formula r=Seq(Call("C",z),Minus,Call("Qt",t,Call("C",z)));
        Formula local=Seq(Forall,Sp,p,InMacro,Sp,Call("A",t),Comma,Sp,
            All("z",Call("H"),Seq(Call("pullback",p,Par(r)),Eq,Call("C",Call("S",p,z)))));
        Formula global=All("z",Call("H"),Seq(SqNorm(Par(r)),Eq,
            SumA(Seq(Call("mass",p),Cdot,Sp,SqNorm(Call("C",Call("S",p,z))))),Leq,Sp,
            Call("goldenRatio"),Cdot,Sp,t,Cdot,Sp,SqNorm(z)));
        Formula dimensions=Seq(Call("dim",Call("Vt",t)),Eq,Call("card",Call("A",t)),Land,Sp,
            Call("dim",Call("Vt0",t)),Eq,Call("card",Call("A",t)),Minus,D(1));
        Formula range=Seq(Call("range",Call("restrict",Call("Qt",t),V("G0"))),Eq,
            Call("intersection",Call("Vt",t),V("G0")));
        return All("t",Call("Threshold"),Seq(Par(local),Land,Sp,Par(global),Land,Sp,
            All("F",Call("G"),Seq(Call("Qt",t,f),Eq,Call("starProjection",Call("Vt",t),f))),Land,Sp,
            Par(dimensions),Land,Sp,Par(range)));
    }
}

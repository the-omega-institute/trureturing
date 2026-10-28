using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Geometry;

internal sealed class BiasedBoundaryOperatorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryOperator.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original infinite biased trace has dense range. Its free-root form has a densely defined self-adjoint realization with exactly the constant zero modes.",
        H("The Actual Biased Boundary Operator"), Blocks(
            Def("centeredTrace", "This is the original C=Pi J with codomain the actual mean-zero subspace G0 of L2(M). Its domain is the original infinite edge ell2. The product law M has the original golden biased probabilities."),
            Def("boundaryCovariance", "The boundary covariance is CC* acting on the original ambient L2(M). It maps into G0 and annihilates constants. It is distinct from the edge covariance Sigma=C*C, whose kernel can be large."),
            Def("boundaryOperator", "The boundary operator is the partially defined linear map obtained from the exact graph mean(h)=0 and Pi(u)=CC*h. Its graph is proved to equal the weak variational graph of the original domain D={constG(c)+Jz} and the pairing of the attained original increment energy. Its definition assumes no operator realization or spectral conclusion."),
            Describe.Lean(DescribeId.Create("biasedboundaryoperator-realization"),
                DeclarationHandle.Create(Prefix + "actual_self_adjoint_realization"),
                H("Self-Adjoint Realization of the Original Form"),
                StatementSource.FromAuthor(RealizationFormula()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Every prefix cylinder is measurable, and the prefix cylinders form a generating pi-system for the sigma algebra of the original infinite ray space. For coordinate i and a prescribed bit, its inverse image is the union of the prefix cylinders of length i+1 carrying that bit. A vector annihilated by J* has zero integral on every nonempty cylinder because each cylinder indicator is the trace of an original single edge increment. The two first cylinders also give zero integral on the entire boundary. Uniqueness of vector measures on a generating pi-system forces the vector to vanish almost everywhere. Thus J has dense range, and projection gives dense range of the actual centered trace in G0. The original form domain is dense as it contains every Jz.")),
                    Paragraph(Text("The actual stopping spaces establish infinite dimension. If G0 had dimension d, choose the stopping threshold 1/(d+2). The mass lower bound gives at least d+2 stopping cylinders, and their mean-zero span has dimension at least d+1. Its natural inclusion into G0 is injective, contradicting dimension d.")),
                    Paragraph(Text("The weak graph is single-valued: CC*h=0 with mean(h)=0 implies C*h=0, and density of the original trace implies h=0. Constants and the pairs (CC*k,Pi k) belong to the graph. Testing them shows that its domain has trivial orthogonal complement and is dense. The same tests identify the orthogonal adjoint graph with the graph itself, giving self-adjointness as a partially defined Hilbert-space operator. The graph equality identifies this operator with the self-adjoint realization of the original free-root energy. At zero output, the graph equation is Pi(u)=0, so precisely the real constants are zero modes.")),
                    Paragraph(Text("The polar unitary, its range and domain identities, the ordered positive eigenvalue sequence, compact resolvent and global counting bounds require further results. Infinite dimension and self-adjoint realization alone do not assert these spectral conclusions."))), DescribeRole.Theorem))));

    private static DocumentBlock Def(string name, string prose) => Describe.Lean(
        DescribeId.Create("biasedboundaryoperator-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(name), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula V(string s) => F.Id(s);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Seq(Operatorname, Grp(V(s))), [.. xs]);
    private static Formula All(string s, Formula t, Formula x) => Seq(Forall,Sp,V(s),Colon,Sp,t,Comma,Sp,Par(x));
    private static Formula And(params Formula[] xs) => Seq([.. xs.SelectMany((x,i) => i==0 ? new[] { Par(x) } : new[] { Land,Par(x) })]);
    private static Formula RealizationFormula()
    {
        Formula op=V("boundaryOperator"), g=V("G"), u=V("u"), h=V("h");
        Formula graph=Call("graph",op);
        return And(Call("DenseRange",V("J")),Call("DenseRange",V("centeredTrace")),
            Seq(Neg,Sp,Call("FiniteDimensional",Seq(Mathbb,Grp(V("R"))),V("Gzero"))),
            Call("Dense",V("D")),Call("Dense",Call("domain",op)),Call("IsSelfAdjoint",op),
            All("u",g,All("h",g,Seq(Call("pair",u,h),InMacro,Sp,graph,Iff,Call("weakGraph",u,h)))),
            All("u",g,Seq(Call("pair",u,D(0)),InMacro,Sp,graph,Iff,
                Exists,Sp,V("c"),Colon,Sp,Seq(Mathbb,Grp(V("R"))),Comma,Sp,u,Eq,Call("constG",V("c")))));
    }
}

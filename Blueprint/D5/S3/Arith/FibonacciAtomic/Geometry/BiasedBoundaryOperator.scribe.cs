using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Geometry;

internal sealed class BiasedBoundaryOperatorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryOperator.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original infinite biased trace has dense range. Its free-root form has a densely defined self-adjoint realization, a compact resolvent, exactly the constant zero modes and a multiplicity-preserving positive covariance eigenspace identification.",
        H("The Actual Biased Boundary Operator"), Blocks(
            Def("centeredTrace", "This is the original C=Pi J with codomain the actual mean-zero subspace G0 of L2(M). Its domain is the original infinite edge ell2. The product law M has the original golden biased probabilities."),
            Def("boundaryCovariance", "The boundary covariance is CC* acting on the original ambient L2(M). It maps into G0 and annihilates constants. It is distinct from the edge covariance Sigma=C*C, whose kernel can be large."),
            Def("boundaryResolvent", "Writing A=CC*, positivity gives the bounded inverse T=(I+A)^(-1). The actual resolvent is constG composed with mean, plus A composed with T. The theorem proves its two-sided inverse graph equation for the same boundaryOperator, rather than assuming resolvent data."),
            Def("boundaryEigenspace", "For every real lambda, this is the submodule of actual G consisting of u for which (u,lambda u) belongs to the entire graph of the original boundaryOperator. It includes the operator domain condition."),
            Def("covarianceEigenEquiv", "For each positive mu, this linear equivalence sends a vector z in the full mu eigenspace of the original Sigma=C*C to Cz in the mu^(-1) eigenspace of the actual H. Its inverse sends u to mu^(-1) C*u. It acts on the complete eigenspaces, allowing repeated eigenvalues."),
            Def("boundaryOperator", "The boundary operator is the partially defined linear map obtained from the exact graph mean(h)=0 and Pi(u)=CC*h. Its graph is proved to equal the weak variational graph of the original domain D={constG(c)+Jz} and the pairing of the attained original increment energy. Its definition assumes no operator realization or spectral conclusion."),
            Describe.Lean(DescribeId.Create("biasedboundaryoperator-realization"),
                DeclarationHandle.Create(Prefix + "actual_self_adjoint_realization"),
                H("Self-Adjoint Realization of the Original Form"),
                StatementSource.FromAuthor(RealizationFormula()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Every prefix cylinder is measurable, and the prefix cylinders form a generating pi-system for the sigma algebra of the original infinite ray space. For coordinate i and a prescribed bit, its inverse image is the union of the prefix cylinders of length i+1 carrying that bit. A vector annihilated by J* has zero integral on every nonempty cylinder because each cylinder indicator is the trace of an original single edge increment. The two first cylinders also give zero integral on the entire boundary. Uniqueness of vector measures on a generating pi-system forces the vector to vanish almost everywhere. Thus J has dense range, and projection gives dense range of the actual centered trace in G0. The original form domain is dense as it contains every Jz.")),
                    Paragraph(Text("The actual stopping spaces establish infinite dimension. If G0 had dimension d, choose the stopping threshold 1/(d+2). The mass lower bound gives at least d+2 stopping cylinders, and their mean-zero span has dimension at least d+1. Its natural inclusion into G0 is injective, contradicting dimension d.")),
                    Paragraph(Text("The weak graph is single-valued: CC*h=0 with mean(h)=0 implies C*h=0, and density of the original trace implies h=0. Constants and the pairs (CC*k,Pi k) belong to the graph. Testing them shows that its domain has trivial orthogonal complement and is dense. The same tests identify the orthogonal adjoint graph with the graph itself, giving self-adjointness as a partially defined Hilbert-space operator. The graph equality identifies this operator with the self-adjoint realization of the original free-root energy. At zero output, the graph equation is Pi(u)=0, so precisely the real constants are zero modes.")),
                    Paragraph(Text("The polar unitary, its range and domain identities, the ordered positive eigenvalue sequence and global counting bounds require further results. The subsequent theorem establishes compact resolvent directly on the same operator; it does not assume the polar formula."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("biasedboundaryoperator-resolvent"),
                DeclarationHandle.Create(Prefix + "actual_compact_resolvent"),
                H("Compact Resolvent of the Actual Operator"),
                StatementSource.FromAuthor(ResolventFormula()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Let A=CC* on the actual boundary L2 space. The pairing of (I+A)x with x is the sum of the squared norms of x and C*x. The pinned coercivity theorem therefore gives a bounded inverse T=(I+A)^(-1). Put R=constG composed with mean, plus A composed with T. Since C is the original stopping-derived compact map, A is compact. The constant part of R has rank at most one, so R is compact.")),
                    Paragraph(Text("The exact weak graph implies (I+A)u=constG(mean(u+h))+A(u+h). Conversely that equation implies mean(h)=0 and Pi(u)=Ah. Injectivity of I+A then proves that (u,h) belongs to the actual operator graph exactly when R(u+h)=u. Thus R is the actual two-sided inverse of H+I, including the constant mode. This proves compact resolvent without assuming a polar unitary or a spectral-counting target.")),
                    Paragraph(Text("For each positive real lambda, the actual eigenvector equation (u,lambda u) in graph(H) is equivalent to mean(u)=0 and Au=lambda^(-1)u. This is the inverse eigenvalue correspondence with the actual boundary covariance CC*. The following theorem identifies the complete eigenspaces with the original edge covariance C*C. A complete ordered spectral sequence and the literal polar expression in source equation (2.3) require additional results."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("biasedboundaryoperator-eigenspaces"),
                DeclarationHandle.Create(Prefix + "actual_covariance_eigenspaces"),
                H("The Original Covariance and Operator Eigenspaces"),
                StatementSource.FromAuthor(EigenspacesFormula()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For positive mu, intertwining CC* with C*C sends each original covariance eigenvector z to Cz. The inverse eigenvalue equation puts this trace in the actual boundary operator domain with eigenvalue mu^(-1). Conversely an actual operator eigenvector u at that value gives CC*u=mu u; applying C* and scaling gives the edge eigenvector mu^(-1)C*u. The two maps compose to the identity on both full eigenspaces. This is an explicit linear equivalence, so multiplicities are preserved without assuming simplicity.")),
                    Paragraph(Text("Each positive edge eigenvector is mu^(-1)C*Cz and hence lies in K, since the original adjoint range lies in K. Thus these are precisely the effective edge modes relevant to the source. The original stopping-derived compactness of Sigma and the pinned finite-eigenspace theorem make its nonzero eigenspaces finite dimensional. The explicit equivalence transfers this property to the actual operator eigenspaces.")),
                    Paragraph(Text("These results do not yet construct the polar unitary W or its range and domain identities, enumerate and exhaust the positive spectrum, establish divergence of an ordered sequence, or prove the original global counting inequalities. Source equation (2.3) in its literal W form and the full Theorem 2.1 remain unfinished."))), DescribeRole.Theorem))));

    private static DocumentBlock Def(string name, string prose) => Describe.Lean(
        DescribeId.Create("biasedboundaryoperator-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(name), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula V(string s) => F.Id(s);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Seq(Operatorname, Grp(V(s))), [.. xs]);
    private static Formula All(string s, Formula t, Formula x) => Seq(Forall,Sp,V(s),Colon,Sp,t,Comma,Sp,Par(x));
    private static Formula And(params Formula[] xs) => Seq([.. xs.SelectMany((x,i) => i==0 ? new[] { Par(x) } : new[] { Land,Par(x) })]);
    private static Formula EigenspacesFormula()
    {
        Formula m=V("mu"), z=V("z"), u=V("u");
        Formula e=Call("eigenspace",V("Sigma"),m);
        Formula b=Call("boundaryEigenspace",Call("inverse",m));
        Formula w=Call("covarianceEigenEquiv",m);
        return All("mu",Seq(Mathbb,Grp(V("R"))),Seq(D(0),Lt,m,Implies,Sp,And(
            All("z",e,Seq(z,InMacro,Sp,V("K"))),
            All("z",e,Seq(new Formula.Apply(w,[z]),Eq,Call("C",z))),
            All("u",b,Seq(new Formula.Apply(Call("inverse",w),[u]),Eq,
                Call("inverse",m),Call("adjoint",V("C"),u))),
            Call("FiniteDimensional",Seq(Mathbb,Grp(V("R"))),b))));
    }
    private static Formula ResolventFormula()
    {
        Formula g=V("G"), u=V("u"), h=V("h"), l=V("lambda");
        Formula r=V("boundaryResolvent"), a=V("boundaryCovariance");
        Formula graph=Call("graph",V("boundaryOperator"));
        Formula inverse=All("u",g,All("h",g,Seq(Call("pair",u,h),InMacro,Sp,graph,Iff,
            new Formula.Apply(r,[Par(Seq(u,Plus,h))]),Eq,u)));
        Formula eigen=All("lambda",Seq(Mathbb,Grp(V("R"))),Seq(D(0),Lt,l,Implies,Sp,
            All("u",g,Seq(Call("pair",u,Seq(l,u)),InMacro,Sp,graph,Iff,And(
                Seq(Call("mean",u),Eq,D(0)),
                Seq(new Formula.Apply(a,[u]),Eq,Call("inverse",l),u))))));
        return And(Call("IsCompactOperator",r),inverse,eigen);
    }
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

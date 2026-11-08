using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class JBAlgebraDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Natural powers in a real unital JB algebra multiply additively in their exponents and generate an associative closed real subspace whose multiplication operators commute on the entire ambient space.",
        H("Powers and the closed singly generated Jordan algebra"),
        Blocks(
            Paragraph(Text("Let X be a real normed vector space, S:X x X -> X a specified real bilinear map, and u a specified unit. Data(X,S,u) consists of exactly six laws, for every x,y in X: symmetry S(x,y)=S(y,x); S(u,x)=x; the Jordan identity S(S(x,y),S(x,x))=S(x,S(y,S(x,x))); norm(S(x,y))<=norm(x)norm(y); norm(S(x,x))=norm(x)^2; and norm(S(x,x))<=norm(S(x,x)+S(y,y)). All products and norms below are these same specified operations. There is no nonzero-space, dimension, completeness, specialness or ambient associativity hypothesis.")),
            Paragraph(Text("Write p(a,0)=u and p(a,n+1)=S(a,p(a,n)). Write L(x) for the continuous real linear map v -> S(x,v) on all of X. Product norm domination proves its continuity. Let C(a) be the norm closure in X of the real linear span of {p(a,n): n is a natural number}. In an incomplete X this is the relative closure in X, without introducing a completion.")),
            Describe.Lean(DescribeId.Create("polarized-jordan-commutator"),
                DeclarationHandle.Create("D5/S3/Topology/JBAlgebra.polarized"),
                H("The polarized Jordan commutator identity"), StatementSource.FromAuthor(F.Disp(PolarizedStatement())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Define bracket(S,a,b,v)=S(a,S(b,v))-S(b,S(a,v)), the commutator of left multiplication by a and b applied to an arbitrary ambient vector v. Mathlib's polarized Jordan identity gives twice the cyclic sum equal to zero; cancellation of the nonzero real scalar two gives the displayed identity. Only Data on the original real normed carrier is assumed.")))),
            Describe.Lean(DescribeId.Create("power-multiplication"),
                DeclarationHandle.Create("D5/S3/Topology/JBAlgebra.power_mul"),
                H("All natural powers"), StatementSource.FromAuthor(F.Disp(PowerStatement())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("A simultaneous induction on total degree proves power multiplication and ambient operator commutation. The induction assumes only smaller total degrees. To multiply p(a,i) by p(a,j+1), commute multiplication by p(a,i) past multiplication by a using the smaller-degree operator assertion, and then use the smaller-degree product assertion. The unit and j=0 cases are handled separately.")))),
            Describe.Lean(DescribeId.Create("ambient-power-commutation"),
                DeclarationHandle.Create("D5/S3/Topology/JBAlgebra.power_lmul_commute"),
                H("Commutation on every ambient vector"), StatementSource.FromAuthor(F.Disp(CommuteStatement())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Mathlib's polarized Jordan identity gives [L(x),L(S(y,z))]+[L(y),L(S(z,x))]+[L(z),L(S(x,y))]=0. For fixed total degree N and arbitrary ambient v, put c(k)=[L(p(a,k)),L(p(a,N-k))]v. Smaller-degree multiplication turns the identity into c(r)+c(s)+c(t)=0 whenever r,s,t are positive and sum to N. Skew symmetry gives c(N-k)=-c(k). Taking r=1 yields c(k)=k c(1) for k<N, hence N c(1)=0. Real scalar cancellation proves every c(k)=0. Degrees zero and one use the unit directly. This is a universal structural induction, rather than a finite-degree test or an associative model of X.")))),
            Describe.Lean(DescribeId.Create("closed-generated-algebra"),
                DeclarationHandle.Create("D5/S3/Topology/JBAlgebra.generated_algebra"),
                H("The actual closed span is an associative algebra"), StatementSource.FromAuthor(F.Disp(GeneratedStatement())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Linear span induction extends the two power assertions to linear combinations. Closed-set extension, separately in each variable of the same bounded bilinear S, then extends them to C(a). Membership in C(a) is a closed condition; equality of the two ambient-vector expressions is also closed. Thus C(a) is closed under S and every two of its elements have commuting multiplication operators on all of X. Applying this commutation to the third vector and using symmetry gives associativity on C(a). No operator is restricted to C(a) in the commutation assertion.")))),
            Paragraph(Text("A general analytic consequence uses Hilbert-space constructions. Let B:X ->L (X ->L R) be symmetric and nonnegative on the diagonal, on the specified original real normed X. On a separate copy V of its vector space, use B as a PreInnerProductSpace.Core and form H=UniformSpace.Completion(V). The original X norm and original continuous duals are unchanged. Since norm(Jx)^2=B(x,x)<=norm(B)norm(x)^2, the canonical linear J:X -> H is bounded by norm(B)+1. Mathlib's completion inner product gives inner(Jx,Jy)=B(x,y). Completion identifies the entire radical, so zero forms, zero spaces and nonzero null directions need no exceptional hypotheses.")),
            Paragraph(Text("Define the bounded T:H ->L X* by T(z)(x)=inner(z,Jx), using ContinuousLinearMap.compL and innerSL. For arbitrary F,G in the continuous bidual of the original X, InnerProductSpace.toDual and toDual_symm_apply give u,v in H satisfying inner(u,z)=F(T(z)) and inner(v,z)=G(T(z)) for every z. The original-continuous-functional identities G composed with B=T(v) and F composed with flip(B)=T(u) follow pointwise from inner(Jx,Jy)=B(x,y) and B symmetry. Therefore F(G composed with B)=inner(u,v)=inner(v,u)=G(F composed with flip(B)). No embedded-vector restriction is imposed on F or G.")),
            Paragraph(Text("For two continuous symmetric positive-semidefinite forms B1,B2, linearity gives G composed with (B1-B2)=(G composed with B1)-(G composed with B2), and the corresponding flipped identity for F. Subtracting their interchange equalities proves the exact interchange for B1-B2, without positivity of the difference. For the specified product S of Data, product_norm bundles S as a continuous bilinear M on the original norm. If continuous linear functionals P,Q satisfy phi=P-Q and P(S(x,x)),Q(S(x,x)) nonnegative, then BP(x,y)=P(S(x,y)) and BQ(x,y)=Q(S(x,y)) are continuous PSD forms by Data.symm, and phi composed with M=BP-BQ. The preceding subtraction gives the exact arbitrary-F,G evaluation equality for that phi.")),
            Paragraph(Text("This classical Hilbert-factorization argument claims no literature novelty. Its application to a JB functional phi is conditional on a positive-dual decomposition phi=P-Q. Applying it to every continuous phi requires construction of P,Q from the original Data together with completeness; this argument does not supply that step. No order, representation, positivity, dual-generation, Arens, nontriviality or unit-normalization premise is added to the original all-functional Arens equality problem. The argument does not establish JBW structure or the physical preparation needed for the quantum applications.")),
            Paragraph(Text("These are classical Jordan algebra facts; the local proof combines the pinned polarized identity with a natural-degree induction and topological closure. No literature novelty is claimed. In the pure-real original-domain setting of Unit 15.2, the same-S JB completion must first be constructed from the original data. The present result supplies the algebraic single-generator prerequisite, including the zero space and exceptional Jordan algebras. It does not construct square-root functional calculus, prove positivity of quadratic representations, build contraction semigroups or Abel operators, prove a quantitative commutator estimate, or discharge the original finite-certificate readback argument.")))));

    private static Formula V(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] args) => new Formula.Apply(V(s), [.. args]);
    private static Formula All(string s, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), type, body);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Product(Formula x, Formula y) => Call("S", x, y);
    private static Formula Power(Formula n) => Call("p", V("a"), n);
    private static Formula L(Formula x) => Call("L", x);
    private static Formula C => Call("C", V("a"));
    private static Formula Scope(Formula body) => All("X", V("RealNormedSpaces"),
        All("S", Call("RealBilinearMaps", V("X")), All("u", V("X"),
            Imp(Call("Data", V("X"), V("S"), V("u")), All("a", V("X"), body)))));
    private static Formula Bracket(string a, Formula b) => Call("bracket", V("S"), V(a), b, V("v"));
    private static Formula PolarizedStatement() => Scope(All("b", V("X"), All("c", V("X"), All("v", V("X"),
        Eq(Add(Add(Bracket("a", Product(V("b"), V("c"))), Bracket("b", Product(V("c"), V("a")))),
            Bracket("c", Product(V("a"), V("b")))), F.D(0))))));
    private static Formula PowerStatement() => Scope(All("m", V("Naturals"), All("n", V("Naturals"),
        Eq(Product(Power(V("m")), Power(V("n"))), Power(Add(V("m"), V("n")))))));
    private static Formula CommuteStatement() => Scope(All("m", V("Naturals"), All("n", V("Naturals"),
        Call("Commute", L(Power(V("m"))), L(Power(V("n")))))));
    private static Formula InC(string x, Formula body) => All(x, V("X"), Imp(Call("mem", V(x), C), body));
    private static Formula GeneratedStatement() => Scope(And(
        InC("x", InC("y", Call("mem", Product(V("x"), V("y")), C))),
        And(InC("x", InC("y", InC("z", Eq(Product(Product(V("x"), V("y")), V("z")),
            Product(V("x"), Product(V("y"), V("z"))))))),
            InC("x", InC("y", Call("Commute", L(V("x")), L(V("y"))))))));
}

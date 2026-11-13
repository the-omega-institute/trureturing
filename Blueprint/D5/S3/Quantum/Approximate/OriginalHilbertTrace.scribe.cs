using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Approximate;

internal sealed class OriginalHilbertTraceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An associative finite complex C-star algebra close to an original Hilbert product has a nearby faithful trace on the same vector space.",
        H("A nearby trace in the original Hilbert metric"), Blocks(
            Describe.Lean(DescribeId.Create("nearby-faithful-trace"),
                DeclarationHandle.Create("D5/S3/Quantum/Approximate/OriginalHilbertTrace.nearby_faithful_trace"),
                H("One trace and its positive Hermitian form"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("A is a nontrivial finite-dimensional unital complex C-star algebra with its supplied associative product, involution and C-star norm. B is an arbitrary positive definite Hermitian inner product on the same complex vector space. Write p(x)=sqrt(Re B(x,x)) for its original Hilbert norm. The C-star norm is used for the compact topology of the actual unitary group; p is used for every perturbation estimate. Neither norm is identified with the other.")),
                    Paragraph(Text("The original unit e is the element 1 of the supplied algebra, and B(1,1)=1. Its involution is isometric for p, hence an isometric antilinear involution for the original metric. The original product mu is complex bilinear, has right unit 1, and satisfies B(mu(x,y),z)=B(y,mu(star(x),z)) for all x,y,z. Thus the theorem also applies when mu has the two-sided unit and star compatibility of the original setup. Assume M>=1, 0<=q<1 and 0<=d<=1/8. For all x,y assume p(mu(x,y))<=M p(x)p(y) and p(xy-mu(x,y))<=q p(x)p(y). For every actual unitary u of the supplied associative algebra assume p(u)<=1+2d.")),
                    Paragraph(Text("There are one complex-linear functional t and one positive definite Hermitian form Bt on that same full vector space. They satisfy t(1)=1, t(xy)=t(yx), t(star(x))=conj(t(x)), and Bt(x,y)=t(star(x)y) for every x,y. In particular t is positive and faithful: t(star(x)x) is a nonnegative real number and is strictly positive for x nonzero. Bt(1,1)=1 and Bt(ax,y)=Bt(x,star(a)y) for every a,x,y. All of these conclusions use the same t and Bt.")),
                    Paragraph(Text("With tau(x)=B(1,x), the original dual estimate is abs(t(x)-tau(x))<=8 M q p(x) for every x. The same trace form satisfies abs(Bt(x,y)-B(x,y))<=17 M^2 q p(x)p(y) for all x,y. The pointwise dual inequality is precisely the operator norm bound on the original Hilbert dual; no C-star dual norm is substituted.")),
                    Paragraph(Text("The unit and adjoint identity give tau(mu(x,y))=B(star(x),y). Polarization of the original isometric antilinear involution makes this symmetric in x,y. Consequently abs(tau(xy-yx))<=2q p(x)p(y) and Re tau(star(x)x)>=(1-q)p(x)^2. In particular tau is a faithful positive unital functional on the supplied associative algebra.")),
                    Paragraph(Text("Define t(x) by integrating tau(star(u)xu) over normalized Haar measure on the actual compact unitary group. Left translation makes t invariant under unitary conjugation. For a unitary u, apply this invariance to ux to obtain t(ux)=t(xu). Every element is a complex linear combination of four actual unitaries by Mathlib's CStarAlgebra.exists_sum_four_unitary, so complex linearity gives the full trace identity. Pointwise positivity and positivity of Haar measure near the identity prove faithfulness.")),
                    Paragraph(Text("Associativity gives (xu)star(u)=x. Applying the commutator estimate to star(u) and xu bounds the integrand difference by 2q(M+q)(1+2d)^2 p(x), which is at most 8Mq p(x). Combining this with the bilinear product error gives q+8Mq(M+q)<=17M^2q for the form difference. This is a conditional trace and form construction. It does not construct the associative product, a unit-fixing metric transport, or a transported product on the original Hilbert metric, and asserts no physical realization."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula a=F.Id("A"), b=F.Id("B"), mu=F.Id("mu"), m=F.Id("M"), q=F.Id("q"), d=F.Id("d");
        Formula x=F.Id("x"), y=F.Id("y"), t=F.Id("t"), bt=F.Id("Bt");
        Formula p(Formula z) => Call("p",z);
        Formula tr(Formula z) => Call("t",z);
        Formula star(Formula z) => Call("star",z);
        Formula norm(Formula z) => new Formula.Norm(z);
        Formula le(Formula l,Formula r) => new Formula.Relation(l,FormulaRelationOperator.LessThanOrEqual,r);
        Formula and(Formula l,Formula r) => new Formula.Logic(l,FormulaLogicOperator.And,r);
        Formula all(string n,Formula typ,Formula body) => new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(n),typ,body);
        Formula ex(string n,Formula typ,Formula body) => new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create(n),typ,body);
        Formula one=F.D(1);
        Formula result=and(Eq(tr(one),one),and(
            all("x",a,all("y",a,Eq(tr(Multiply(x,y)),tr(Multiply(y,x))))),and(
            all("x",a,Eq(tr(star(x)),star(tr(x)))),and(
            all("x",a,le(norm(Subtract(tr(x),Call("B",one,x))),Multiply(Multiply(Multiply(F.D(8),m),q),p(x)))),and(
            all("x",a,all("y",a,Eq(Call("Bt",x,y),tr(Multiply(star(x),y))))),and(
            Eq(Call("Bt",one,one),one),and(
            all("x",a,all("y",a,le(norm(Subtract(Call("Bt",x,y),Call("B",x,y))),
                Multiply(Multiply(Multiply(Multiply(F.D(17),Power(m,F.D(2))),q),p(x)),p(y))))),
            all("a",a,all("x",a,all("y",a,Eq(Call("Bt",Multiply(F.Id("a"),x),y),Call("Bt",x,Multiply(star(F.Id("a")),y)))))))))))));
        Formula hypotheses=Call("OriginalHilbertProductBounds",a,b,mu,m,q,d);
        Formula conclusion=ex("t",Call("ComplexLinearFunctional",a),ex("Bt",Call("PositiveHermitianCore",a),result));
        Formula statement=new Formula.Logic(hypotheses,FormulaLogicOperator.Implies,conclusion);
        statement=all("d",Call("Real"),statement);
        statement=all("q",Call("Real"),statement);
        statement=all("M",Call("Real"),statement);
        statement=all("mu",Call("ComplexBilinearProduct",a),statement);
        statement=all("B",Call("PositiveHermitianCore",a),statement);
        return all("A",Call("FiniteDimensionalNontrivialComplexCStarAlgebra"),statement);
    }
}

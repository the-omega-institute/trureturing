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
                H("One trace, its positive form and its original Riesz operator"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("A is a nontrivial finite-dimensional unital complex C-star algebra with its supplied associative product, involution and C-star norm. B is an arbitrary positive definite Hermitian inner product on the same complex vector space. Write p(x)=sqrt(Re B(x,x)) for its original Hilbert norm. The C-star norm is used for the compact topology of the actual unitary group; p is used for every perturbation estimate. Neither norm is identified with the other.")),
                    Paragraph(Text("The original unit e is the element 1 of the supplied algebra, and B(1,1)=1. Its involution is isometric for p, hence an isometric antilinear involution for the original metric. The original product mu is complex bilinear, has right unit 1, and satisfies B(mu(x,y),z)=B(y,mu(star(x),z)) for all x,y,z. Thus the theorem also applies when mu has the two-sided unit and star compatibility of the original setup. Assume M>=1, 0<=q<1 and 0<=d<=1/8. For all x,y assume p(mu(x,y))<=M p(x)p(y) and p(xy-mu(x,y))<=q p(x)p(y). For every actual unitary u of the supplied associative algebra assume p(u)<=1+2d.")),
                    Paragraph(Text("There are one complex-linear functional t and one positive definite Hermitian form Bt on that same full vector space. They satisfy t(1)=1, t(xy)=t(yx), t(star(x))=conj(t(x)), and Bt(x,y)=t(star(x)y) for every x,y. In particular t is positive and faithful: t(star(x)x) is a nonnegative real number and is strictly positive for x nonzero. Bt(1,1)=1 and Bt(ax,y)=Bt(x,star(a)y) for every a,x,y. All of these conclusions use the same t and Bt.")),
                    Paragraph(Text("With tau(x)=B(1,x), the original dual estimate is abs(t(x)-tau(x))<=8 M q p(x) for every x. The same trace form satisfies abs(Bt(x,y)-B(x,y))<=17 M^2 q p(x)p(y) for all x,y. The pointwise dual inequality is precisely the operator norm bound on the original Hilbert dual; no C-star dual norm is substituted.")),
                    Paragraph(Text("The same witnesses also supply an invertible complex-linear Riesz operator G on the original vector space, with B(x,Gy)=Bt(x,y), B(Gx,y)=B(x,Gy), and Re B(x,Gx)>0 for every nonzero x. It commutes with the original antilinear involution: G(star(x))=star(Gx). Its quantitative bound is p(Gx-x)<=17M^2q p(x) for every x, equivalently the original Hilbert operator bound ||G-I||<=17M^2q. This G is the positive Gram operator of the trace form, not the required unit-fixing metric transport.")),
                    Paragraph(Text("The unit and adjoint identity give tau(mu(x,y))=B(star(x),y). Polarization of the original isometric antilinear involution makes this symmetric in x,y. Consequently abs(tau(xy-yx))<=2q p(x)p(y) and Re tau(star(x)x)>=(1-q)p(x)^2. In particular tau is a faithful positive unital functional on the supplied associative algebra.")),
                    Paragraph(Text("Define t(x) by integrating tau(star(u)xu) over normalized Haar measure on the actual compact unitary group. Left translation makes t invariant under unitary conjugation. For a unitary u, apply this invariance to ux to obtain t(ux)=t(xu). Every element is a complex linear combination of four actual unitaries by Mathlib's CStarAlgebra.exists_sum_four_unitary, so complex linearity gives the full trace identity. Pointwise positivity and positivity of Haar measure near the identity prove faithfulness.")),
                    Paragraph(Text("Associativity gives (xu)star(u)=x. Applying the commutator estimate to star(u) and xu bounds the integrand difference by 2q(M+q)(1+2d)^2 p(x), which is at most 8Mq p(x). Combining this with the bilinear product error gives q+8Mq(M+q)<=17M^2q for the form difference. This is a conditional trace and form construction. It does not construct the associative product, a unit-fixing metric transport, or a transported product on the original Hilbert metric, and asserts no physical realization.")),
                    Paragraph(Text("Riesz representation is taken using B and its induced original Hilbert norm. The positive definiteness of Bt makes its Riesz map injective, and finite dimension makes it invertible. Evaluating the form error against Gx-x bounds its squared norm and yields the operator estimate. Traciality gives Bt(star(x),star(y))=Bt(y,x). Combining this identity with polarization of the original antilinear isometry and nondegeneracy of B proves conjugation commutation without treating star as complex linear.")),
                    Paragraph(Text("The remaining restoration claim requires one invertible complex-linear T with T1=1, T(star(x))=star(Tx), Bt(Tx,Ty)=B(x,y), ||T-I||<=3r0, ||T^-1-I||<=2r0 and ||T||,||T^-1||<=2, where r0=17M^2q<=1/16. This theorem does not supply T. Consequently it does not establish the simultaneous original-metric product conclusion for hatnu(x,y)=T^-1((Tx)(Ty)), including its adjoint compatibility and the error q+34Mr0<=579M^3q.")),
                    Paragraph(Text("For the source pipeline, keep a>=1, 0<epsilonStar<=1, M>=1 and 0<=delta<=min(epsilonStar/M,1/A), with A=10000aM^6, epsilon=M delta, d=aM delta, q=16aM^3delta and r0=17M^2q. These substitutions give d<=1/(10000M^5)<=1/8, q<=16/(10000M^3)<1, r0<=272/(10000M)<1/16 and epsilon<=epsilonStar<=1. Conditional on constructing the same T and proving the transported-product bound, its error is at most 579M^3q=9264aM^6delta<=A delta. The external approximate-algebra construction that supplies nu is not proved here; these substitutions do not supply that input algebra, even at zero defect, and assert no physical realization."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula a=F.Id("A"), b=F.Id("B"), mu=F.Id("mu"), m=F.Id("M"), q=F.Id("q"), d=F.Id("d");
        Formula x=F.Id("x"), y=F.Id("y"), t=F.Id("t"), bt=F.Id("Bt"), g=F.Id("G");
        Formula p(Formula z) => Call("p",z);
        Formula tr(Formula z) => Call("t",z);
        Formula star(Formula z) => Call("star",z);
        Formula norm(Formula z) => new Formula.Norm(z);
        Formula eq(Formula l,Formula r) => new Formula.Relation(l,FormulaRelationOperator.Equal,r);
        Formula le(Formula l,Formula r) => new Formula.Relation(l,FormulaRelationOperator.LessThanOrEqual,r);
        Formula and(Formula l,Formula r) => new Formula.Logic(l,FormulaLogicOperator.And,r);
        Formula all(string n,Formula typ,Formula body) => new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(n),typ,body);
        Formula ex(string n,Formula typ,Formula body) => new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create(n),typ,body);
        Formula one=new Formula.Number(1);
        Formula result=and(eq(tr(one),one),and(
            all("x",a,all("y",a,eq(tr(Multiply(x,y)),tr(Multiply(y,x))))),and(
            all("x",a,eq(tr(star(x)),star(tr(x)))),and(
            all("x",a,le(norm(Subtract(tr(x),Call("B",one,x))),Multiply(Multiply(Multiply(new Formula.Number(8),m),q),p(x)))),and(
            all("x",a,all("y",a,eq(Call("Bt",x,y),tr(Multiply(star(x),y))))),and(
            eq(Call("Bt",one,one),one),and(
            all("x",a,all("y",a,le(norm(Subtract(Call("Bt",x,y),Call("B",x,y))),
                Multiply(Multiply(Multiply(Multiply(new Formula.Number(17),Multiply(m,m)),q),p(x)),p(y))))),
            all("a",a,all("x",a,all("y",a,eq(Call("Bt",Multiply(F.Id("a"),x),y),Call("Bt",x,Multiply(star(F.Id("a")),y)))))))))))));
        Formula gx=Call("G",x), gy=Call("G",y);
        Formula gram=and(
            all("x",a,all("y",a,eq(Call("B",x,gy),Call("Bt",x,y)))),and(
            all("x",a,all("y",a,eq(Call("B",gx,y),Call("B",x,gy)))),and(
            all("x",a,new Formula.Logic(Call("Nonzero",x),FormulaLogicOperator.Implies,
                new Formula.Relation(new Formula.Number(0),FormulaRelationOperator.LessThan,Call("Re",Call("B",x,gx))))),and(
            all("x",a,eq(Call("G",star(x)),star(gx))),
            all("x",a,le(p(Subtract(gx,x)),Multiply(Multiply(Multiply(new Formula.Number(17),Multiply(m,m)),q),p(x))))))));
        result=and(result,ex("G",Call("ComplexLinearAutomorphism",a),gram));
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

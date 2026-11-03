using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.PrimitiveLifts;

internal sealed class RationalReturnAtlasCriterionDocument : IScribeDocumentDefinition
{
    private static Formula I(string n) => F.Id(n);
    private static Formula.BoundVariable B(string n, Formula t) => new(FormulaIdentifier.Create(n), t);
    private static Formula Q(Formula f, params Formula.BoundVariable[] v) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. v], f);
    private static Formula Ex(Formula f, params Formula.BoundVariable[] v) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. v], f);
    private static Formula And(Formula a, Formula b) => Seq(Open,a,Sp,Land,Sp,b,Close);
    private static Formula App(Formula f, Formula x) => Call("apply",f,x);
    private static Formula RationalGroup => Call("Multiplicative",I("Rational"));
    private static Formula OneTime => Call("ofAdd",D(1));
    private static Formula Criterion => Seq(Open,Open,
        Ex(And(Seq(Open,Q(Call("Equivariant",I("A"),App(I("rho"),I("q"))),B("q",RationalGroup)),Close),
            Equal(Call("underlyingFunction",App(I("rho"),OneTime)),Call("time",I("A")))),
            B("rho",Call("MonoidHom",RationalGroup,Call("Perm",I("X"))))),Close,
        Sp,F.Iff,Sp,
        And(Equal(Call("period",I("A")),D(1)),
            Ex(Equal(App(I("phi"),OneTime),Call("holonomy",I("A"))),
                B("phi",Call("MonoidHom",RationalGroup,I("H"))))),Close);
    private static Formula Statement => Q(
        Q(Seq(OpenBracket,Call("Group",I("H")),CloseBracket,
            Q(Criterion,B("X",Call("Type",I("v"))),B("A",Call("ReturnAtlas",I("H"),I("X"))))),
            B("H",Call("Type",I("u")))),
        B("u",I("Universe")),B("v",I("Universe")));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One complete return chart supports rational time precisely when its phase period is one and its holonomy extends to a rational group homomorphism.",
        H("Rational time on a single complete return chart"),Blocks(
        Describe.Lean(DescribeId.Create("rational-return-atlas-criterion"),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PrimitiveLifts/RationalReturnAtlasCriterion.rational_time_action_criterion"),
            H("Exact criterion for a coherent rational action"),
            StatementSource.FromAuthor(Disp(Statement)),
            AssessedProvenance.FromRepo(),Blocks(
                Paragraph(Text("The universes u and v are independent. H is any group, X is any carrier, and A is a complete signed ReturnAtlas H X. A has a positive natural period d, holonomy h in H, and coordinates point(t,z). Its complete equality relation is point(t,z)=point(s,w) exactly when t=s+d*m and z*h^m=w for some integer m. Its time map advances t by one, while deck(a) multiplies z on the left. These are the entire hypotheses; H may be infinite, noncommutative or have torsion.")),
                Paragraph(Text("Multiplicative Rational is the additive group of all rational numbers written multiplicatively. Its identity is ofAdd(0); ofAdd(1) is the positive unit time. A monoid homomorphism rho into Perm X is one coherent action, with rho(ofAdd(q+r))=rho(ofAdd(q))*rho(ofAdd(r)) and rho(ofAdd(0)) the identity permutation. Equivariant A (rho(q)) means that rho(q)(deck(a,x))=deck(a,rho(q)(x)) for every a in H and x in X. The displayed equality at unit time is equality of the underlying functions on all X. Neither continuity nor an order or topology is assumed.")),
                Paragraph(Text("For necessity, put R=rho(ofAdd(1/d)). The homomorphism law gives R^d=rho(ofAdd(1)), hence the dth iterate of R is A.time. Apply the existing ReturnAtlas.root_criterion at k=d. Its signed equation is d*s.val=1+d*m, so d divides 1 and d=1. This uses the existing signed root classification rather than a separate classification of roots.")),
                Paragraph(Text("When d=1, the existing complete atlas coordinates give the equivalence e:H equiv X defined by e(z)=point(0,z). The left deck law becomes e(a*z)=deck(a,e(z)); the signed return relation gives time(e(z))=e(z*h). Every deck-equivariant permutation rho(q) therefore has the form rho(q)(e(z))=e(z*b(q)), where b(q)=e inverse(rho(q)(e(1))). With permutation multiplication interpreted as composition, right translations satisfy R(b)*R(c)=R(c*b). Consequently the immediate composition rule is b(p*q)=b(q)*b(p). Commutativity of the rational source also gives b(p*q)=b(p)*b(q), producing the required genuine homomorphism phi into H. Unit time forces phi(ofAdd(1))=h.")),
                Paragraph(Text("Conversely, a homomorphism phi with this unit value defines rho(q) by transporting z maps to z*phi(q) through e. The images of phi commute because the rational source is commutative, so these right translations satisfy the permutation homomorphism law in its actual composition order. Associativity makes them commute with every left deck translation, and the value at ofAdd(1) is exactly time. The construction includes zero and negative rational times and uses neither finite nor countable carriers nor a divisibility hypothesis on H.")),
                Paragraph(Text("This is a repository derivation from the complete return chart and its existing root criterion. The result concerns a single specified chart and its specified deck action. It makes no literature priority claim."))),DescribeRole.Theorem))));
}

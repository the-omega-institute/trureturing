using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers;

internal sealed class LegalChainMomentCoordinatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integral incidence inversion and polar forms on actual legal-chain states.",
        H("Legal chain integral and polar coordinates"), Blocks(
            Paragraph(Text("Notation: Nat, Int and Real denote the natural numbers, integers and real numbers. All named operators below use the corresponding Lean definitions in LegalChainMomentCoordinates, LegalChainMomentQuotient, LegalChainMomentTopology and LegalChainMomentGeometry. Application is written with parentheses; x.1 and x.2 are product projections and p.val is the underlying subtype value. Every displayed sum is over the indicated finite type. toReal is the integer-to-real inclusion, and toAngle is the ordinary projection Real to Real/(2 pi Int). A binder g in AddCommGroup(G) supplies the additive commutative group structure used in all subsequent expressions on G.")),
            Paragraph(Text("Pattern(n) is exactly the finite subsets I of Fin n with no i,j in I whose natural values satisfy i.val+1=j.val. Low(n,q) and High(n,q) are the subtypes with |I|<=q and q<|I|. V(n)=Pattern(n) to Real. incidence(n)(T,I)=1 when T is contained in I and is zero otherwise; signedIncidence(n)(I,T)=(-1)^(|T|-|I|) when I is contained in T and is zero otherwise. Matrix 1 is the identity. moments(p)(T)=sum over I containing T of p(I); probabilities(mu)(I)=sum over T containing I of (-1)^(|T|-|I|) mu(T); phases(theta)(T)=sum over I contained in T of (-1)^(|T|-|I|) theta(I); originalPhases(Phi)(I)=sum over T contained in I of Phi(T). Integer coefficients act by integer multiples in G.")),
            Paragraph(Text("PositiveProbability(n) consists of p in V(n) with every p(I)>0 and sum p(I)=1. ProbabilityFibre(q,p0) consists of all such p with moments(p)(T)=moments(p0)(T) for every T in Low(n,q). fillMoments(q,p0,x) fills the low slots from moments(p0) and the high slots from x. positiveDomain(q,p0)={x:High(n,q) to Real | every probabilities(fillMoments(q,p0,x))(I)>0}; using a set as a type means its subtype. Nonempty, IsOpen and Convex(Real,...) refer to this actual subset of the full high real function space.")),
            Paragraph(Text("occupationAction(n,q,G,t)(I) is the sum of t(T) over low T contained in I. actionHom(n,q,G,t)=originalPhases(lowEmbedding(t)), where lowEmbedding extends t by zero. PhaseOrbit(n,q,G,theta,eta) means there exists t with eta=theta+occupationAction(n,q,G,t). highPhases(q,theta)(T)=phases(theta)(T.val), with the source's implicit q shown explicitly. Representative(q,p0)=ProbabilityFibre(q,p0) times all Pattern(n) phase circles. reductionSetoid keeps the probability equal and relates phases by PhaseOrbit. quotientCover(q,p0)(x,theta) is the inverse actual reductionHomeomorph applied to (x,angleCover(n,q)(theta)); angleCover projects each high real phase to its circle of period 2 pi.")),
            Paragraph(Text("polarMap(n,x)(I)=sqrt(x.1(I)) exp(-i x.2(I)); polarTorusMap(n,p,theta)(I)=sqrt(p(I)) times the unit-circle image of -theta(I). polarDerivative(n,x)(d)(I)=exp(-i x.2(I)) times (d.1(I)/(2 sqrt(x.1(I)))-i sqrt(x.1(I)) d.2(I)). amplitudeOneForm(n,x,d) is minus the imaginary part of sum conjugate(polarMap(n,x)(I)) polarDerivative(n,x)(d)(I). sourceTwoForm(n,d,e)=sum over I of d.2(I)e.1(I)-e.2(I)d.1(I). Writing psi(I)=polarMap(n,x)(I) and D(d)(I)=polarDerivative(n,x)(d)(I), projectiveTwoForm(n,x,d,e)=2 Im(sum conjugate(D(d)(I)) D(e)(I) - conjugate(sum conjugate(psi(I)) D(d)(I)) times (sum conjugate(psi(I)) D(e)(I))). Every sum here is over Pattern(n). HasFDerivAt asserts the actual real Frechet derivative, and IsLocalHomeomorph asserts local homeomorphism for the ordinary period projection.")),
            Describe.Lean(DescribeId.Create("legal-chain-coordinate-laws"),
                DeclarationHandle.Create("D5/S3/Quantum/Fibers/LegalChainMomentCoordinates.legal_chain_coordinate_laws"),
                H("Integral and polar coordinate laws"),
                StatementSource.FromAuthor(CoordinateFormula()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every finite path and every natural order q, the actual legal patterns are its independent subsets. Their downward closure identifies each inclusion interval with the powerset of the difference. Powerset signed cancellation proves both integral incidence inverse identities.")),
                    Paragraph(Text("The signed upper moment inverse and unsigned lower phase inverse act by integer multiples on every additive commutative group, including the actual circle of period 2 pi. The literal occupation generators are exactly the inverse images of the low phase slots. Their orbits are classified by all high phases, with no residual finite ambiguity.")),
                    Paragraph(Text("For every positive normalized reference law, the actual inverse-moment positivity inequalities define a nonempty open convex high-moment domain. The orbit quotient has its quotient topology and is homeomorphic to this domain times the ordinary high torus. Real lifts have exactly the independent 2 pi integer periods.")),
                    Paragraph(Text("The amplitude on the actual phase circles has real-lift expression sqrt(p) exp(-i theta). Its Frechet derivative follows from the square-root and exponential rules. Minus the imaginary amplitude pairing gives sum p dtheta, equal to sum mu dPhi by integral duality. The source two-form becomes sum dPhi wedge dmu. On normalized probability tangents the rank-one projective correction has zero imaginary part, giving the specified projective form with the source sign.")),
                    Paragraph(Text("These coordinate laws are used by the smooth fixed-moment reduction. All positivity assumptions, exact period relations and actual polar derivatives are retained."))),
                DescribeRole.Theorem))));

    private static Formula CoordinateFormula()
    {
        Formula n = V("n"), q = V("q"), p0 = V("p0"), x = V("x"), y = V("y");
        Formula d = V("d"), e = V("e"), theta = V("theta"), eta = V("eta"), g = V("G");
        Formula pattern = C("Pattern", n), low = C("Low", n, q), high = C("High", n, q);
        Formula vector = C("V", n), pair = Product(vector, vector), domain = C("positiveDomain", q, p0);
        Formula positive = All("I", pattern, Less(D(0), A(Field(x, 1), V("I"))));
        Formula c01 = Equal(Mul(C("signedIncidence", n), C("incidence", n)), D(1));
        Formula c02 = Equal(Mul(C("incidence", n), C("signedIncidence", n)), D(1));
        Formula c03 = All("G", C("Type"), All("g", C("AddCommGroup", g),
            All("t", Arrow(low, g), Equal(C("occupationAction", n, q, g, V("t")), C("actionHom", n, q, g, V("t"))))));
        Formula c04 = All("G", C("Type"), All("g", C("AddCommGroup", g),
            All("theta", Arrow(pattern, g), All("eta", Arrow(pattern, g),
                IffTo(C("PhaseOrbit", n, q, g, theta, eta),
                    Equal(C("highPhases", q, theta), C("highPhases", q, eta)))))));
        Formula c05 = All("p0", C("PositiveProbability", n),
            And(C("Nonempty", domain), And(C("IsOpen", domain), C("Convex", C("Real"), domain))));
        Formula c06 = All("p0", C("PositiveProbability", n),
            All("x", Product(domain, Arrow(high, C("Real"))),
                All("y", Product(domain, Arrow(high, C("Real"))), Periods(n, q, p0, x, y))));
        Formula c07 = All("x", pair, All("d", pair, ImpliesTo(positive,
            Equal(C("amplitudeOneForm", n, x, d), SumOver("T", pattern,
                Mul(C("moments", Field(x, 1), V("T")), C("phases", Field(d, 2), V("T"))))))));
        Formula c08 = All("d", pair, All("e", pair, Equal(C("sourceTwoForm", n, d, e),
            SumOver("T", pattern, Sub(
                Mul(C("phases", Field(d, 2), V("T")), C("moments", Field(e, 1), V("T"))),
                Mul(C("phases", Field(e, 2), V("T")), C("moments", Field(d, 1), V("T"))))))));
        Formula c09 = All("x", pair, All("d", pair, All("e", pair, ImpliesTo(positive,
            ImpliesTo(Equal(SumOver("I", pattern, A(Field(d, 1), V("I"))), D(0)),
                ImpliesTo(Equal(SumOver("I", pattern, A(Field(e, 1), V("I"))), D(0)),
                    Equal(C("projectiveTwoForm", n, x, d, e), C("sourceTwoForm", n, d, e))))))));
        Formula c10 = All("x", pair, ImpliesTo(positive,
            C("HasFDerivAt", C("polarMap", n), C("polarDerivative", n, x), x)));
        Formula c11 = All("p", vector, All("theta", vector,
            Equal(C("polarMap", n, Pair(V("p"), theta)),
                C("polarTorusMap", n, V("p"), Lam("I", pattern, C("toAngle", A(theta, V("I"))))))));
        Formula c12 = C("IsLocalHomeomorph", C("angleCover", n, q));
        return Disp(All("n", C("Nat"), All("q", C("Nat"),
            Conj(c01, c02, c03, c04, c05, c06, c07, c08, c09, c10, c11, c12))));
    }

    private static Formula C(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);

    private static Formula A(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);
    private static Formula V(string name) => F.Id(name);
    private static Formula Field(Formula value, int index) => Seq(value, Dot, new Formula.Number(index));
    private static Formula Pair(Formula x, Formula y) => Seq(Open, x, Comma, y, Close);
    private static Formula Product(Formula x, Formula y) => Seq(Open, x, Close, Times, Open, y, Close);
    private static Formula Arrow(Formula x, Formula y) => new Formula.TypeArrow(x, y);
    private static Formula Equal(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Less(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula ImpliesTo(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula IffTo(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Iff, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Lam(string name, Formula type, Formula body) =>
        Seq(Open, LambdaLower, Sp, V(name), Colon, type, Comma, body, Close);
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(V(name), InMacro, type), Grp(body));

    private static Formula Conj(params Formula[] clauses)
    {
        Formula[] rows = new Formula[clauses.Length];
        for (int i = 0; i < clauses.Length; i++)
            rows[i] = i == 0 ? Seq(Open, clauses[i], Close)
                : Seq(Land, Open, clauses[i], Close);
        return Seq(Left, Open, new Formula.Aligned([.. rows]), Right, Close);
    }

    private static Formula Periods(Formula n, Formula q, Formula p0, Formula x, Formula y) =>
        IffTo(Equal(C("quotientCover", q, p0, x), C("quotientCover", q, p0, y)),
            And(Equal(Field(x, 1), Field(y, 1)),
                Some("k", Arrow(C("High", n, q), C("Int")),
                    All("T", C("High", n, q),
                        Equal(Sub(A(Field(x, 2), V("T")), A(Field(y, 2), V("T"))),
                            Mul(Mul(D(2), Pi), C("toReal", A(V("k"), V("T")))))))));
}

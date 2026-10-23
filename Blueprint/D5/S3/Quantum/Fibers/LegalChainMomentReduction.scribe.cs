using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers;

internal sealed class LegalChainMomentReductionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer moment coordinates and the full positive symplectic quotient of a legal path.",
        H("Legal chain moment and phase reduction"), Blocks(
            Paragraph(Text("Notation: Nat, Int, Real and Complex have their usual meanings; natural subtraction is truncated and natural division is floored. Proof(P) is the type of proofs of P; the binder hn therefore witnesses 1<=n. Every operator spelled as a Lean identifier below denotes its actual definition in the owning LegalChainMoment modules, with parentheses for application. x.1/x.2 are product projections and x.val unwraps a subtype; a set used as a type is its subtype. All sums display their exact finite index type. Pattern(n) is the actual no-adjacent-position subset type, Low(n,q) has |T|<=q, High(n,q) has q<|T|, V(n)=Pattern(n) to Real, H(n,q)=High(n,q) to Real and E(n,q)=H(n,q) times H(n,q). Layer(n,k) is the subtype of Pattern(n) with |I|=k. Ioc(a,b)={k in Nat | a<k and k<=b}; choose(a,k) is the binomial coefficient. card is Fintype.card, finrank is Module.finrank, and fib is Nat.fib. Thus finrank(Real,...) is real vector-space dimension.")),
            Paragraph(Text("PositiveProbability(n)={p:V(n) | every p(I)>0 and sum p(I)=1}. ProbabilityFibre(q,p0) is its entire subspace with all low moments equal to those of p0. moments, probabilities, phases and originalPhases are respectively the unsigned upper, signed upper, signed lower and unsigned lower inclusion sums on actual legal subsets; incidence and signedIncidence are their integer matrices. fillMoments(q,p0,x) fixes the low moment slots from p0 and inserts x in the high slots. positiveDomain(q,p0)={x:H(n,q) | every probabilities(fillMoments(q,p0,x))(I)>0}. probabilityFibreEquiv(q,p0)(p) is the subtype-valued high moment tuple of p. highPhases(q,theta)(T)=phases(theta)(T.val), with its implicit q displayed explicitly.")),
            Paragraph(Text("The phase circle is AddCircle(2 pi)=Real/(2 pi Int); toAngle is its ordinary real projection and toReal is the integer inclusion. Representative(q,p0)=ProbabilityFibre(q,p0) times (Pattern(n) to AddCircle(2 pi)). reductionSetoid identifies (p,theta) and (p',eta) exactly when p=p' and eta(I)=theta(I)+sum over low T contained in I of t(T), for some low phase tuple t. Thus the empty T is common phase. Quotient(reductionSetoid(q,p0)) carries this actual quotient topology; quotientMk(reductionSetoid(q,p0),a) is its class. Homeomorph(X,Y) is the type X equiv-topological Y, so the displayed existential supplies an actual map h as well as its inverse and continuity.")),
            Paragraph(Text("reductionHomeomorph(q,p0) is the constructed quotient homeomorphism. angleCover(n,q) projects each real high phase modulo 2 pi, and quotientCover(q,p0)(x,theta)=reductionHomeomorph(q,p0).symm(x,angleCover(n,q)(theta)). originalPhaseProjection(q,p0,x,theta) is the class of (probabilityFibreEquiv(q,p0).symm(x),toAngle composed with theta). J(n,q) denotes exactly the product model I(Real,H(n,q)).prod I(Real,H(n,q)); Ireal is I(Real,Real). ModelProd(H,H) is the chart coordinate model type H times H. The source's proved ordinary-period atlas and transported quotient charts are used by IsManifold, chartAt, TangentSpace and ContMDiff; no chart or rank is a premise.")),
            Paragraph(Text("fixedTangent(n,q)={d:V(n) times V(n) | every low moments(d.1)(T)=0}; its subtype coercion is d.val. verticalTangent consists exactly of zero probability velocity and a low occupation phase velocity. tangentCoordinates(n,q,d) is (high moments of d.val.1, high phases of d.val.2). highPhaseLinear(n,q) is the real linear highPhases map. representativeLift(q,p0)(u)=(probabilities(fillMoments(q,p0,u.1)),originalPhases(highEmbedding(u.2))), where highEmbedding extends by zero. liftLinear(n,q)(d)=(probabilities(highEmbedding(d.1)),originalPhases(highEmbedding(d.2))); it is the actual affine lift's linear part. toContinuousLinearMap forgets a finite-dimensional real linear map to its continuous linear map; fst, snd, comp and prod are precisely LinearMap.fst, LinearMap.snd, composition and paired product with their displayed scalar/domain arguments. continuousIdentity(Real,E) is ContinuousLinearMap.id Real E.")),
            Paragraph(Text("polarMap(n,(p,theta))(I)=sqrt(p(I)) exp(-i theta(I)); polarTorusMap uses sqrt(p(I)) times the unit-circle image of -theta(I). polarDerivative(n,(p,theta))(d)(I)=exp(-i theta(I))(d.1(I)/(2 sqrt(p(I)))-i sqrt(p(I)) d.2(I)). amplitudeOneForm is minus the imaginary amplitude/derivative Hermitian pairing; sourceTwoForm(n,d,e)=sum over I of d.2(I)e.1(I)-e.2(I)d.1(I). Writing psi(I)=polarMap(n,x)(I) and D(d)(I)=polarDerivative(n,x)(d)(I), projectiveTwoForm(n,x,d,e)=2 Im(sum conjugate(D(d)(I)) D(e)(I) - conjugate(sum conjugate(psi(I)) D(d)(I)) times (sum conjugate(psi(I)) D(e)(I))). These sums are over Pattern(n). normSq is Complex.normSq. reducedForm(n,q,d,e)=sum over T in High(n,q) of d.2(T)e.1(T)-e.2(T)d.1(T). quotientTwoForm(q,p0,z) is the source bilinear pullback via liftLinear, on the actual tangent model E(n,q). liftedSourceTwoForm(q,p0)(u) is the literal continuous alternating source form pulled back by fderiv Real (representativeLift(q,p0)) u. extDeriv is its exterior derivative. liftedChart(q,p0,z)(u)=(u.1,chartAt(H(n,q),reductionHomeomorph(q,p0)(z).2)(angleCover(n,q)(u.2))); source denotes a chart's actual source set. Lambda notation denotes the displayed typed function, and HasFDerivAt is its real Frechet derivative.")),
            Describe.Lean(DescribeId.Create("complete-legal-chain-coordinates"),
                DeclarationHandle.Create("D5/S3/Quantum/Fibers/LegalChainMomentReduction.complete_legal_chain_coordinates"),
                H("Complete coordinates on every positive fixed-moment fibre"),
                StatementSource.FromAuthor(CompleteFormula()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Gamma n is the set of actual subsets of Fin n with no consecutive occupied positions. Position i in Fin n denotes position i+1 in the one-based path. The empty subset is retained. Every subset of a legal pattern is legal.")),
                    Paragraph(Text("Z(T,I) is one when T is contained in I and zero otherwise. S(I,T) is zero unless I is contained in T; in that case it is minus one to the power |T|-|I|. For I contained in J, intermediate legal patterns correspond exactly to subsets of J minus I, by deleting I and by adjoining I. The signed interval sum therefore vanishes unless I=J.")),
                    Paragraph(Text("The two integer matrix products are identities. Integer matrices act by finite integer multiples on every additive commutative group. Thus the same inverse laws hold on the integral lattice, on real probabilities, and on the phase circle R/(2 pi Z). No division of a phase or choice of a smaller lattice occurs.")),
                    Paragraph(Text("The moment transform is mu(T)=sum over I containing T of p(I). Its inverse is the signed upper sum with coefficient (-1)^(|T|-|I|). The phase transform is the signed lower sum; its inverse is theta(I)=sum over T contained in I of Phi(T). momentEquiv and phaseEquiv carry both inverse laws, and the real versions are linear equivalences.")),
                    Paragraph(Text("The amplitude is first defined on the actual phase circles R/(2 pi Z), using their ordinary unit-circle map. Its expression on every real lift is exactly sqrt(p) exp(-i theta). Thus the amplitude expression is compatible with the specified periods, without any phase division.")),
                    Paragraph(Text("The amplitude is literally sqrt(p(I)) exp(-i theta(I)). At every strictly positive p, the square-root, complex-exponential and product rules yield its Frechet derivative. Probability and phase variations are independent real directions before restriction to the normalized moment fibre.")),
                    Paragraph(Text("The canonical one-form is minus the imaginary part of the Hermitian pairing of the actual amplitude and its derivative. Direct calculation gives sum p(I) dtheta(I). Substituting the unsigned lower phase inverse and interchanging the finite sums gives sum mu(T) dPhi(T), including the empty pattern.")),
                    Paragraph(Text("The projective expression is twice the imaginary part of the Hermitian derivative pairing after subtracting the rank-one amplitude correction. For normalized probability tangents, the sum of each probability velocity is zero. Their amplitude pairings are then purely imaginary, so the correction has real product and zero imaginary part.")),
                    Paragraph(Text("The resulting form is sum dtheta(I) wedge dp(I), with the prescribed sign. Integer duality transforms it into sum dPhi(T) wedge dmu(T). The empty-moment term vanishes on normalized tangents, and the fixed low-moment terms vanish upon restriction to their level set.")),
                    Paragraph(Text("Low n q consists of legal patterns of cardinality at most q, including the empty pattern. Its occupation generator at T adds t(T) to theta(I) exactly when T is contained in I. The empty generator is the common phase. Summing these literal generators equals inverse phase transformation of the low slots extended by zero.")),
                    Paragraph(Text("Two original phase tuples are in the same supplied occupation-action orbit if and only if all their transformed high phases agree. This holds in every additive commutative group, in particular the actual circle with period 2 pi. The inverse chooses zero low phase slots and reconstructs the original phases. It proves the quotient is precisely the high torus without an additional finite ambiguity.")),
                    Paragraph(Text("p0 is an arbitrary strictly positive probability with total mass one. ProbabilityFibre fixes every low moment to the value at p0. Any prescribed nonempty low-moment fibre containing a positive probability is of this form: choose that probability as p0. The empty moment is one throughout by normalization, so including it adds no extra constraint.")),
                    Paragraph(Text("Fill the low moment slots with their fixed values and the high slots with x. The actual signed inverse gives all probabilities. positiveDomain requires each such probability to be strictly positive. The empty moment forces the reconstructed total mass to be one. Inversion gives an equivalence between this domain and the whole positive fixed fibre.")),
                    Paragraph(Text("Finite strict affine inequalities make the high domain open and convex. It is nonempty because p0 supplies a point. No equality among high moments is imposed, and the ambient high-coordinate space is the full real function space. The construction is uniform for q=0 and for an empty set of high patterns.")),
                    Paragraph(Text("The inverse real lift fills the fixed low moments, applies the actual signed probability inverse, fills zero low relation phases and applies the actual unsigned phase inverse. Its affine linear part is computed directly and is its Frechet derivative.")),
                    Paragraph(Text("fixedTangent consists of the actual probability-phase velocities whose low moment derivatives vanish. verticalTangent consists of zero probability velocity and the low occupation-phase velocities. The high moment and high relation-phase derivatives give a surjective linear map, with exactly this vertical kernel. The quotient of these tangent spaces is the full high-pair vector space.")),
                    Paragraph(Text("The pullback of the prescribed source form is the sum, over actual high legal patterns, of dPhi(T) wedge dmu(T). Testing against individual probability and phase directions proves nondegeneracy, also when the high index type is empty.")),
                    Paragraph(Text("The descended two-form is the bilinear pullback of the original source form by the actual derivative of the inverse coordinates. The same form is obtained from every fixed-fibre representative and the projective Hermitian expression. Its coefficients are smooth. As a continuous alternating form on the real covering coordinates, its literal pullback has zero exterior derivative because the differentiated inverse is constant. The local period charts have translation transitions and identity differential, so these local expressions agree.")),
                    Paragraph(Text("Characteristic Boolean words identify actual legal path subsets with the existing admissible-word carrier and preserve occupation cardinality. The existing support-size theorem gives choose(n-k+1,k) for each legal layer in range. The same characteristic-word equivalence directly transports the existing total count F(n+2), without a new counting proof. The existing sharp occupation bound gives maximum size floor((n+1)/2), equal to ceil(n/2). Thus the number of actual high patterns is the sum of those binomial coefficients for q<k<=ceil(n/2).")),
                    Paragraph(Text("The derived tangent quotient has two real coordinates for each actual high pattern. For every n>=1 and every q from zero through the maximum size, its real dimension is twice that sum. At q=0 only normalization and common phase are removed. At the maximum size there are no high patterns and the positive quotient is a point. These uniform constructions include n=1 and every compatible positive fixed fibre.")),
                    Paragraph(Text("These are dimensions of the specified probability-phase state relation space. They supply neither a physical space dimension nor an independently callable experimental control menu.")),
                    Paragraph(Text("The atlas is formed from genuine local inverses of the surjective ordinary period projection from the real high-phase space to its circle product. On an overlap two continuous lifts have the same projection. Their difference has zero projection. Local injectivity of the period map forces that difference to be locally constant.")),
                    Paragraph(Text("Every overlap is therefore locally a translation and is smooth of all orders. The same argument proves that the period projection, followed by any such chart, is locally a translation and has identity derivative. The smooth structure and tangent correspondence are consequences of the actual lattice projection, rather than rank or chart assumptions.")),
                    Paragraph(Text("The positive probability domain is an open subset of the full high-moment vector space. Combine its ordinary chart with the proved phase-lift atlas, then use the actual quotient homeomorphism to obtain charts on the orbit quotient. Chart overlaps remain the same smooth transitions. This constructs the quotient manifold for every positive reference, including zero-dimensional fibres.")),
                    Paragraph(Text("The chart coordinates are the actual high moments and local real lifts of the actual high relation phases. Probability and phase carry the usual subspace and quotient topologies throughout.")),
                    Paragraph(Text("The representative space is the actual positive fixed-moment fibre times all original phase circles. Its equivalence relation keeps probability fixed and identifies the literal low occupation rotations. The quotient carries its quotient topology.")),
                    Paragraph(Text("The probability coordinate equivalence and its inverse are continuous affine maps on subspaces. Integer phase sums are continuous on the circle. The quotient coordinate map and its inverse are consequently continuous and are a homeomorphism onto the positive high-moment domain times the high phase torus.")),
                    Paragraph(Text("Real lifts reconstruct quotient states by the proved inverse coordinates. Two such lifts yield the same quotient point exactly when their probability coordinates agree and each phase difference is 2 pi times an integer. The integers are independent for the actual high patterns. Local real lifts exist by finite products of the ordinary circle period projection."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("legal-chain-source-form-pullback"),
                DeclarationHandle.Create("D5/S3/Quantum/Fibers/LegalChainMomentReduction.reduced_form_pullback"),
                H("The actual source form pulls back to the high symplectic pairs"),
                StatementSource.FromAuthor(PullbackFormula()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For every length n, order q and pair of real high-coordinate velocities d and e, "
                    + "the actual differentiated inverse coordinates pull the source form back to "
                    + "the sum of dPhi(T) wedge dmu(T) over the actual high legal patterns."))),
                DescribeRole.Theorem))));

    private static Formula CompleteFormula()
    {
        Formula n = V("n"), q = V("q"), p0 = V("p0"), theta = V("theta");
        Formula x = V("x"), y = V("y"), d = V("d"), e = V("e"), z = V("z"), u = V("u"), p = V("p");
        Formula pattern = C("Pattern", n), high = C("High", n, q), low = C("Low", n, q);
        Formula vector = C("V", n), hspace = C("H", n, q), espace = C("E", n, q);
        Formula domain = C("positiveDomain", q, p0), fibre = C("ProbabilityFibre", q, p0);
        Formula relation = C("reductionSetoid", q, p0), quotient = C("Quotient", relation);
        Formula torus = Arrow(high, C("AddCircle", Mul(D(2), Pi)));
        Formula tangent = C("fixedTangent", n, q), model = C("J", n, q);
        Formula probability = Val(Val(p)), point = Pair(probability, theta);
        Formula upper = new Formula.Floor(new Formula.Fraction(Add(n, D(1)), D(2)));
        Formula c01 = All("a", C("Representative", q, p0),
            Equal(A(V("h"), C("quotientMk", relation, V("a"))),
                Pair(C("probabilityFibreEquiv", q, p0, Field(V("a"), 1)), C("highPhases", q, Field(V("a"), 2)))));
        Formula c02 = Equal(Mul(C("signedIncidence", n), C("incidence", n)), D(1));
        Formula c03 = Equal(Mul(C("incidence", n), C("signedIncidence", n)), D(1));
        Formula c04 = All("theta", Arrow(pattern, C("AddCircle", Mul(D(2), Pi))),
            And(Equal(C("originalPhases", C("phases", theta)), theta),
                Equal(C("phases", C("originalPhases", theta)), theta)));
        Formula c05 = C("Nonempty", domain);
        Formula c06 = C("IsOpen", domain);
        Formula c07 = C("Convex", C("Real"), domain);
        Formula c08 = C("IsManifold", model, Infty, quotient);
        Formula c09 = All("x", Product(domain, hspace), All("y", Product(domain, hspace), Periods(n, q, p0, x, y)));
        Formula c10 = All("p", fibre, All("theta", vector, All("d", Product(vector, vector),
            Equal(C("amplitudeOneForm", n, point, d), SumOver("T", pattern,
                Mul(C("moments", probability, V("T")), C("phases", Field(d, 2), V("T"))))))));
        Formula c11 = All("p", fibre, All("theta", vector, All("d", tangent, All("e", tangent,
            Equal(C("projectiveTwoForm", n, point, Val(d), Val(e)),
                C("reducedForm", n, q, C("tangentCoordinates", n, q, d), C("tangentCoordinates", n, q, e)))))));
        Formula c12 = All("d", tangent, IffTo(
            All("e", tangent, Equal(C("sourceTwoForm", n, Val(d), Val(e)), D(0))),
            Member(d, C("verticalTangent", n, q))));
        Formula c13 = All("d", espace,
            ImpliesTo(All("e", espace, Equal(C("reducedForm", n, q, d, e), D(0))), Equal(d, D(0))));
        Formula projection = C("originalPhaseProjection", q, p0, x, theta);
        Formula projectionLinear = C("toContinuousLinearMap", C("prod",
            C("fst", C("Real"), hspace, vector),
            C("comp", C("highPhaseLinear", n, q), C("snd", C("Real"), hspace, vector))));
        Formula c14 = All("x", domain, All("theta", vector,
            Some("f", Arrow(Product(hspace, vector), espace), And(
                All("y", domain, All("eta", vector,
                    Equal(C("chartAt", C("ModelProd", hspace, hspace), projection,
                        C("originalPhaseProjection", q, p0, y, V("eta"))),
                        A(V("f"), Pair(Val(y), V("eta")))))),
                C("HasFDerivAt", V("f"), projectionLinear, Pair(Val(x), theta))))));
        Formula c15 = All("z", espace, C("HasFDerivAt", C("representativeLift", q, p0),
            C("toContinuousLinearMap", C("liftLinear", n, q)), z));
        Formula c16 = All("d", espace, All("e", espace, PullbackEquality(n, q, d, e)));
        Formula c17 = All("k", C("Nat"), ImpliesTo(AtMost(V("k"), upper),
            Equal(C("card", C("Layer", n, V("k"))), C("choose", Add(Sub(n, V("k")), D(1)), V("k")))));
        Formula c18 = All("p", fibre, All("theta", vector,
            Equal(SumOver("I", pattern, C("normSq", C("polarMap", n, point, V("I")))), D(1))));
        Formula c19 = All("z", quotient, And(
            All("d", espace, Equal(C("quotientTwoForm", q, p0, z, d, d), D(0))), And(
                All("d", espace, ImpliesTo(All("e", espace,
                    Equal(C("quotientTwoForm", q, p0, z, d, e), D(0))), Equal(d, D(0)))),
                All("p", fibre, All("theta", vector, All("d", tangent, All("e", tangent,
                    Equal(C("quotientTwoForm", q, p0, z, C("tangentCoordinates", n, q, d), C("tangentCoordinates", n, q, e)),
                        C("projectiveTwoForm", n, point, Val(d), Val(e))))))))));
        Formula c20 = All("d", espace, All("e", espace,
            C("ContMDiff", model, C("Ireal"), Infty,
                Lam("z", quotient, C("quotientTwoForm", q, p0, z, d, e)))));
        Formula chartSource = Seq(C("chartAt", hspace, Field(C("reductionHomeomorph", q, p0, z), 2)), Dot, C("source"));
        Formula c21 = All("z", quotient, All("u", Product(domain, hspace),
            ImpliesTo(Member(C("angleCover", n, q, Field(u, 2)), chartSource),
                C("HasFDerivAt", C("liftedChart", q, p0, z),
                    C("continuousIdentity", C("Real"), espace), Pair(Val(Field(u, 1)), Field(u, 2))))));
        Formula c22 = All("p", fibre, All("theta", vector, And(
            Equal(C("polarMap", n, point), C("polarTorusMap", n, probability,
                Lam("I", pattern, C("toAngle", A(theta, V("I")))))),
            C("HasFDerivAt", C("polarMap", n), C("polarDerivative", n, point), point))));
        Formula c23 = All("u", espace, All("v", Arrow(C("Fin", D(2)), espace),
            Equal(C("liftedSourceTwoForm", q, p0, u, V("v")),
                C("reducedForm", n, q, A(V("v"), D(0)), A(V("v"), D(1))))));
        Formula c24 = All("u", espace, Equal(C("extDeriv", C("liftedSourceTwoForm", q, p0), u), D(0)));
        Formula c25 = Equal(C("card", pattern), C("fib", Add(n, D(2))));
        Formula c26 = All("b", Arrow(low, C("Real")), ImpliesTo(
            All("T", low, Equal(C("moments", Val(p0), Val(V("T"))), A(V("b"), V("T")))),
            Equal(FibreSet(n, q, All("T", low,
                Equal(C("moments", Val(p), Val(V("T"))), A(V("b"), V("T"))))),
                FibreSet(n, q, All("T", low,
                    Equal(C("moments", Val(p), Val(V("T"))), C("moments", Val(p0), Val(V("T")))))))));
        Formula c27 = All("z", quotient,
            Equal(C("finrank", C("Real"), C("TangentSpace", model, z)),
                Mul(D(2), SumOver("k", C("Ioc", q, upper), C("choose", Add(Sub(n, V("k")), D(1)), V("k"))))));
        return Disp(All("n", C("Nat"), All("hn", C("Proof", AtMost(D(1), n)), All("q", C("Nat"),
            All("p0", C("PositiveProbability", n),
                Some("h", C("Homeomorph", quotient, Product(domain, torus)),
                    Conj(c01, c02, c03, c04, c05, c06, c07, c08, c09, c10, c11, c12, c13, c14,
                        c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27)))))));
    }

    private static Formula FibreSet(Formula n, Formula q, Formula condition) =>
        Seq(OpenBrace, V("p"), Colon, C("PositiveProbability", n), Mid, condition, CloseBrace);

    private static Formula PullbackEquality(Formula n, Formula q, Formula d, Formula e) =>
        Equal(C("sourceTwoForm", n, C("liftLinear", n, q, d), C("liftLinear", n, q, e)),
            C("reducedForm", n, q, d, e));

    private static Formula PullbackFormula()
    {
        Formula n = V("n"), q = V("q"), d = V("d"), e = V("e");
        return Disp(All("n", C("Nat"), All("q", C("Nat"), All("d", C("E", n, q),
            All("e", C("E", n, q), PullbackEquality(n, q, d, e))))));
    }

    private static Formula C(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);

    private static Formula A(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);
    private static Formula V(string name) => F.Id(name);
    private static Formula Field(Formula value, int index) => Seq(value, Dot, new Formula.Number(index));
    private static Formula Val(Formula value) => Seq(value, Dot, C("val"));
    private static Formula Pair(Formula x, Formula y) => Seq(Open, x, Comma, y, Close);
    private static Formula Product(Formula x, Formula y) => Seq(Open, x, Close, Times, Open, y, Close);
    private static Formula Arrow(Formula x, Formula y) => new Formula.TypeArrow(x, y);
    private static Formula Equal(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula AtMost(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Member(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.MemberOf, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula ImpliesTo(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula IffTo(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Iff, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
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

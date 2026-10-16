using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class ResetIntegralGluingDocument : IScribeDocumentDefinition
{
    private static Formula I(string s) => F.Id(s);
    private static Formula.BoundVariable B(string s, Formula t) => new(FormulaIdentifier.Create(s), t);
    private static Formula All(Formula f, params Formula.BoundVariable[] v) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. v], f);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Conj(params Formula[] c)
    {
        Formula f = c[^1];
        for (int j = c.Length - 2; j >= 0; --j) f = And(c[j], f);
        return f;
    }
    private static Formula Q(string s) => Call(s, I("q"));
    private static Formula Scope(Formula f) => All(new Formula.Logic(Call("positive", I("q")),
        FormulaLogicOperator.Implies, f), B("q", I("Nat")));
    private static Formula P(string s, Formula p) => Call(s, I("q"), p);
    private static Formula Pair(Formula a, Formula b) => Call("pair", a, b);
    private static Formula Value(Formula a) => Call("value", a);
    private static Formula Diff => Call("sub", P("a0", Call("fst", Value(I("z")))),
        P("b0", Call("snd", Value(I("z")))));
    private static DocumentBlock Entry(string n, string h, Formula f, string prose) => Describe.Lean(
        DescribeId.Create(n.Replace('_','-')), DeclarationHandle.Create(
            "D5/S3/ConceptDynamics/Coding/ResetIntegralGluing." + n),
        H(h), StatementSource.FromAuthor(Disp(f)), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integral sign components are glued by their literal common residue, with a canonical inverse.",
        H("Integral sign gluing and coefficient halves"),
        Blocks(
            Paragraph(Text("For q natural put S(q)=sum over k<q of X^k, f(q)=X^q-S(q), "
                + "g(q)=X^q+S(q), F(q)=f(q)g(q), and W(q)=S(q)-(X-1)X^q. "
                + "Plus(q) and Minus(q) are the literal integer polynomial quotients by f and g. "
                + "reduce maps each integer coefficient to ZMod 2 and fixes X. Common(q) is "
                + "(ZMod 2)[X]/reduce(g(q)); g(q)=S(q+1). The ring maps rplus and rminus descend "
                + "this same coefficient reduction. Compatible(q) is their RingHom.pullback subring "
                + "of Plus(q) times Minus(q). fp is the original ResetSignIntegerCyclic quotient map.")),
            Entry("sign_ideals", "The actual sum and intersection ideals",
                All(And(
                    Equal(Call("sup", Call("span", Q("f")), Call("span", Q("g"))),
                        Call("spanPair", Num(2), Q("g"))),
                    Equal(Call("inf", Call("span", Q("f")), Call("span", Q("g"))),
                        Call("span", Q("F")))), B("q", I("Nat"))),
                "span is the principal ideal in Int[X], spanPair generates an ideal with two elements, "
                + "and sup and inf are the ideal sum and intersection. The geometric identity supplied "
                + "by ResetSignIntegerCyclic gives X*f+(2-X)*g=2. Since f=g-2*S, the sum is (2,g). "
                + "For a common multiple f*a=g*b the same certificate makes 2*b a multiple of f. "
                + "Take its monic f remainder. Remainders commute with integer scalar multiplication, "
                + "and each integer coefficient is free of two-torsion. Thus f divides b and F divides "
                + "the common multiple. Integral comaximality is neither assumed nor used."),
            Entry("compatible_even", "Compatibility detects every even remainder coefficient",
                All(Call("divides", Num(2), Call("coeff", Diff, I("i"))),
                    B("q", I("Nat")), B("z", Q("Compatible")), B("i", I("Nat"))),
                "a0 and b0 are AdjoinRoot.modByMonicHom for the monic degree-q polynomials f and g. "
                + "They are canonical representatives, including zero. Mapping these remainders to "
                + "characteristic two agrees with the common monic remainder. The compatibility "
                + "equation therefore makes reduce(a0-b0)=0, so every integer coefficient is even. "
                + "No nonnegative-coefficient assumption is present."),
            Entry("integral_gluing", "The literal equivalence and both inverse identities",
                Scope(Conj(
                    All(Equal(P("fromCompatible", P("toCompatible", I("v"))), I("v")), B("v", Q("QF"))),
                    All(Equal(P("toCompatible", P("fromCompatible", I("z"))), I("z")), B("z", Q("Compatible"))),
                    All(Equal(Value(P("gluing", P("fp", I("p")))),
                        Pair(Call("mk", Q("f"), I("p")), Call("mk", Q("g"), I("p")))),
                        B("p", I("IntPolynomial"))),
                    All(Equal(Call("inverseApply", Q("gluing"), I("z")),
                        P("fp", Call("sub", P("a0", Call("fst", Value(I("z")))),
                            Call("mul", Call("mul", I("X"), Q("f")), Call("half", Diff))))),
                        B("z", Q("Compatible"))),
                    All(And(Call("degreeLess", P("a0", Call("fst", Value(I("z")))), I("q")),
                        Call("degreeLess", P("b0", Call("snd", Value(I("z")))), I("q"))),
                        B("z", Q("Compatible"))),
                    All(Equal(Call("half", Diff), Call("coefficientHalfRangeSum", I("q"), Diff)),
                        B("z", Q("Compatible"))))
                    ),
                "positive(q) means 0<q. degreeLess is polynomial degree strictly below q, including zero. "
                 + "coefficientHalfRangeSum(q,p) is sum over i<q of monomial i (p.coeff(i)/2). "
                + "mk denotes the indicated polynomial quotient map; value forgets "
                + "pullback membership. half divides every coefficient by 2 using integer Euclidean "
                + "division, so negative coefficients are included. Since a0-b0=2*half(a0-b0), "
                + "the polynomial p=a0-X*f*half(a0-b0) projects to a0 modulo f and to b0 modulo g: "
                + "p-b0=(2-X)*g*half(a0-b0). This proves the pullback-side inverse identity. "
                + "The intersection ideal identity reflects equality from both components back to "
                + "QF, proving the other inverse identity. gluing has toCompatible as its forward "
                + "ring homomorphism and this exact fromCompatible as its inverse. All positive q, "
                + "including q=1, are retained; no entropy assertion occurs."),
            Entry("gluing_generators", "Forward time, original sign, scalars and the common quotient",
                All(Conj(
                    Equal(Value(P("gluing", P("fp", I("X")))),
                        Pair(Call("root", Q("f")), Call("root", Q("g")))),
                    Equal(Value(P("gluing", P("fp", Q("W")))), Pair(Num(1), Call("neg", Num(1)))),
                    All(Equal(Value(P("gluing", P("fp", Call("C", I("z"))))),
                        Pair(Call("integerCastPlus", I("z")), Call("integerCastMinus", I("z")))),
                        B("z", I("Int"))),
                    All(Equal(P("commonQuotientEquiv", Call("mkSumIdeal", I("p"))),
                        P("commonPolynomial", I("p"))), B("p", I("IntPolynomial"))),
                    Equal(Call("reduce", Q("g")), Call("geometricSum", Call("succ", I("q"))))),
                    B("q", I("Nat"))),
                "commonQuotientEquiv identifies Int[X] modulo the actual sum ideal with Common(q). "
                + "Its map is literally coefficient reduction followed by the common quotient, fixing X. "
                + "Its kernel proof uses monic division by g and evenness of the remainder; coefficient "
                + "lifts give surjectivity. The identities W=1-X*f and W=-1+(2-X)*g give the two sign "
                + "images. Each integer maps to the same integer in both components. "
                + "At q=1 this is the congruence pullback of two copies of Int over the two-element field."),
            Paragraph(Text("For every natural q, the following application uses only local mathematical notation. "
                + "For every q>0, every a in Plus(q) and every b in Minus(q), "
                + "rplus(q,a)=0 iff there exists u in Plus(q) with a=2*u, and "
                + "rminus(q,b)=0 iff there exists v in Minus(q) with b=2*v. "
                + "Reuse ResetIntegralGluing.reduce_a0 and reduce_b0, half_cancel and common_kernel "
                + "(private suppliers in this owner), with AdjoinRoot.mk_leftInverse. For example, "
                + "rplus(q,a)=0 gives reduce(a0(q,a))=0, so a0(q,a)=2*half(a0(q,a)); "
                + "one may take u=AdjoinRoot.mk(f(q))(half(a0(q,a))). The Minus formula uses b0 and g. "
                + "Conversely common_kernel puts 2 in ker(commonPolynomial(q)), so 2=0 in Common(q) "
                + "and every even component has zero residue. This uses no field or squarefree hypothesis.")),
            Paragraph(Text("For every natural q and every integer epsilon, write V(q,epsilon) for the "
                + "additive subgroup of Compatible(q) defined, for every z in Compatible(q), by "
                + "z in V(q,epsilon) iff gluing(q,fp(q,W(q)))*z=epsilon*z, where epsilon*z is integer "
                + "scalar multiplication. This is local notation for an eigenspace of the literal original W; "
                + "ResetIntegralGluing.gluing_generators gives its product coordinates exactly (1,-1).")),
            Paragraph(Text("For every q>0 and every z in Compatible(q), z in V(q,1) iff there exists "
                + "a in Plus(q) with z.val=(2*a,0), and z in V(q,-1) iff there exists b in Minus(q) "
                + "with z.val=(0,2*b). In the first equation (1,-1)*z=z forces twice the Minus "
                + "coordinate to vanish. Apply AdjoinRoot.modByMonicHom to that equation, use the owner's "
                + "private two_torsion and g_monic, then AdjoinRoot.mk_leftInverse, to make that coordinate zero. "
                + "Compatibility and the component-kernel derivation above make the remaining coordinate even. "
                + "Interchange f_monic and g_monic for the negative eigenspace. Conversely either even axis "
                + "is compatible and satisfies its stated W equation.")),
            Paragraph(Text("For every q>0 put L(q)=V(q,1) sup V(q,-1) and D(q)=Plus(q) times Minus(q). "
                + "For every z in Compatible(q), z in L(q) iff there exist a in Plus(q) and b in Minus(q) "
                + "with z.val=(2*a,2*b). Thus the image of L(q) in D(q) is exactly 2*D(q). "
                + "The halves a and b range independently over the FULL product: they need not be compatible. "
                + "Apply Mathlib's AddSubgroup.mem_sup to split z into its two even axes; conversely "
                + "(2*a,0) and (0,2*b) are compatible and add to the displayed pair. "
                + "This identifies twice the full product, with no restriction to compatible halves.")),
            Paragraph(Text("For every q>0 and every d in D(q), the conductor condition is exactly "
                + "(for every t in D(q), d*t belongs to the subring Compatible(q)) iff "
                + "there exists e in D(q) with d=2*e. The conductor in this specified product overring "
                + "is therefore 2*D(q), with arbitrary potentially incompatible halves e=(a,b). "
                + "Use RingHom.pullback's defining residue equality and test t=(1,0) and t=(0,1). "
                + "Both component residues must vanish, so the component-kernel derivation gives d=(2*a,2*b). "
                + "Conversely (2*a,2*b)*(t1,t2) has both residues zero for every t. "
                + "No normalization or general unit classification enters this argument.")),
            Paragraph(Text("For every natural q, write kappa(q):Compatible(q) -> Common(q) for the "
                + "ring homomorphism (rplus q).comp ((rplus q).pullbackFst (rminus q)). "
                + "For every z in Compatible(q), kappa(q,z)=rplus(q,z.val.1)=rminus(q,z.val.2); "
                + "the second equality is precisely pullback membership. This notation uses the existing "
                + "rplus and rminus with Mathlib's RingHom.pullbackFst.")),
            Paragraph(Text("For every natural q and every c in Common(q), there exists z in Compatible(q) "
                + "with kappa(q,z)=c. The owner's private common_surjective supplies p in Int[X] with "
                + "commonPolynomial(q,p)=c; take z=gluing(q,fp(q,p)). The defining projection equations "
                + "give kappa(q,z)=commonPolynomial(q,p). This is residue surjectivity only, "
                + "with no lifting assertion for a native centralizer or the original rho image.")),
            Paragraph(Text("For every q>0, ker(kappa(q).toAddMonoidHom)=L(q). Indeed for every "
                + "z in Compatible(q), kappa(q,z)=0 iff both component residues vanish, iff "
                + "there exist independent a in Plus(q), b in Minus(q) with z.val=(2*a,2*b), "
                + "iff z belongs to L(q). The first equivalence uses compatibility, the second uses "
                + "the component-kernel derivation, and the last uses the AddSubgroup.mem_sup derivation above.")),
            Paragraph(Text("For every q>0 there is an additive equivalence "
                + "eta(q):Compatible(q)/L(q) ~=+ Common(q) with eta(q,[z])=kappa(q,z) "
                + "for every z in Compatible(q). Apply Mathlib's QuotientAddGroup.quotientAddEquivOfEq "
                + "to the kernel equality, then QuotientAddGroup.quotientKerEquivOfSurjective to "
                + "kappa(q).toAddMonoidHom and the coefficient-lift surjectivity above. "
                + "This is the actual additive subgroup quotient. Compatible(q) contains one as a subring "
                + "of D(q); no ring quotient of D(q) by Compatible(q) is being formed.")),
            Paragraph(Text("For every q>0, Nat.card(Common(q))=2^q and "
                + "Nat.card(Compatible(q)/L(q))=2^q. The owner's private degree_S and g_monic, "
                + "Polynomial.degree_add_eq_left_of_degree_lt and Polynomial.Monic.natDegree_map "
                + "give natDegree(reduce(g(q)))=q; private common_monic supplies monicity. "
                + "AdjoinRoot.powerBasis' followed by Basis.equivFun identifies the additive carrier "
                + "with Fin(q) -> ZMod(2). Apply Nat.card_congr, Nat.card_fun, Nat.card_zmod and "
                + "Nat.card_fin, then transport through eta(q). These formulas include odd q, "
                + "repeated factors and nonreduced Common(q); they use no semisimplicity or separability.")),
            Paragraph(Text("For every natural q, write tau(q) for the unit of Common(q) whose value is "
                + "AdjoinRoot.root(reduce(g(q)))=[X] and whose inverse value is [X]^q. "
                + "ResetIntegralGluing.gluing_generators identifies reduce(g(q)) with sum over k<q+1 "
                + "of X^k. Mathlib's geom_sum_mul gives reduce(g(q))*(X-1)=X^(q+1)-1. "
                + "AdjoinRoot.mk_eq_zero and AdjoinRoot.mk_X therefore give [X]^(q+1)=1, "
                + "and Units.mkOfMulEqOne constructs tau(q) with exactly that inverse. "
                + "This specifies forward time without classifying all residue units.")),
            Paragraph(Text("The exact order formula is orderOf(tau(1))=1 and, for every natural q "
                + "with 2<=q, orderOf(tau(q))=q+1. At q=1, reduce(g(1))=X-1, so [X]=1. "
                + "For q>=2, a smaller positive period m with 0<m<q+1 would, by AdjoinRoot.mk_eq_zero, "
                + "make reduce(g(q)) divide X^m-1. Polynomial.monic_X_pow_sub_C and "
                + "Polynomial.natDegree_X_pow_sub_C make the latter monic of degree m. "
                + "Polynomial.natDegree_le_of_dvd forces q<=m, hence m=q. "
                + "Polynomial.eq_of_monic_of_dvd_of_natDegree_le then identifies the two degree-q monic "
                + "polynomials. Their X coefficients are respectively one and zero for q>=2, by "
                + "Polynomial.coeff_X_pow and Polynomial.coeff_one, a contradiction. "
                + "Apply orderOf_eq_iff with the period q+1 and these exclusions. "
                + "Every positive q, including q=1 and repeated-factor cases, stays in scope.")),
            Paragraph(Text("For q,n natural put m=q+1 and d=gcd(m,n). Common(q) is literally "
                + "(ZMod 2)[X]/span(reduce(g(q))), with forward time multiplication by its root [X]. "
                + "gluing_generators identifies the modulus with P_m=sum over j<m of X^j. "
                + "The periodic fixed subtype is {x in Common(q) : [X]^n*x=x}; its cardinality is "
                + "2^(d-1 + (if Even(m/d) then 1 else 0)). Both m and d are positive for every q,n.")),
            Paragraph(Text("Here is the full parameter substitution for the library derivation. For q>0, "
                + "FiniteCompanionCyclicModule.P(-1,q)=P_m, so cyclicEquiv(-1,q,hq), followed by "
                + "Module.AEval'.of inverse, gives the actual companion coordinates C:Common(q) -> (Fin q -> ZMod 2). "
                + "cyclic_presentation and polynomial evaluation give C([X]*x)=T(C(x)), where "
                + "T(v)=cons(-sum(v),init(v)). Extend v to B(v)=snoc(v,-sum(v)), a sum-zero function "
                + "on Fin(q+1)=ZMod(q+1). Restriction to the first q entries is B inverse: the "
                + "sum-zero equation uniquely determines the last entry. Fin.sum_univ_castSucc, "
                + "Fin.sum_univ_succ, Fin.cons_snoc_eq_snoc_cons and Fin.snoc_init_self give "
                + "B(T(v))(i+1)=B(v)(i). Thus E=B composed with C is an actual equivariant "
                + "bijection to augmentation, and E([X]^n*x)(i+n)=E(x)(i). This proves, in both "
                + "directions, the fixed-subtype bijection with the sum-zero functions v satisfying v(i+n)=v(i).")),
            Paragraph(Text("The orbits of addition by n on ZMod m are precisely the cosets of "
                + "H=zmultiples(n). Nat.card_zmultiples and ZMod.addOrderOf_coe give |H|=m/d. "
                + "AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup then gives |ZMod m/H|=d. "
                + "Function.Periodic.lift supplies the descent to these cosets. "
                + "AddMonoidHom.fiberEquivKerOfSurjective with QuotientAddGroup.ker_mk' "
                + "gives each fibre cardinality directly. Fintype.sum_fiberwise' therefore "
                + "writes the total coordinate sum of a coset-constant function as (m/d) times "
                + "the sum of its d independent values. Setoid.liftEquiv and "
                + "Setoid.quotientKerEquivOfSurjective supply the parameter bijection for the "
                + "surjective coset map; the sum-zero predicate is transported using that sum identity. "
                + "If m/d is even, ZMod.natCast_eq_zero_iff_even "
                + "makes the constraint automatic, giving 2^d. If it is odd, that scalar is nonzero "
                + "in ZMod 2 and the constraint is sum(c)=0. Summation onto ZMod 2 is surjective "
                + "by a single-coordinate vector; QuotientAddGroup.quotientKerEquivOfSurjective "
                + "and the subgroup cardinality formula give a kernel of size 2^(d-1). "
                + "Nat.card_fun supplies the unconstrained function cardinality. No cycle count, "
                + "surjectivity or equivariance is an extra assumption.")),
            Paragraph(Text("At q=0 the modulus is 1 and Common(0) is the one-element zero ring, so the "
                + "count is 1. At q=1, [X]=1, so the count is 2 for every n. At n=0 every element "
                + "is fixed and the count is 2^q; the formula retains each of these boundaries. "
                + "The proof uses the companion presentation and additive quotient/cardinality APIs, "
                + "so repeated factors and even m remain in scope. No semisimple splitting, root "
                + "normalization, nonzero-n condition, faithfulness or entropy premise is needed. "
                + "This is a repository application of the cited existing results; no literature novelty is claimed.")),
            Paragraph(Text("For every q>=2 let beta=dbonacciPerronRoot(q), with the literal "
                + "f(q)=X^q-sum(i<q)X^i. Evaluation p |-> p.eval2(Int.cast,beta) factors "
                + "through the actual Plus(q)=Int[X]/(f(q)), because f(q)(beta)=0. "
                + "The uniform DBonacci irreducibility theorem makes "
                + "AdjoinRoot(map(Int->Rat,f(q))) a field, so its lift to Real is injective. "
                + "The representative map from Plus(q) into that rational quotient sends p to "
                + "[map(p)]. Equality of two images means map(f(q)) divides map(p-s). "
                + "Monicity makes f(q) primitive; Gauss divisibility gives f(q)|(p-s), "
                + "hence equality already in Plus(q). The two evaluation lifts commute on "
                + "every integer polynomial by eval2_map. Thus E:Plus(q)->+*Real is injective "
                + "and E([p])=p(beta). This uses the existing polynomial and quotient, and "
                + "places no ring structure on the native dimension group.")),
            Paragraph(Text("The construction is a repository derivation from standard quotient, monic division "
                + "and pullback APIs in pinned Mathlib, together with ResetSignIntegerCyclic's literal "
                + "geometric certificate. It supplies the integral reconstruction used by ResetIntegralUnits "
                + "and the original native action in ResetNativeUnitNormalForm; no literature novelty is claimed. "
                + "The local eigenlattice sum and conductor, common-residue kernel and quotient, cardinality "
                + "and exact common-time order apply to the original Native groups as described in "
                + "ResetNativeUnitNormalForm. The derivations above apply the cited existing suppliers. "
                + "That application uses nativeGluing and its existing "
                + "all-centralizer scalarization; there is no reverse Native dependency in this arithmetic owner. "
                + "Compatible is a subring containing one; the sign quotient used here is additive.")))));
}

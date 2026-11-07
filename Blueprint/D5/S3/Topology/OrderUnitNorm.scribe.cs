using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class OrderUnitNormDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original Archimedean order-unit cone gives an exact norm and a quantitative preparation criterion for the same positive unital exponential group.",
        H("The original order-unit norm"),
        Blocks(
            Paragraph(Text("Let E be any finite-dimensional real normed vector space. Its auxiliary norm supplies the usual topology only. The data A consist of a convex cone C containing zero, a closedness proof, salience, and a specified vector u in its interior. Salience means that a vector and its negative can both belong to C only when the vector vanishes. No inner product, lattice, Jordan product, self-duality or nonzero-dimension assumption is used.")),
            Paragraph(Text("Put B equal to the vectors v for which u-v and u+v belong to C. For each v, let S(v) be the nonnegative real radii r for which r u-v and r u+v belong to C, and let n(v) be inf S(v). In particular, zero is retained among the radii. The order relation is exactly w-v in C.")),
            Describe.Lean(
                DescribeId.Create("constructed-order-norm-core"),
                DeclarationHandle.Create("D5/S3/Topology/OrderUnitNorm.norm_core"),
                H("The norm axioms follow from the original cone"),
                StatementSource.FromAuthor(F.Disp(CoreStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The symbols R and Types denote the real scalars and the type universe. ConeUnitData denotes precisely the original cone and unit data stated above. The displayed norm laws apply to the copy of E with norm n; this first assertion does not require finite dimension. They are proved rather than supplied as an extra hypothesis. The interior-unit assumption makes B a neighborhood of zero and hence absorbent. Each S(v) is nonempty, closed and bounded below by zero, so its infimum is attained.")),
                    Paragraph(Text("The symmetric interval is convex and balanced. Its gauge equals n exactly: every positive gauge radius is an order radius, and every radius just above the attained order radius is a positive gauge radius. This includes v=0, where S(0) contains its infimum zero although the gauge uses strictly positive radii. Mathlib's gaugeSeminorm supplies the seminorm laws. At n(v)=0 the attained inequalities put v and -v in C, so salience supplies definiteness.")))),
            Describe.Lean(
                DescribeId.Create("identity-dominated-scalar-rigidity"),
                DeclarationHandle.Create("D5/S3/Topology/OrderUnitNorm.identity_dominated_scalar"),
                H("Scalar rigidity on every original vector"),
                StatementSource.FromAuthor(F.Disp(RigidityStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Here E is any real normed vector space, including zero, infinite-dimensional and incomplete spaces. A is exactly the original ConeUnitData, P is an arbitrary real-linear endomorphism and c is any real number. For every original cone vector v, both P(v) and v-P(v) must belong to that same cone, and P(u)=c u. The conclusion holds for every original vector. The ambient norm need not equal the order-unit norm; no continuity of P, product, lattice or representation is assumed.")),
                    Paragraph(Text("If u=0, the attained order bounds and salience force every vector to vanish, so arbitrary c is retained. Otherwise positivity of P and I-P at u proves 0<=c<=1. A positive map sending u to a nonnegative multiple a u contracts the constructed order norm by a. Thus each actual binomial map choose(n,k) P^k (I-P)^(n-k) has the required global bound c^k(1-c)^(n-k) choose(n,k). Positivity of its factors is proved by induction on the powers.")),
                    Paragraph(Text("The pinned Mathlib declarations bernsteinPolynomial.sum and bernsteinPolynomial.sum_smul supply the operator partition and first moment by polynomial evaluation in the original endomorphism algebra. The triangle inequality, the scalar Bernstein probability and variance identities, and finite Cauchy-Schwarz bound the squared deviation by c(1-c) n(v)^2/n. An arbitrarily large natural n then forces n(P(v)-c v)=0. The scalar probability and variance results are reused, not reproved. This is a classical binomial rigidity argument; no literature originality is asserted.")),
                    Paragraph(Text("This is the general implication used at equations (2.15)-(2.16) of AURIC_ARBITRARY_DIMENSIONAL_SMALL_WINDOW_UNIT_BRIDGE. Its paper application substitutes E=X, the original completed cone and unit, P=A_h and c=exp(-h). It remains conditional on constructing that actual A_h and proving both full-cone positivities and its unit equation. This node does not establish those premises, B=0, K=0, the mirror and flow construction, general JB reconstruction, identification of the same original S, either source entrance, old D or physical consumers. The full Unit 2.2 through 6.1 goal remains open.")))),
            new DocumentBlock.Section(
                H("Positive functionals and the same original operator"),
                Blocks(
                    Paragraph(Text("These are applications of the constructed norm and existing operator theory. In Lean, Data.operatorBounds(H * H) is exactly the set of nonnegative c with n(H(H(v))) at most c n(v) for every v. ContinuousLinearMap.norm_def identifies its infimum with the norm of Data.operator(H * H); definitional conjugation identifies that operator with the square of Data.operator(H), and ContinuousLinearMap.isLeast_opNorm proves attainment and minimality. The transported positive functional is Data.functional(beta); its upper norm bound follows from Data.positive_bound and ContinuousLinearMap.opNorm_le_bound, and evaluation at the unit gives the reverse inequality via ContinuousLinearMap.le_opNorm_of_le. NormedSpace.map_exp applied to Data.bridge.conjContinuousAlgEquiv gives the exponential transport.")),
                    Paragraph(Text("PositiveDual denotes all original real-linear functionals nonnegative on C, and Effects denotes all x with x and u-x in C. RealEndomorphisms denotes all original real-linear maps E to E. The notation K abbreviates the norm of the square of the transported operator, and IsLeast includes membership and minimality in operatorBounds(H squared), the nonnegative global order-norm bound set. Here j is the canonical linear wrapping map to the copy E_u, and H_u is defined solely by H_u(j(v))=j(H(v)). The constructed copy is complete. The wrapping map and its inverse are continuous in the original finite-dimensional topology; no equality with the auxiliary ambient norm is asserted.")),
                    Paragraph(Text("For every positive original real-linear functional beta, its evaluation is bounded by its mass beta(u) times n(v). Applying beta to the attained endpoint inequalities proves this without dividing by its mass. Thus mass zero forces the original functional to vanish. The operator norm of beta transported to E_u is exactly beta(u), including in dimension zero.")),
                    Paragraph(Text("The square H_u squared acts on j(v) as j(H(H(v))). Its operator norm is exactly the infimum of all nonnegative c satisfying n(H(H(v))) at most c n(v) for every original v. This infimum is attained. Neither an ambient operator bound nor the square of the norm of H is substituted for this number.")),
                    Paragraph(Text("A positive unital linear map contracts n. A linear equivalence whose inverse is also positive is an isometry; positivity and unitality alone do not imply isometry. Applying this conclusion to exp(tH) uses both the assumed positivity at t and at -t. Independently, H(u)=0 makes the derivative of exp(tH)u vanish on the whole real line, so the actual exponential fixes u. Conjugation by j carries the actual exponential to exp(tH_u).")),
                    Paragraph(Text("Assume that every original exp(tH) is positive and fixes u. Its order norm is then preserved for every real t. If the separately supplied condition H(u)=0 also holds, an effect x in C with u-x in C has centered vector z=x-u/2 of order norm at most one half, and H(H(x))=H(H(z)). Positive-functional domination and the exact square-operator bound give the all-time centered-orbit estimate.")),
                    Paragraph(Text("The actual scalar orbit f(t)=beta(exp(tH)x) is twice continuously differentiable, with first derivative beta(exp(tH)Hx) and second derivative beta(exp(tH)H(Hx)). Taylor's theorem on the unoriented interval from 0 to any real s gives f(s) at most f(0)+s f'(0)+M s squared divided by two, where M=beta(u)K/2. Positivity makes this quadratic nonnegative on the entire real line. The existing quadratic discriminant theorem then gives f'(0) squared at most 2M f(0), including M=0. This proves the reverse certificate with exactly K=the operator norm of H_u squared, without division by mass or curvature. The positive-generator argument is supplied by the separate criterion below. The coefficient K is usable; no optimality claim is made.")),
                    Paragraph(Text("For an arbitrary original preparation set P contained in the full positive dual, assume its finite nonnegative cone has closure equal to that dual. Finite-dimensionality identifies every original linear functional with its unique continuous-linear version. The closure is the usual topology on the original dual, not a replacement preparation set. A certificate with one fixed nonnegative q on P extends with exactly the same q to the full dual. Mathlib's weighted finite Cauchy-Schwarz inequality applies directly to signed evaluations with nonnegative weights and masses, including the empty sum. For each fixed effect the squared inequality describes a closed set of functionals, so it persists under closure.")),
            Paragraph(Text("For r strictly positive and y and r u-y in C, apply the effect certificate to y/r and use the original linear maps. Multiplication by r squared leaves exactly q r beta(y) beta(u). There is no positive lower mass bound or division by mass. The attained order-radius bound supplies a finite strictly positive r for every positive y. Therefore beta(y)=0 forces beta(Hy)=0 for every positive original beta. The symbols Certificate, Cone and Closure mean precisely this effect certificate, finite nonnegative cone and ordinary dual-topology closure.")),
            Paragraph(Text("Order-unit norm and positive-functional mass facts are classical; the construction retains the original cone, unit, functional and linear action in one construction. It asserts no literature priority or physical realization of the mathematical exponential.")))),
            Describe.Lean(
                DescribeId.Create("original-cross-positive-generator"),
                DeclarationHandle.Create("D5/S3/Topology/OrderUnitNorm.cross_positive_flow"),
                H("Cross-positivity preserves the original cone"),
                StatementSource.FromAuthor(F.Disp(GeneratorStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Here L is any original real-linear endomorphism, C is the original closed salient convex cone containing zero, and u is its specified interior unit. The positive-dual quantifier includes every original algebraic linear functional nonnegative on C. Finite dimension supplies the unique continuous version of each such functional and completeness of the original space. No condition L(u)=0 is imposed. The exponential is precisely NormedSpace.exp of t times the continuous wrapping of that same L, in the original endomorphism algebra.")),
                    Paragraph(Text("Hahn-Banach separates a boundary point z of C from its interior. The resulting nonzero functional, with its sign reversed, is nonnegative on the original cone and vanishes at z: evaluation at zero and at twice z forces the contact value to be zero. Its unit mass is strictly positive, because the already proved zero-mass bound would otherwise make the functional zero. No normalized state, self-duality or smooth boundary is assumed.")),
                    Paragraph(Text("Choose a=n(Lu)+1 and d=a u-Lu. The attained order-radius inequality gives d-u in C. For y in C and epsilon strictly positive, perturb the actual orbit by w(t)=exp(tL)y+epsilon exp(a t)u. It starts in the interior and its actual derivative is Lw(t)+epsilon exp(a t)d. On a compact time interval, the closed set where w is not in the interior has a least element T if it is nonempty. Since w(0) is interior, T is strictly positive; every earlier nonnegative time is interior. Closedness of C puts w(T) in C, while the defining bad set keeps it outside the interior.")),
                    Paragraph(Text("At this original boundary contact take the supporting positive beta. For negative h tending to zero with -T<h<0, beta(w(T+h)) is nonnegative and beta(w(T))=0, so the left difference quotient is nonpositive. Existence of the actual derivative gives beta(w'(T)) at most zero. Cross-positivity at the proved cone point w(T), together with beta(d) at least beta(u)>0, makes that same derivative strictly positive. This contradiction keeps every perturbed orbit interior. At each fixed nonnegative time, letting epsilon tend to zero through positive values and using closedness gives the original unperturbed orbit in C. This proof needs neither a positive Euler step nor a time-monotone orbit, and includes dimension zero and boundary initial vectors.")),
                    Paragraph(Text("The classical implication is the cross-positive generator theorem of Schneider and Vidyasagar, Cross-Positive Matrices, SIAM Journal on Numerical Analysis 7(4), 508-519, Theorem 3. The original source also cites Niestegge, arXiv:1402.0158v2, Section 4, Lemma 3 for the two-sided zero-contact criterion. These mathematical sources motivate the route; the Lean proof uses the pinned Hahn-Banach, compact-minimum, exponential derivative and one-sided slope declarations directly. No literature originality is asserted.")))),
            Describe.Lean(
                DescribeId.Create("same-object-quantitative-generator-equivalence"),
                DeclarationHandle.Create("D5/S3/Topology/OrderUnitNorm.quantitative_generator_iff"),
                H("The same preparation coefficient and the same exponential"),
                StatementSource.FromAuthor(F.Disp(QuantitativeStatement(false))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Assume separately H(u)=0. The preparation set P is the original arbitrary subset of the full positive dual, and its finite nonnegative cone has the ordinary dual closure equal to that entire dual. Certificate(H,q,beta) means the squared effect inequality with coefficient q, every x and u-x in C, and the original evaluations beta(Hx), beta(x), beta(u). The first assertion is the full quantified equivalence between existence of one finite nonnegative preparation coefficient and positivity plus unit fixation of the same exp(tH) at every real time.")),
                    Paragraph(Text("The fixed-coefficient extension and exact radius factor are retained. Their full-dual zero-contact conclusion supplies cross-positivity for H and for -H separately. The generator theorem gives each nonnegative-time semigroup. A negative time for H is a nonnegative time for -H, in the same endomorphism algebra. Independently H(u)=0 fixes the original unit. The actual inverse exp(-tH) and the canonical norm transport are those already proved above; no new cone or generator is selected.")),
                    Paragraph(Text("Conversely Q=norm(H_u squared) is nonnegative and gives the certificate for every positive original functional. Applying this same bound to u-x and using H(u)=0 gives the complementary bound. Taking the lesser of the two proves the source's strengthening with Q min(beta(x),beta(u-x)) beta(u). Zero coefficient, zero mass and zero-dimensional fibers require no divisions. This theorem is a mathematical consequence for the original operator and preparations; it supplies no actual clock, reference or callable exponential.")))),
            Describe.Lean(
                DescribeId.Create("algebraic-archimedean-original-cone-criterion"),
                DeclarationHandle.Create("D5/S3/Topology/OrderUnitNorm.archimedean_quantitative_generator_iff"),
                H("The algebraic Archimedean hypotheses supply the topology bridge"),
                StatementSource.FromAuthor(F.Disp(QuantitativeStatement(true))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("ArchimedeanConeUnitData retains the original convex cone C containing zero, salience, positive unit u, and two algebraic assumptions. For each v some strictly positive real r has r u-v and r u+v in C. If v+epsilon u belongs to C for every epsilon>0, then v belongs to C. No closedness or interior-unit hypothesis is supplied in these data. An arbitrary auxiliary real norm realizes the usual finite-dimensional topology; the theorem derives the required topological facts for that topology and the same C and u.")),
                    Paragraph(Text("The order-unit bounds put every v in the linear span of C, so its affine span is the whole space. The pinned finite-dimensional convex-set theorem gives nonempty interior, including dimension zero. If v is an interior point and r u-v is in C for r>0, cone addition makes r u interior, and positive inverse scaling makes u interior. For v in the closure of C, adding epsilon u puts v+epsilon u in C: addition of an open interior set absorbs closure. The original Archimedean condition then puts v in C. Thus C is closed.")),
                    Paragraph(Text("The map toData preserves C and u literally and supplies only these proved topology properties. The operator H, preparation set P, all functionals, the ordinary dual closure, and the actual exponential remain the original ones. The norm, square-operator coefficient, same-K extension, exact scaling and complementary minimum are precisely those in the preceding quantified criterion. This is the source's complete mathematical Theorem 68.1. The correlated execution-map extension of Section 69.2 is a separate statement and is not a consequence claimed here.")))))));


    private static Formula CoreStatement()
    {
        var n = Id("n"); var v = Id("v"); var w = Id("w"); var a = Id("a");
        var laws = All("v", Id("E"), And(
            Le(F.D(0), Apply(n, v)),
            Iff(Eq(Apply(n, v), F.D(0)), Eq(v, F.D(0))),
            All("a", Id("R"), Eq(Apply(n, Scale(a, v)),
                Mul(Call("abs", a), Apply(n, v)))),
            All("w", Id("E"), Le(Apply(n, Add(v, w)),
                Add(Apply(n, v), Apply(n, w))))));
        return All("E", Id("Types"), Implies(Call("RealNormedVectorSpace", Id("E")),
            All("A", Call("ConeUnitData", Id("E")), laws)));
    }

    private static Formula RigidityStatement()
    {
        var E=Id("E"); var A=Id("A"); var P=Id("P"); var c=Id("c"); var v=Id("v");
        var C=Call("cone",A); var u=Call("unit",A);
        var positive=All("v",C,And(Call("mem",Apply(P,v),C),
            Call("mem",Call("sub",v,Apply(P,v)),C)));
        return All("E",Id("Types"),Implies(Call("RealNormedVectorSpace",E),
            All("A",Call("ConeUnitData",E),All("P",Call("RealEndomorphisms",E),
                All("c",Id("R"),Implies(And(positive,Eq(Apply(P,u),Scale(c,u))),
                    All("v",E,Eq(Apply(P,v),Scale(c,v)))))))));
    }

    private static Formula GeneratorStatement()
    {
        var C=Id("C"); var L=Id("L"); var beta=Id("beta"); var z=Id("z");
        var t=Id("t"); var y=Id("y");
        var cp=All("z",C,All("beta",Id("PositiveAlgebraicDual"),
            Implies(Eq(Apply(beta,z),F.D(0)),Le(F.D(0),Apply(beta,Apply(L,z))))));
        var pos=All("t",Id("NonnegativeReals"),All("y",C,
            Call("mem",Apply(Call("exp",Scale(t,L)),y),C)));
        return All("E",Id("Types"),Implies(Call("FiniteDimensionalRealNormedSpace",Id("E")),
            All("A",Call("ConeUnitData",Id("E")),All("L",Call("RealEndomorphisms",Id("E")),
                Implies(cp,pos)))));
    }

    private static Formula QuantitativeStatement(bool algebraic)
    {
        var E=Id("E"); var C=Id("C"); var u=Id("u"); var H=Id("H"); var P=Id("P");
        var beta=Id("beta"); var x=Id("x"); var y=Id("y"); var t=Id("t");
        var r=Id("r"); var q=Id("q"); var Q=Call("norm",Call("square",Id("Hu")));
        Formula Orbit(Formula v) => Apply(Call("exp",Scale(t,H)),v);
        Formula Cert(Formula coefficient,Formula functional) => Call("Certificate",H,coefficient,functional);
        var group=All("t",Id("R"),And(All("y",C,Call("mem",Orbit(y),C)),Eq(Orbit(u),u)));
        var exists=new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create("q"),Id("R"),
            And(Le(F.D(0),q),All("alpha",P,Cert(q,Id("alpha")))));
        var same=All("q",Id("R"),Implies(And(Le(F.D(0),q),All("alpha",P,Cert(q,Id("alpha")))),
            And(All("beta",Id("PositiveDual"),Cert(q,beta)),
                All("beta",Id("PositiveDual"),All("r",Id("PositiveReals"),All("y",C,
                    Implies(Call("mem",Call("sub",Scale(r,u),y),C),
                        Le(Call("square",Call("abs",Apply(beta,Apply(H,y)))),
                            Mul(Mul(Mul(q,r),Apply(beta,y)),Apply(beta,u))))))))));
        var reverse=Implies(group,And(All("beta",Id("PositiveDual"),Cert(Q,beta)),
            All("beta",Id("PositiveDual"),All("x",Id("Effects"),
                Le(Call("square",Call("abs",Apply(beta,Apply(H,x)))),
                    Mul(Mul(Q,Call("min",Apply(beta,x),Apply(beta,Call("sub",u,x)))),Apply(beta,u)))))));
        var result=And(Iff(exists,group),same,reverse);
        if(algebraic) result=And(Call("Closed",C),Call("mem",u,Call("Interior",C)),result);
        return All("E",Id("Types"),Implies(Call("FiniteDimensionalRealNormedSpace",E),
            All("A",Call(algebraic?"ArchimedeanConeUnitData":"ConeUnitData",E),
                All("H",Call("RealEndomorphisms",E),All("P",Call("Subsets",Id("PositiveDual")),
                    Implies(And(Eq(Apply(H,u),F.D(0)),
                        Eq(Call("Closure",Call("Cone",P)),Id("PositiveDual"))),result))))));
    }

    private static Formula Id(string s)=>F.Id(s);
    private static Formula Call(string s,params Formula[] a)=>new Formula.Apply(Id(s),[..a]);
    private static Formula Apply(Formula f,params Formula[] a)=>new Formula.Apply(f,[..a]);
    private static Formula All(string s,Formula type,Formula body)=>new Formula.Bind(
        FormulaQuantifier.ForAll,FormulaIdentifier.Create(s),type,body);
    private static Formula Eq(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Le(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Add(Formula a,Formula b)=>new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula Mul(Formula a,Formula b)=>new Formula.Binary(a,FormulaBinaryOperator.Multiply,b);
    private static Formula Scale(Formula a,Formula b)=>Call("smul",a,b);
    private static Formula Implies(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Iff(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.Iff,b);
    private static Formula And(params Formula[] a)
    {
        var r=a[^1];
        for(var i=a.Length-2;i>=0;i--) r=new Formula.Logic(a[i],FormulaLogicOperator.And,r);
        return r;
    }
}

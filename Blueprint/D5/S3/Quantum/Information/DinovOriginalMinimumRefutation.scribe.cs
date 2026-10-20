using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class DinovOriginalMinimumRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/dinov2026kime");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At two degrees of freedom, a nonuniform phase density has the same joint action marginal as its uniform-phase product comparator and strictly smaller uncertainty in both degrees of freedom.",
        H("The within-DOF minimum clause of equipartition duality fails"),
        Blocks(
            Paragraph(Text("Real.Angle is the quotient AddCircle(2*pi), with angular volume of mass 2*pi. The action reference measure action is Lebesgue measure restricted to strictly positive reals. TorusOne is Real.Angle times the reals, TorusTwo is its square, and CartesianTwo is the square of a real coordinate pair. torusBase is angular volume times action; torusFullBase is its square. Cartesian volume is the standard product Lebesgue measure. The first Bool index selects the degree of freedom; the second selects q for false and p for true. Pair, fst and snd below denote ordered pairing and projections. integral, integralNN, ae, and withDensity use their indicated measures; ofReal is the nonnegative extended-real embedding. Function spaces and products are ordinary function and Cartesian product types.")),
            FourthHarmonicApplication(),
            Node("PsiA", "The action-angle source map", All("z", V("TorusOne"), Eq(Call("PsiA", V("z")),
                Pair(Mul(Call("sqrt", Mul(D(2), Call("snd", V("z")))), Call("sin", Call("fst", V("z")))),
                     Mul(Call("sqrt", Mul(D(2), Call("snd", V("z")))), Call("cos", Call("fst", V("z"))))))),
                "The sine and cosine are those of the quotient angle. PsiA2 applies PsiA independently to the two coordinate pairs. R2(q,p)=q^2+p^2; radialAction takes R2/2 in each degree of freedom, and actionProjection takes the two action coordinates.", true),
            Node("actualCovariance", "Covariance of the actual Cartesian coordinates", All("mu", Call("Measure", V("CartesianTwo")),
                All("i", Call("Product", V("Bool"), V("Bool")), All("k", Call("Product", V("Bool"), V("Bool")),
                Eq(App(Call("actualCovariance", V("mu")), V("i"), V("k")),
                    Call("covariance", Call("actualCoordinate", V("i")), Call("actualCoordinate", V("k")), V("mu")))))),
                "Covariance is the integral of the centered product under the actual law. No covariance matrix is prescribed as a hypothesis."),
            Node("actualUncertainty", "Within-DOF uncertainty", All("mu", Call("Measure", V("CartesianTwo")),
                All("j", V("Bool"), Eq(Call("actualUncertainty", V("mu"), V("j")),
                    Call("sqrt", Call("det", Call("covarianceBlock", V("mu"), V("j"))))))),
                "covarianceBlock(mu,j) is the two by two q,p principal block of actualCovariance(mu), in that order. The uncertainty is its determinant's nonnegative square root, as in Theorem 3.16.", true),
            Node("cartesianLaw", "The normalized Cartesian density law", All("F", DensityType,
                Eq(Call("cartesianLaw", V("F")), Call("withDensity", V("volume"),
                    Lam("x", Call("ofReal", App(V("F"), V("x"))))))),
                "Normalization and nonnegativity are requirements of sourceState; the density law itself is defined for every real-valued function."),
            Node("sourcePullback", "Density pulled back through the source map", All("F", DensityType,
                All("z", V("TorusTwo"), Eq(Call("sourcePullback", V("F"), V("z")),
                    App(V("F"), Call("PsiA2", V("z")))))),
                "sourceTorusLaw(F) is torusFullBase.withDensity(ofReal(sourcePullback(F))). It uses the actual quotient-angle source map."),
            Node("sourceEntropy", "Cartesian differential entropy", All("F", DensityType,
                Eq(Call("sourceEntropy", V("F")), new Formula.Negate(EntropyIntegral(V("F"), false)))),
                "Entropy uses the natural logarithm. sourceUncertainty(F,j) is actualUncertainty(cartesianLaw(F),j). The finite integrals and the torus-to-Cartesian entropy identity are certified in sourceState."),
            Node("actionDensity", "A joint action density", All("r", ActionDensityType,
                Iff(Call("actionDensity", V("r")), And(Call("Measurable", V("r")),
                    And(All("J", ActionPair, Le(D(0), App(V("r"), V("J")))),
                        Eq(Call("integralNN", ActionMeasure, Lam("J", Call("ofReal", App(V("r"), V("J"))))), D(1)))))),
                "actionLaw(r) is the action product measure weighted by ofReal(r). oneActionDensity is the same measurable, nonnegative, unit-mass condition for one action coordinate."),
            Node("sourceState", "Finite-entropy states with their source realization", StateFormula(),
                "The density is Borel measurable, pointwise nonnegative and normalized on Cartesian volume. Every one of its four Cartesian coordinates belongs to L2, and its full four by four actual covariance is positive definite. Both entropy integrands are integrable; their integrals agree, and PsiA2 pushes the actual source law to the Cartesian density law. These extra certificates restrict the universal comparison and are all established for the counterexample."),
            Node("commonActionMarginal", "The same joint marginal in both representations", MarginalFormula(),
                "For almost every positive action pair J, both angular fibers are integrable and their integrals equal r(J). Both source-law action projections and both Cartesian radial-action projections equal actionLaw(r). Marginal equality is joint equality for the same two actions."),
            Node("phaseUniformProduct", "The phase-uniform product comparator", UniformFormula(),
                "The source density equals r(actionProjection(z))/(2*pi)^2 almost everywhere. The joint action density factors almost everywhere into two actually normalized nonnegative one-action densities. This condition certifies existence of the product comparator."),
            Node("dinovTwoDofMinimumClause", "The necessary two-DOF minimum assertion", ClaimFormula(),
                "Conjecture 3.22 (Equipartition duality): \"Fix n ≥ 2, an entropy value s, and an action marginal ρ_J on (0,∞)^n. Among all states on T^n × (0,∞)^n with entropy ≥ s and action marginal ρ_J, the phase-equipartitioned product state (unique when it exists) simultaneously (i) maximizes the entropy, (ii) minimizes every within-DOF uncertainty u_j, and (iii) is the unique state at which the per-DOF conjectured bound of Problem 3.17(b) is saturated for all j; moreover it is the unique fixed point, with the given marginal, of the multi-DOF kime-deformed semigroup ∂t ρ = Σj (−ωj ∂θj + ε ∂θj²) ρ.\" The formal predicate expresses only a necessary specialization of clause (ii), at n=2, on the certified finite-entropy, L2, positive-definite subclass. The original all-n assertion implies clause (ii), which implies this specialization. The predicate has no n quantifier and makes no separate assertion about clauses (i), (iii), or the semigroup."),
            Node("result", "Both uncertainties are smaller than the comparator's", new Formula.Not(V("dinovTwoDofMinimumClause")),
                "Use r(J1,J2)=exp(-(J1+J2)) and independent phases phi(theta)=(1+cos(2*theta)/2)/(2*pi). Each action has density exp(-J), and the comparator has uniform phases. The two Cartesian densities are the products of the actual one-DOF densities exp(-R2/2)*(1+(p^2-q^2)/(2*R2))/(2*pi) and exp(-R2/2)/(2*pi); the first is set to zero at R2=0. The zero-action planes have zero measure. Change of variables proves normalization, the source pushforwards, common joint marginal and entropy equality. Both entropies are finite and nonnegative, so s=0 is admissible. The actual covariance matrices, ordered q1,p1,q2,p2, are diag(3/4,5/4,3/4,5/4) and the identity. Both are positive definite and all coordinates belong to L2. For each of the two degrees of freedom the uncertainties are sqrt(15/16) and 1, respectively, with sqrt(15/16)<1. Adding both strict comparisons contradicts the sum of both inequalities required by the minimum assertion. Thus clause (ii), and hence the simultaneous conjecture as written, fails. Entropy maximization, saturation uniqueness and semigroup claims receive no separate settlement here.",
                role: DescribeRole.Theorem,
                resolution: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("dinov-2026-equipartition-duality-minimum-refutation"), ResolutionKind.Refuted)))));

    private static DocumentBlock FourthHarmonicApplication() => new DocumentBlock.Section(
        H("A fourth-harmonic application to state-level saturation uniqueness"),
        Blocks(
            Paragraph(Text("This application concerns Conjecture 3.22(iii) of Ivo D. Dinov, arXiv:2607.07851v1, with the bound of Problem 3.17(b) and the Williamson convention of Theorem 3.13. The fourth-harmonic counterexample is attributed to prior mathematical work of Wenlin Zhang, Haobo Ma and Ivo D. Dinov; no first-discovery or matrix-inequality priority is asserted. The definitions used here are the existing DinovOriginalMinimumRefutation definitions displayed below: PsiA, PsiA2, sourcePullback, sourceTorusLaw, cartesianLaw, sourceState, commonActionMarginal, phaseUniformProduct, actualCovariance and sourceUncertainty.")),
            Paragraph(Text("The declared theorem result below remains solely the second-harmonic refutation of the minimum clause (ii). Its concluding sentence about assertions receiving no separate settlement refers to that theorem. The fourth-harmonic argument in this section has an archived, compiled exact specialization with standard-axiom evidence, but that specialization is unadmitted and is not a delivered library declaration. This exposition adds no Lean theorem; checking the existing owner's declarations does not newly compile or certify this application.")),
            Paragraph(Text("Fix n=2, the entropy lower threshold s=0, and r0(J1,J2)=exp(-(J1+J2)) on (0,infinity)^2. Angles lie in Real.Angle=AddCircle(2*pi). Their reference is angular Lebesgue volume of mass 2*pi, not probability-normalized Haar measure. Actions use action=volume restricted to J>0; torusBase is their angle-action product and torusFullBase its square. PsiA(theta,J)=(sqrt(2*J)*sin(theta),sqrt(2*J)*cos(theta)), in q,p order, and PsiA2 acts on both pairs. Lemma 2.3 supplies a smooth chart off zero action. Definition 2.4 and the static conjecture require probability densities on positive actions, without imposing smooth extension across the Cartesian zero-action planes. The witnesses below have the additional Borel, finite-entropy, L2 and positive-definiteness certificates in sourceState; these do not identify that subclass with the full source class.")),
            Paragraph(Text("The reference-volume transport can be seen directly through ordinary polar coordinates (r,t). Set H(r,t)=(t,r^2/2) for r>0 and -pi<t<pi. Its derivative matrix is [[0,1],[r,0]], its determinant is -r, and its inverse on the image is (t,J) mapped to (sqrt(2*J),t). Thus the Jacobian-weighted polar measure r dr dt maps under H to dt dJ. The real action-angle map composed with H is the polar map followed by the swap of the two Cartesian coordinates. The two Jacobian formulas and invariance of product Lebesgue measure under that swap give real-chart volume transport. The omitted ray and origin are null; replacing (-pi,pi) by (-pi,pi] changes no measure. AddCircle.measurePreserving_mk at period 2*pi and initial point -pi then passes to quotient angles. Consequently map(PsiA,torusBase)=volume and map(PsiA2,torusFullBase)=volume. This also explains why no angular entropy shift is introduced.")),
            Paragraph(Text("Let a4(theta)=(1+cos(4*theta)/2)/(2*pi) and a0(theta)=1/(2*pi), both as quotient-angle functions. They are continuous, strictly positive, normalized against angular volume, and bounded above by 1; specifically 1/(4*pi)<=a4<=3/(4*pi)<1. For a Cartesian pair write R=q^2+p^2 and P=p^4-6*p^2*q^2+q^4. Define f4(q,p)=exp(-R/2)*(1+P/(2*R^2))/(2*pi) when R>0, and f4(0,0)=0. Define g(q,p)=exp(-R/2)/(2*pi) also at the origin. For x=((q1,p1),(q2,p2)), put F4(x)=f4(q1,p1)*f4(q2,p2) and G(x)=g(q1,p1)*g(q2,p2). Here F4 and G name actual Cartesian density functions, not just angular profiles. The polynomial inequalities -R^2<=P<=R^2 give nonnegativity; the piecewise rational formula is Borel measurable and continuous where both radii are positive. The finite zero extension on the null zero-action planes is not a claim of continuity or smoothness there.")),
            Paragraph(Text("For J>0, R(PsiA(theta,J))=2*J and P(PsiA(theta,J))/R(PsiA(theta,J))^2=cos(4*theta). The latter follows from cos(4*theta)=8*cos(theta)^4-8*cos(theta)^2+1. Therefore f4(PsiA(theta,J))=a4(theta)*exp(-J), while g(PsiA(theta,J))=a0(theta)*exp(-J). For either a=a4 or a=a0, set h_a(theta,J)=a(theta)*exp(-J) and rho_a(z)=h_a(z1)*h_a(z2). The corresponding sourcePullback equals rho_a almost everywhere for torusFullBase. Since the angular integral of a and the positive-action integral of exp(-J) are both 1, rho_a has total mass 1. Weighted reference-volume transport gives map(PsiA2,sourceTorusLaw(F))=cartesianLaw(F), for F=F4 and F=G separately, and proves that all four source and Cartesian laws are probability measures.")),
            Paragraph(Text("The common action law is the full joint probability measure actionLaw(r0), whose density factors into the two normalized densities exp(-J1) and exp(-J2). For every positive action pair J, each angular fiber rho_a((theta1,J1),(theta2,J2)) is integrable on the compact angular square and its integral is exp(-(J1+J2))=r0(J). Thus both required almost-everywhere fiber certificates hold. Moreover map(actionProjection,sourceTorusLaw(F4))=actionLaw(r0), map(actionProjection,sourceTorusLaw(G))=actionLaw(r0), map(radialAction,cartesianLaw(F4))=actionLaw(r0), and map(radialAction,cartesianLaw(G))=actionLaw(r0). The last two equalities use radialAction composed with PsiA2 equal to actionProjection almost everywhere on positive actions, together with the weighted transports. These are all six components of commonActionMarginal, not a comparison of action means. G also satisfies phaseUniformProduct: its source density is r0(actionProjection(z))/(2*pi)^2 and its two action factors are individually normalized.")),
            Paragraph(Text("Entropy requires genuine integrability before transport. For either profile a, compactness and strict positivity make a and a*log(a) integrable on Real.Angle. The Gamma integrals at parameters 1 and 2 give integrability of exp(-J) and J*exp(-J) on positive actions. The identity h_a*log(h_a)=(a*log(a))*exp(-J)-a*(J*exp(-J)), with the two variables separated, proves one-pair log-density integrability. For the two-pair product, rho_a*log(rho_a) is the sum of (h_a*log(h_a)) in the first pair times h_a in the second and the reversed product, so it too is integrable. Measurability and reference-volume transport then prove integrability of F*log(F) on Cartesian volume and of sourcePullback(F)*log(sourcePullback(F)) on torusFullBase, and equality of these two integrals for each F separately. At zero density use the usual 0*log(0)=0 integral convention. On positive actions 0<rho_a<=1, hence -rho_a*log(rho_a)>=0. Accordingly sourceEntropy(F4)>=0 and sourceEntropy(G)>=0, so both meet s=0. No equality between these two state entropies is assumed or asserted.")),
            Paragraph(Text("For each of the angular laws a4(theta)dtheta and a0(theta)dtheta, the exact moments are E[sin(theta)]=E[cos(theta)]=E[sin(theta)*cos(theta)]=0 and E[sin(theta)^2]=E[cos(theta)^2]=1/2. One way to check every entry is to rewrite a4 as (3/2-4*cos(theta)^2+4*cos(theta)^4)/(2*pi), integrate cosine powers through degree six on [-pi,pi], and use the sine-times-cosine-power integral with equal endpoint cosines; sin(theta)^2=1-cos(theta)^2 supplies the remaining square. The uniform moments follow from the corresponding sine and cosine integrals. These are the first and second harmonic cancellations needed for covariance, with the fourth harmonic retained in the density.")),
            Paragraph(Text("Under either one-pair law, angle and action are independent and E[J]=integral(J*exp(-J),J>0)=1. Measurable coordinate squares are integrable: their weighted integrals separate into 2*integral(J*exp(-J)) times the bounded angular square integral. The actual coordinates therefore belong to L2 under the one-pair law, and product projection followed by PsiA2 transport gives MemLp 2 for all four actualCoordinate functions under each Cartesian law. This justifies the first and mixed moments, rather than presupposing finite covariance. Both Cartesian means vanish, E[q^2]=E[p^2]=1 and E[q*p]=0 within each pair. Independence of the two pairs and their zero means gives all cross-pair covariances zero. In q1,p1,q2,p2 order, all four diagonal entries are 1 and all twelve off-diagonal entries are 0: actualCovariance(cartesianLaw(F4))=I4=actualCovariance(cartesianLaw(G)). These are covariances of the realized probability laws. Matrix.PosDef.one establishes their positive definiteness, completing every sourceState component together with the normalization, entropy and transport facts above.")),
            Paragraph(Text("Use the source symplectic convention in the same order: Omega=diag([[0,1],[-1,0]],[[0,1],[-1,0]]). A frequency-one Williamson certificate requires 1>0 and a matrix S with S*Omega*S^T=Omega and S*Sigma*S^T=I4. For each actual covariance Sigma=I4, choose S=I4. Thus both positive frequencies are 1, with both matrix identities satisfied in the stated convention. Each actual q,p covariance block is I2, so sourceUncertainty(F4,j)=sqrt(det(I2))=1=sourceUncertainty(G,j) for every j in Bool. Both states simultaneously attain the per-DOF value 1 associated with their minimum symplectic frequency. This identity certificate does not prove a general Williamson theorem, general-spectrum bound or orbit-sharpness result.")),
            Paragraph(Text("The actual Cartesian probability laws are unequal. If cartesianLaw(F4)=cartesianLaw(G), uniqueness of withDensity densities over sigma-finite Lebesgue measure would give equality of their nonnegative real densities almost everywhere. On the open set where both radii are positive, both densities are continuous and Lebesgue measure has full support. Measure.eqOn_open_of_ae_eq would therefore force pointwise equality throughout that open set. At x=((0,1),(0,1)), each fourth-harmonic factor is 3/2 times the corresponding Gaussian factor, so F4(x)=(9/4)*G(x), with G(x)>0, a contradiction. The open-set argument is essential: a discrepancy at one point alone would not distinguish probability laws.")),
            Paragraph(Text("Specialize the source's state-level uniqueness assertion to n=2, s=0 and r0. Its necessary consequence says that a pair of sourceState densities with commonActionMarginal, a phaseUniformProduct comparator, both entropy lower bounds, both actual covariances I4, both positive frequency-one certificates and both all-j saturations must have equal Cartesian laws. Indeed uniqueness would identify the source states modulo null sets, hence their source laws; their PsiA2 pushforwards would then identify the Cartesian laws. F4 and G satisfy every antecedent just established and violate that consequence. This supplies the fourth-harmonic failure of the clause-(iii) specialization within the stated static source class. It neither invokes the earlier clause-(ii) contradiction nor replaces law inequality with angular pointwise nonuniformity. It leaves the fixed-covariance symplectic inequality intact: the two different density laws have exactly the same covariance and frequencies.")),
            Paragraph(Text("The reused suppliers are pinned Mathlib at db584cd6d46c92f209a44c0f1c829460d327499d with Lean v4.33.0. The transport uses map_withDensity_abs_det_fderiv_eq_addHaar, the polarCoord derivative and null-complement facts, AddCircle.measurePreserving_mk and Measure.map_prod_map. Integral transport and product decomposition use integral_map, MeasurePreserving.integrable_comp, integral_prod_mul and prod_withDensity; normalization and log-integrability use GammaIntegral_convergent and integral_exp_neg_Ioi_zero. The angular calculations use AddCircle.intervalIntegral_preimage, integral_cos_pow and integral_sin_pow_odd_mul_cos_pow. Actual L2 and covariance use memLp_two_iff_integrable_sq, memLp_map_measure_iff, covariance_map and covariance_fst_snd_prod; weighted-density uniqueness and Measure.eqOn_open_of_ae_eq give the law distinction. These applications are distinct from the frozen owner's clause-(ii) result, whose local proof steps are not exported helper declarations.")),
            Paragraph(Text("The wider Dinov program remains open here: general weighted-harmonic covariance and moment bridges, strict modulus and trace-energy equality; continuous conditional Gibbs/KL identities, normalized fibers and zero-KL equality; the actual Bessel normalization, derivatives, monotonicity, endpoints and inverse range; sharp centered iid variational minima, attainment and all equality cases, including common action-independent orientation, floor endpoints and the empty class above maximal entropy; derivative and endpoint regularity, smooth minimizers, exact harmonic entropy, Gaussian comparison and analytic noncentered improvement; non-iid joint-law KL and mutual-information decomposition and the exact attainable-area region with boundary equality cases; general canonical-pair symplectic bounds and orbit sharpness; and positive-diffusion stationary uniqueness, convergence and entropy production under the required solution regularity. No conclusion about pure transport dynamics, general n, a general symplectic spectrum or the whole conjecture's other assertions follows from this exposition."))));

    private static DocumentBlock Node(string declaration, string title, Formula formula,
        string prose, bool literature = false, DescribeRole role = DescribeRole.Definition,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("dinov-minimum-" + declaration.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.FromAuthor(Disp(formula)),
        literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Pair(Formula a, Formula b) => Call("pair", a, b);
    private static Formula Lam(string name, Formula body) => Seq(Named("fun"), Sp, V(name), Sp, Mapsto, Sp, Grp(body));
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Grp(a), FormulaLogicOperator.And, Grp(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Grp(a), FormulaLogicOperator.Implies, Grp(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, Grp(b));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Grp(a), b);
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula DensityType => new Formula.TypeArrow(V("CartesianTwo"), R);
    private static Formula ActionPair => Call("Product", R, R);
    private static Formula ActionDensityType => new Formula.TypeArrow(ActionPair, R);
    private static Formula OneActionDensityType => new Formula.TypeArrow(R, R);
    private static Formula ActionMeasure => Call("prod", V("action"), V("action"));
    private static Formula Law(Formula f) => Call("cartesianLaw", f);
    private static Formula TorusLaw(Formula f) => Call("sourceTorusLaw", f);
    private static Formula EntropyFunction(Formula f, bool torus) => Lam("x", Mul(
        torus ? Call("sourcePullback", f, V("x")) : App(f, V("x")),
        Call("log", torus ? Call("sourcePullback", f, V("x")) : App(f, V("x")))));
    private static Formula EntropyIntegral(Formula f, bool torus) =>
        Call("integral", torus ? V("torusFullBase") : V("volume"), EntropyFunction(f, torus));

    private static Formula StateFormula()
    {
        var f = V("F");
        return All("F", DensityType, Iff(Call("sourceState", f),
            And(Call("Measurable", f), And(All("x", V("CartesianTwo"), Le(D(0), App(f, V("x")))),
            And(Call("IsProbabilityMeasure", Law(f)), And(Call("Integrable", EntropyFunction(f, false), V("volume")),
            And(All("i", Call("Product", V("Bool"), V("Bool")), Call("MemLp", Call("actualCoordinate", V("i")), D(2), Law(f))),
            And(Call("PosDef", Call("actualCovariance", Law(f))),
            And(Call("Integrable", EntropyFunction(f, true), V("torusFullBase")),
            And(Eq(EntropyIntegral(f, true), EntropyIntegral(f, false)),
                Eq(Call("map", V("PsiA2"), TorusLaw(f)), Law(f))))))))))));
    }

    private static Formula Fiber(Formula f) => Lam("ts", Call("sourcePullback", f,
        Pair(Pair(Call("fst", V("ts")), Call("fst", V("J"))), Pair(Call("snd", V("ts")), Call("snd", V("J"))))));
    private static Formula Fibers(Formula f) => Call("ae", ActionMeasure, Lam("J",
        And(Call("Integrable", Fiber(f), V("volume")), Eq(Call("integral", V("volume"), Fiber(f)), App(V("r"), V("J"))))));
    private static Formula ActionMap(Formula f, bool torus) => Eq(
        Call("map", V(torus ? "actionProjection" : "radialAction"), torus ? TorusLaw(f) : Law(f)), Call("actionLaw", V("r")));
    private static Formula MarginalFormula() => All("F", DensityType, All("G", DensityType, All("r", ActionDensityType,
        Iff(Call("commonActionMarginal", V("F"), V("G"), V("r")), And(Fibers(V("F")), And(Fibers(V("G")),
            And(ActionMap(V("F"), true), And(ActionMap(V("G"), true), And(ActionMap(V("F"), false), ActionMap(V("G"), false))))))))));
    private static Formula UniformFormula() => All("G", DensityType, All("r", ActionDensityType,
        Iff(Call("phaseUniformProduct", V("G"), V("r")), And(
            Call("aeEq", V("torusFullBase"), Call("sourcePullback", V("G")), Lam("z",
                new Formula.Fraction(App(V("r"), Call("actionProjection", V("z"))), Pow(Mul(D(2), Pi), D(2))))),
            Exists("rone", OneActionDensityType, Exists("rtwo", OneActionDensityType,
                And(Call("oneActionDensity", V("rone")), And(Call("oneActionDensity", V("rtwo")),
                    Call("aeEq", ActionMeasure, V("r"), Lam("J", Mul(App(V("rone"), Call("fst", V("J"))), App(V("rtwo"), Call("snd", V("J"))))))))))))));
    private static Formula ClaimFormula() => Iff(V("dinovTwoDofMinimumClause"), All("s", R, All("r", ActionDensityType,
        All("F", DensityType, All("G", DensityType,
            Imp(Call("actionDensity", V("r")), Imp(Call("sourceState", V("F")), Imp(Call("sourceState", V("G")),
            Imp(Call("commonActionMarginal", V("F"), V("G"), V("r")), Imp(Call("phaseUniformProduct", V("G"), V("r")),
            Imp(Le(V("s"), Call("sourceEntropy", V("F"))), Imp(Le(V("s"), Call("sourceEntropy", V("G"))),
                All("j", V("Bool"), Le(Call("sourceUncertainty", V("G"), V("j")), Call("sourceUncertainty", V("F"), V("j"))))))))))))))));
}

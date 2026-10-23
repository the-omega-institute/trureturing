using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class NativeBorelCommonFlowDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelCommonFlow.";

    public DocumentDefinition Create()
    {
        Formula flow = F.Id("F"), q = F.Id("Q"), w = F.Id("W");
        Formula pset = F.Id("P"), bset = F.Id("S");
        Formula n = F.Id("n"), i = F.Id("i");
        Formula c = Call("C", flow), l = Call("L", flow), mu = Call("nuP", flow);
        Formula g = F.Id("g"), cb = Fraction(Num(9), Num(25));
        Formula normalized = Call("normalizedIterate", flow, g, Num(3), q);
        Formula f = F.Id("f"), f1 = F.Id("f1"), f2 = F.Id("f2");
        Formula zb = Fraction(Num(6), Num(25));
        Formula iteration = All(Equal(Call("coordinate", n, i, q),
            Call("iterate", l, Call("coordinate", Num(0), i), n, q)),
            ("n", "Nat"), ("i", "Letter"));
        Formula completion = Equal(Call("g", q), Times(
            Seq(Open, Sub(Num(1), Call("u", q)), Close), Call("BIntegral", flow, q,
                Call("oneMinusV"))));
        Formula wordStatement = All(And(Equal(Call("measureComp", c, mu), mu),
            And(Ae(mu, q, iteration), Ae(mu, q, completion))), ("F", "CommonFlow"));
        Formula rows = All(And(Le(Call("smul", Fraction(Num(1), Num(5)),
            Call("row", c, q)), Call("row", l, q)),
            Le(Call("row", l, q), Call("smul", Fraction(Num(4), Num(15)),
                Call("row", c, q)))), ("Q", "PDescriptor"));
        Formula bounded = And(Le(cb, Call("g", q)), And(
            Le(Call("g", q), Fraction(Num(4), Num(9))),
            Le(Call("iterate", l, g, Num(3), q), Times(cb, Pow(zb, Num(3))))));
        Formula normalizedStep = All(Imp(Call("Measurable", f),
            Equal(Call("normalizedIterate", flow, f, Seq(n, Plus, Num(1)), q),
                Call("normalizedAction", flow,
                    Call("normalizedIterate", flow, f, n), q))),
            ("F", "CommonFlow"), ("f", "PDescriptorFunction"), ("n", "Nat"),
            ("Q", "PDescriptor"));
        Formula actionAdd = All(Imp(Call("Measurable", f1),
            Equal(Call("normalizedAction", flow, Seq(f1, Plus, f2), q),
                Seq(Call("normalizedAction", flow, f1, q), Plus,
                    Call("normalizedAction", flow, f2, q)))),
            ("F", "CommonFlow"), ("f1", "PDescriptorFunction"),
            ("f2", "PDescriptorFunction"), ("Q", "PDescriptor"));
        Formula averageAction = All(Equal(Call("normalizedAction", flow,
                Call("threeStepAverage", flow), q),
            new Formula.Fraction(Seq(Call("normalizedIterate", flow, g, Num(1), q), Sp, Plus, Sp,
                Call("normalizedIterate", flow, g, Num(2), q), Sp, Plus, Sp,
                Call("normalizedIterate", flow, g, Num(3), q)), Num(3))),
            ("F", "CommonFlow"), ("Q", "PDescriptor"));
        Formula boundsStatement = All(And(rows, Ae(mu, q, bounded)), ("F", "CommonFlow"));
        Formula coreStatement = All(ThereExists(
            And(Call("MeasurableSet", pset), And(Call("MeasurableSet", bset),
            And(Ae(mu, q, Call("Member", q, pset)),
            And(Ae(Call("nuB", flow), w, Call("Member", w, bset)),
            And(All(Imp(Call("Member", q, pset), And(Call("goodP", flow, q),
                Ae(Call("BRow", flow, q), w, Call("Member", w, bset)))),
                ("Q", "PDescriptor")),
                All(Imp(Call("Member", w, bset), And(Call("goodB", flow, w),
                Ae(Call("ARow", flow, w), q, Call("Member", q, pset)))),
                ("W", "BDescriptor"))))))),
            ("P", "PSet"), ("S", "BSet")), ("F", "CommonFlow"));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Acquired common flows on full legal-tail probability descriptors.",
            H("Full laws and the acquired return"), Blocks(
                Paragraph(Text("ValidTail(p) consists of every complete word pWord(n,i) and the infinite noncompletion outcome. ValidTail(beta) consists of betaStop, every alpha-prefixed pWord(n,i), and noncompletion. These are the legal full-tail carriers of NativeFullResidual, whose renderer retains original operation blocks and complete-law total variation. The source draws one positive depth K from a fixed finite or countable prior before the first paid Read. Conditional on that same K=k, NativeConditionalControl.DepthLaw.rate is F_(k+1)/F_(k+3). Positive prior masses at depths 1 and 2 supply rates 1/3 and 2/5; every other supported depth remains a target. The analysis below introduces no observer registers.")),
                Paragraph(Text("RegularDescriptor(s) is a probability law on ValidTail(s), with emission in [1/3,2/5] and every source tail inequality at rate 4/15. The suspended tail has the additional factor 2/5. Its measurable structure is inherited from the Giry evaluation structure. Equality of this structure with complete-law-TV Borel is not asserted by the statements here.")),
                Paragraph(Text("CommonFlow contains the original probability measures GammaB and GammaA, their four common unweighted margins nuP and nuB, and the same exhibited Markov disintegrations B and A. Both complete-atom endpoint boxes are included, including noncompletion. The residual contract equates (1-u(Q)) inverse times the prefix-deleted input law to the full B barycenter, and v(W) inverse times the prefix-deleted input law to the full A barycenter. The legal-word partitions then reconstruct the input measure: law(Q)=u(Q) delta_alpha+(1-u(Q)) map(prependB,barycenter(B(Q))); law(W)=(1-v(W)) delta_beta+v(W) map(prependA,barycenter(A(W))). Barycenters are full opposite laws, without opposite regularity requirements. prependB and prependA restore the deleted original letter and preserve noncompletion.")),
                Paragraph(Text("The original input-test presentation is equivalent to this residual contract. Fix the original GammaB, with GammaB=nuP compProd B. For every complete beta tail a, including infinity, and every bounded real Borel function phi of the entire p input descriptor, require integral phi(Q)[law(Q){prependB(a)}-(1-u(Q))law(W){a}] dGammaB(Q,W)=0. On the same fixed GammaA=nuB compProd A, require integral phi(W)[law(W){prependA(a)}-v(W)law(Q){a}] dGammaA(W,Q)=0 for every complete p tail a and bounded Borel phi. These are unnormalized tests on the original unweighted margins and acquired disintegrations; no new joint realization is selected for different tests.")),
                Paragraph(Text("To derive the normalized identities, divide each input test by its input denominator. Regularity gives 3/5 <= 1-u <= 2/3 and 1/3 <= v <= 2/5, so multiplying a bounded test by either reciprocal remains a bounded Borel test. The complete-law TV Borel structure equals the inherited evaluation structure by NativeBorelTVTopology.descriptor_tv_borel_eq. Measure.integral_compProd on the same joint measure then converts each tested discrepancy to its marginal integral. Apply Integrable.ae_eq_zero_of_forall_setIntegral_eq_zero to the singleton-coordinate discrepancy using indicator tests. The discrepancy is measurable and bounded by two. The countable complete tail family, including infinity, synchronizes these equalities on one conull input set, and Measure.ext_of_measureReal_singleton identifies the entire acquired residual measure. Conversely, the residual identity, the same Fubini equation and multiplication by the bounded denominator recover every original joint test. This applies separately to both phases with their own denominators and unchanged opposite-law barycenters.")),
                Paragraph(Text("C is A composed after B. L weights the A row by v(W) and the resulting B composition by 1-u(Q). Thus its action is (Lf)(Q)=(1-u(Q)) integral v(W) integral f(Qprime) A(W,dQprime) B(Q,dW). iterate(L,f,0)=f and iterate(L,f,n+1) is integration of iterate(L,f,n) against the L row. coordinate(n,i,Q) is Q{pWord(n,i)} and g(Q)=coordinate(0,1,Q). AE(mu,Q,P) denotes P for mu-almost every Q; BIntegral(F,Q,oneMinusV) denotes the integral of 1-v under the original B row. measureComp, row and smul denote measure composition, kernel evaluation and nonnegative measure scaling.")),
                Paragraph(Text("For uniform normalized stability, the source operator P is CommonFlow.C, and source L is the actual withDensity-weighted composition CommonFlow.L. Fix one CommonFlow throughout both endpoint estimates. Its nuP and nuB are the original common unweighted marginals, and A and B are the original whole-descriptor disintegrations. The full coordinate boxes and normalized residual identities hold AE on those marginals. Descriptor probabilities can have arbitrary Borel support; no finite-support reduction occurs.")),
                Paragraph(Text("The signed real action is L_R f(Q)=integral f(Qprime) d(L(Q)), with L_R^0 f=f and L_R^(j+1) f=L_R(L_R^j f). A bounded Borel real f is integrable on each finite L row, whose mass is at most one. StronglyMeasurable.integral_kernel supplies Borel measurability of its action, and the integral norm bound preserves a global bound through every iterate. Bochner integral_add, integral_sub and integral_const_mul supply real linearity. In particular all subtraction in this argument is signed real subtraction.")),
                Paragraph(Text("Kernel.integral_withDensity and Kernel.integral_comp instantiate the real action as (1-u(Q)) integral v(W) integral f(Qprime) A(W,dQprime) B(Q,dW), with ENNReal weights converted to real values. Their integrability premises follow from boundedness and the Markov A/B rows. The original C-stationarity and Measure.ae_ae_of_ae_comp transfer any nuP-null input exception to C(Q)-null rows AE; L(Q) <= C(Q) then transfers it to L(Q). Thus L_R respects AE equality and AE order on the original nuP quotient.")),
                Paragraph(Text("Put kappa=1/5 and lambda=4/15. The existing measure inequalities kappa C(Q) <= L(Q) <= lambda C(Q), integral_mono_measure and C-stationarity give kappa integral f dnuP <= integral L_R f dnuP <= lambda integral f dnuP for bounded nonnegative Borel f. If nonnegativity holds only AE, replace f by max(f,0) and use the AE congruence just described. Positivity and induction give kappa^j integral f <= integral L_R^j f <= lambda^j integral f for every natural j. This induction uses the same original marginal and does not require commutation or an invariant probability for L.")),
                Paragraph(Text("For r=a=1/3 or r=b=2/5, set z_r=r(1-r), c_r=(1-r)^2, and sigma_r=1 at a and -1 at b. Write g_R(Q)=Q{pAtom(0,1)}, q_j=L_R^j g_R, w=L_R 1, F_r=sigma_r(c_r-g_R), h_j=sigma_r(q_j-c_r z_r^j), and V_r=sigma_r(w-z_r). All coordinate values in these formulas are real values of the actual complete measures. The original common_flow_word_iteration identifies q_j AE with Q{pAtom(j,1)} for every j. Completion bounds make F_r nonnegative AE.")),
                Paragraph(Text("Let x_r(Q)=|u(Q)-r| and y_r(W)=|v(W)-r|, in real coordinates. The original completion residual gives g_R=(1-u)(1-Bv) and w=1-u-g_R. Hence V_r=F_r-x_r, F_r=(1-r)x_r+(1-u)B y_r=(1-r)B y_r+(1-Bv)x_r. Since u and v lie in [1/3,2/5], both decompositions give F_r >= (1-r)x_r and F_r >= (1-r)B y_r. V_r can be negative; its role below is an upper predecessor bound.")),
                Paragraph(Text("Complete configuration TV is half the sum over every t in ValidTail(s) of |D{t}-native(s,r){t}|. This sum includes the infinite outcome. Singleton masses are summable by Measure.tsum_indicator_apply_singleton and ENNReal.summable_toReal. If one event selects exactly the positive differences, splitting that full sum into the event and its complement and using normalization identifies TV with the signed event difference. The event is finite, but the complementary sum retains all other finite atoms and infinity. This is TV of each descriptor law before integration.")),
                Paragraph(Text("For p, the sign event is Ep={pAtom(0,1),pAtom(1,1),pAtom(2,1)}. For beta it is Eb={betaStop,betaAtom(0,1)}. The endpoint native masses give marker-zero p ratio (6/5)(27/25)^j and marker-one ratio (81/100)(27/25)^j. The latter is below one at j=2 and above one at j=3, and remains above one thereafter. At beta, the standalone ratio is 9/10 and the prefixed marker-one ratio is (243/250)(27/25)^j. The full boxes therefore give the required signs on the entire carrier, including the zero infinite masses, for both endpoint choices.")),
                Paragraph(Text("Put f_j=sigma_r(c_r z_r^j-q_j), for j=0,1,2. The complete signed-event calculation gives TV_p=f_0+f_1+f_2. The original public A_coordinate supplier, applied without changing its statement or proof, gives W{betaAtom(0,1)}=v(W) A g_R(W). The same complete signed-event calculation yields TV_beta=(1-c_r)y_r+v A F_r.")),
                Paragraph(Text("The p recurrence is f_(j+1)=L_R f_j+c_r z_r^j(x_r-F_r), with f_0=F_r. The bound F_r >= (1-r)x_r implies c_r(x_r-F_r) <= z_r F_r. Applying AE order through L_R once gives TV_p <= (1+z_r+z_r^2)F_r+(1+z_r)L_R F_r+L_R^2 F_r. Measurability and boundedness of these actual losses follow from their complete countable sums; each loss lies in [0,1].")),
                Paragraph(Text("The original disintegration and marginal fields give B composed with nuP = nuB and A composed with nuB = nuP. Kernel.integral_comp transports bounded real integrals across these unweighted identities. Let Phi_r=integral F_r dnuP. Integrating F_r >= (1-r)B y_r gives (1-r) integral y_r dnuB <= Phi_r. AE nonnegativity of A F_r and v <= 2/5 then give integral TV_beta dnuB <= ((1-c_r)/(1-r)+2/5)Phi_r.")),
                Paragraph(Text("Define M_r=1+z_r+z_r^2+(1+z_r)lambda+lambda^2. Integrating the p estimate with the first two upper iterate comparisons gives integral TV_p dnuP <= M_r Phi_r. At both r=a,b, ((1-c_r)/(1-r)+2/5) <= M_r. Consequently E_r=max(integral TV_p dnuP,integral TV_beta dnuB) <= M_r Phi_r, on the same actual pair.")),
                Paragraph(Text("The late marker-one ordering and full boxes give h_j >= 0 AE for every j>=3. For n>=4, h_(n-1) is nonnegative and L_R h_(n-1)=h_n-c_r z_r^(n-1)V_r >= 0. Thus V_r <= h_n/(c_r z_r^(n-1)). This bounds V_r from above and supplies no positive lower bound for it.")),
                Paragraph(Text("Expand exactly three steps: L_R^3 1-z_r^3 = z_r^2(w-z_r)+z_r L_R(w-z_r)+L_R^2(w-z_r). Real linearity therefore gives L_R^3 F_r=c_r[z_r^2 V_r+z_r L_R V_r+L_R^2 V_r]-h_3. Since h_3>=0, apply the predecessor upper bound and AE order zero, one and two times to obtain L_R^3 F_r <= (z_r^3/z_r^n)[h_n+z_r^(-1)L_R h_n+z_r^(-2)L_R^2 h_n]. The block length remains three for every n.")),
                Paragraph(Text("Let d_n=integral Q{pAtom(n,1)} dnuP, e_(a,n)=d_n-c_a z_a^n and e_(b,n)=c_b z_b^n-d_n. Coordinate iteration and real integral linearity identify integral h_n=e_(r,n). The lower three-step comparison for F_r and upper comparisons for h_n then give kappa^3 Phi_r <= (z_r^3/z_r^n)[1+lambda/z_r+(lambda/z_r)^2]e_(r,n). Only kappa^3 enters this normalized bound.")),
                Paragraph(Text("Combining the two loss estimates with that fixed block gives E_r <= H_r e_(r,n)/(c_r z_r^n) for both endpoints and every integer n>=4, where H_r=M_r c_r kappa^(-3) z_r^3[1+lambda/z_r+(lambda/z_r)^2]. Exact rational evaluation gives H_a=9839648/2657205 and H_b=20723912/5859375. Neither the constants nor the block length depend on the pair or on n. This is the full-domain normalized stability statement of source Theorem 6.3.")),
                Paragraph(Text("For a fixed prior mu on positive depths, retain J=max over phases s of [sup over every k with mu(k)>0 of integral TV(D,native(s,DepthLaw.rate(k))) dnu_s-rho_s], with rho_p=1116529/22781250 and rho_beta=239/6750. The supremum remains over the entire supported set, including nonendpoint depths. Every target loss is a measurable complete-law loss bounded by one, so the real supported supremum is bounded. Exact Fibonacci evaluation gives DepthLaw.rate(1)=a and DepthLaw.rate(2)=b; positive mu(1),mu(2) only insert these two particular terms into that full supremum.")),
                Paragraph(Text("The complete p endpoint distance is 2rho_p. Pointwise countable-law triangle inequality, integration on the original nuP and the supported opposite endpoint give rho_p <= J+E_r. Thus J+H_r e_(r,n)/(c_r z_r^n) >= rho_p for both r and every n>=4. This argument concerns the original full supported-depth risk, not a finite observer table.")),
                Paragraph(Text("For arbitrary Borel probability marginals on RegularDescriptor(p) and RegularDescriptor(beta), J=0 gives each endpoint mean loss <=rho_s through those supported terms. At a complete coordinate t, the real triangle slack is |D{t}-P_a{t}|+|D{t}-P_b{t}|-|P_a{t}-P_b{t}|, which is nonnegative and integrable. Its full countable sum is 2(TV(D,P_a)+TV(D,P_b))-4rho_s. Each coordinate slack is bounded above by that sum, so the endpoint budgets force its integral to zero. integral_eq_zero_iff_of_nonneg makes it zero AE; countability synchronizes all coordinates. Equality in the real absolute-value triangle places every mass between the endpoint masses, giving the full AE EndpointBox, including infinity. This implication requires no finite-support assumption and no preexisting box assumption.")),
                Paragraph(Text("The boxed p midpoint is a separate condition: integral Q(Ep) dnuP=11758471/22781250, together with CommonFlow. The complete Ep formula then gives each p endpoint mean loss exactly rho_p, hence E_r>=rho_p. It does not impose the suspended midpoint or replace the full supported-target budget. On a boxed pair with J=0, the full triangle bound also gives E_r>=rho_p.")),
                Paragraph(Text("On either of these classes, normalized stability implies e_(r,n)/(c_r z_r^n) >=rho_p/H_r for both endpoints and every n>=4. The two inequalities constrain one and the same d_n: c_a z_a^n(1+rho_p/H_a) <= d_n <= c_b z_b^n(1-rho_p/H_b). They are simultaneous necessary bounds on that pair.")),
                Paragraph(Text("For a proposed repaired pair satisfying one of those classes, write d_n=c_a z_a^n+Delta_n. For every n>=5 the necessary lower correction is Delta_n >=(90438849/15374450000)(2/9)^n>0. The bound holds termwise even when the repaired pair varies with n, provided each pair meets the full hypotheses. Its absolute size decays; it supplies no uniform positive absolute correction. The uncorrected NULL155 flows are not CommonFlow inputs: their entire margins and omitted residuals must first be repaired.")),
                Paragraph(Text("The source parameters (m,d,l,n_source)=(2,1,2,4) stay fixed while the return index n varies. One source depth is sampled before Read, and both seeds, every paid rejection and return, partial parses, marker triples, bare and held records, selectors, write and latch flags, permissions, the third write before latch, fourth completion, delivery and matching Stop remain part of the original complete record. Terminal states have no Read. Initialization is source-independent; acquired and synthetic updates coincide. The full-record measurable bijection retains noncompletion, total variation and every future operation block.")),
                Paragraph(Text("These analytical bounds neither construct a feasible full pair nor provide a finite representation, exact sampler, installed program, paid execution, physical attainment, literal U or a general critical cost. COMPLETE still charges control, program and numbers, selectors, addresses, labels, cursors, sampler state, workspace and persistent randomness. Descriptors and kernels are analytical objects rather than free observer ports or refreshed source depths. No recurrence, native-singleton, mixing, reversibility, deterministic-successor, commutation or invariant-L assumption is added.")),
                Node("common-flow-word-iteration", "common_flow_word_iteration",
                    "Both entire word families", wordStatement,
                    "The disintegrations and common margins make nuP stationary for C. Evaluating the two full residual identities at each complete word gives the one-return recurrence. L is dominated by C, so stationarity transports the null exceptions through every iterate. Countable conjunction yields one full-measure set for every index and bit. At the first marker-one word, reconstruction gives the completion integral."),
                Node("common-flow-operator-bounds", "common_flow_operator_bounds",
                    "Uniform row bounds and the upper three-return box", boundsStatement,
                    "Emission bounds place 1-u in [3/5,2/3] and v in [1/3,2/5]. Positivity of the acquired integrals gives the two measure inequalities and completion bounds. The original endpoint word masses from FourthSegmentStoppedLaw give c_a z_a^3 below c_b z_b^3, with c_b=9/25 and z_b=6/25. The full p box therefore bounds the third L iterate of g. These are conditional integrals; no assertion bounds individual sampled path products."),
                Node("common-flow-conull-core", "common_flow_conull_core",
                    "A closed conull realization", coreStatement,
                    "PSet is Set(PDescriptor) and BSet is Set(BDescriptor); Member is set membership, and BRow and ARow are the original acquired kernel rows. The predicate goodP(F,Q) conjoins the full normalized B residual equality, the full p endpoint box, both entire coordinate iteration formulas, the completion integral, 9/25 <= g <= 4/9, and iterate(L,g,3,Q) <= (9/25)(6/25)^3. The predicate goodB(F,W) conjoins the full normalized A residual equality and the full suspended endpoint box. The measurable sets P and S have full nuP and nuB measure and satisfy these predicates pointwise. Every Q in P has B(Q)-almost every successor in S, and every W in S has A(W)-almost every successor in P. Starting from measurable hulls of the null exceptions, successive sets exclude positive-probability predecessors. The two unweighted margin identities keep every exclusion null. Their countable intersections are closed under both original kernels; no transition-closure hypothesis is imposed."),
                Node("common-flow-normalized-third-step", "common_flow_normalized_third_step",
                    "Normalized third return bound", All(Ae(mu, q, Le(normalized, cb)), ("F", "CommonFlow")),
                    "normalizedIterate(F,f,n,Q) is endpointRate⁻¹ raised to n times iterate(L,f,n,Q). The theorem transports the full p endpoint-box inequality at depth three through the exact scalar normalization endpointRate=6/25; it retains the original arbitrary Borel descriptor and acquired L operator."),
                Node("common-flow-normalized-iterate-succ", "normalizedIterate_succ",
                    "Normalized action advances one return", normalizedStep,
                    "The scalar endpoint normalization commutes with one L integration. The measurable iterate witness is discharged from the same Borel kernel, and no new state or transition is introduced."),
                Node("common-flow-normalized-action-add", "normalizedAction_add",
                    "Normalized action preserves nonnegative addition", actionAdd,
                    "Kernel integration and endpoint scaling preserve addition for the measurable first summand. This is the linearity input needed when the finite-block average is expanded; it does not assert a Jensen or localization conclusion."),
                Node("common-flow-normalized-action-average", "normalizedAction_threeStepAverage",
                    "Normalized action of the finite-block average", averageAction,
                    "The acquired normalized action sends the three-step average to the corresponding three successive normalized iterates. This is an exact finite algebraic bridge for the later localization argument; no fixed point, killing, or limit is claimed."))));
    }

    private static DocumentBlock.Describe Node(string id, string declaration, string title,
        Formula statement, string prose) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula Equal(Formula a, Formula b) => Seq(a, Eq, b);
    private static Formula Le(Formula a, Formula b) => Seq(a, Leq, b);
    private static Formula Sub(Formula a, Formula b) => Seq(a, Minus, b);
    private static Formula Times(Formula a, Formula b) => Multiply(a, b);
    private static Formula Fraction(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, Formula b) => Seq(Grp(a), Caret, Grp(b));
    private static Formula Ae(Formula mu, Formula x, Formula body) => Call("AE", mu, x, body);
    private static Formula And(Formula a, Formula b) => Seq(Open, a, Close, Land, Open, b, Close);
    private static Formula Imp(Formula a, Formula b) => Seq(Open, a, Close, Rightarrow, Open, b, Close);
    private static Formula ThereExists(Formula body, params (string Name, string Type)[] xs)
    {
        for (var i = xs.Length - 1; i >= 0; i--)
            body = Seq(Exists, Sp, F.Id(xs[i].Name), Colon, Sp, F.Id(xs[i].Type), Comma, Sp, body);
        return body;
    }
    private static Formula All(Formula body, params (string Name, string Type)[] xs)
    {
        for (var i = xs.Length - 1; i >= 0; i--)
            body = Seq(Forall, Sp, F.Id(xs[i].Name), Colon, Sp, F.Id(xs[i].Type), Comma, Sp, body);
        return body;
    }
}

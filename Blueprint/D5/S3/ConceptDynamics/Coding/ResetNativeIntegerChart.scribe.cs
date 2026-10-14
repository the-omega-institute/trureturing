using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class ResetNativeIntegerChartDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/ResetNativeIntegerChart.";
    private static Formula I(string name) => F.Id(name);
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Scope(Formula body) => All(body,
        B("q", I("Nat")), B("hq", Call("NatPositive", I("q"))));
    private static Formula Q => Call("QF", I("q"));
    private static Formula N => Call("Native", I("q"));
    private static Formula V => Call("VertexModule", I("Sign"), I("q"));
    private static Formula E => Call("resetNativeEquiv", I("q"), I("hq"));
    private static Formula Phi(Formula b) => Call("nativeIntEquiv", I("q"), I("hq"), b);
    private static Formula PhiInv(Formula x) => Call("apply", Call("inverse",
        Call("nativeIntEquiv", I("q"), I("hq"))), x);
    private static Formula Poly(Formula b) => Call("nativePolynomialEquiv", I("q"), I("hq"), b);
    private static Formula FP(Formula p) => Call("fp", I("q"), p);
    private static Formula Theta => Call("resetTheta", I("q"));
    private static Formula U => Call("groupAction", Call("resetMatrix", I("q")), Call("ofAdd", I("true")));
    private static Formula Stage(Formula n, Formula v) => Call("nativeStage", I("q"), n, v);
    private static Formula Apply(Formula f, Formula x) => Call("apply", f, x);
    private static Formula Scale(Formula z, Formula x) => Call("integerScale", z, x);
    private static Formula Eta(Formula x) => Call("eta", I("q"), I("hq"), x);
    private static Formula Arithmetic(Formula x) => Call("arithmeticChart", I("q"), x);
    private static Formula Square(Formula x) => Call("nativeSquare", I("q"), x);
    private static Formula Time => Call("targetTime", Call("mod", I("q"), Num(4)));
    private static Formula Label => Call("targetLabel", Call("mod", I("q"), Num(4)));
    private static Formula Eval(Formula p) => Call("integerPolynomialEval", p, Time);
    private static Formula Quotient(Formula x) => Call("nativeArithmeticEquiv", I("q"), I("hq"), x);

    private static Formula StageB => Call("ringEquiv", I("q"), Call("pp", I("q"),
        Call("coordinatePolynomial", I("resetLabel"), I("q"),
            Apply(Call("power", Call("resetInverse", I("q"), I("hq")), I("n")), I("v")))));

    private static Formula UnitGeneration()
    {
        Formula residue = Call("mod", I("q"), Num(4));
        Formula shift = Call("unitShift", Call("ResetGraph", I("q")));
        Formula unitPower = Equal(Call("power", Call("targetTimeUnit", residue), I("n")), I("u"));
        Formula shiftValue = Equal(Eta(Apply(Call("rho", I("q"), I("hq"),
            Call("power", shift, I("n"))), Call("generator", I("q"), I("hq")))),
            Call("unitValue", I("u")));
        return All(new Formula.BindMany(FormulaQuantifier.Exists, [B("n", I("Nat"))],
            And(Call("less", I("n"), Call("targetBound", residue)), And(unitPower, shiftValue))),
            B("u", Call("Units", Call("Target", residue))));
    }

    private static Formula ArithmeticStatement()
    {
        Formula[] clauses = [
            All(Equal(Square(Phi(I("b"))), Phi(Call("multiply", FP(I("H")), I("b")))), B("b", Q)),
            All(new Formula.Logic(Equal(Eta(I("x")), Num(0)), FormulaLogicOperator.Iff,
                new Formula.BindMany(FormulaQuantifier.Exists, [B("y", N)], Equal(Square(I("y")), I("x")))), B("x", N)),
            Call("Surjective", Call("eta", I("q"), I("hq"))),
            All(Equal(Quotient(Call("mkQ", Call("range", Call("nativeSquare", I("q"))), I("x"))), Eta(I("x"))), B("x", N)),
            All(Equal(Quotient(Call("add", I("x"), I("y"))),
                Call("add", Quotient(I("x")), Quotient(I("y")))),
                B("x", Call("NativeSquare", I("q"))), B("y", Call("NativeSquare", I("q")))),
            Equal(Eta(Call("generator", I("q"), I("hq"))), Num(1)),
            All(Equal(Eta(Apply(Call("aeval", Theta, I("p")), I("x"))),
                Call("multiply", Eval(I("p")), Eta(I("x")))), B("p", I("IntPolynomial")), B("x", N)),
            All(Equal(Eta(Apply(Theta, I("x"))), Call("multiply", Time, Eta(I("x")))), B("x", N)),
            All(Equal(Eta(Apply(U, I("x"))), Call("multiply", Label, Eta(I("x")))), B("x", N)),
            All(Equal(Eta(Stage(I("n"), I("v"))), Arithmetic(Call("bProjection", I("q"), StageB))),
                B("n", I("Nat")), B("v", V)),
            All(Equal(Arithmetic(Call("squarePolynomial", I("q"), I("p"))), Eval(I("p"))), B("p", I("IntPolynomial"))),
            Equal(Call("joint", I("q")), Call("idealSup",
                Call("principalIdeal", Call("residueF", Call("mod", I("q"), Num(4)))), Call("principalIdeal", I("H")))),
            UnitGeneration()
        ];
        Formula body = clauses[^1];
        for (int j = clauses.Length - 2; j >= 0; j--) body = And(clauses[j], body);
        return Scope(body);
    }

    private static Formula Presentation()
    {
        Formula[] clauses = [
            Equal(Phi(Num(1)), Stage(Num(0), Call("e0", I("q"), I("hq")))),
            All(Equal(Phi(Call("multiply", FP(I("X")), I("b"))), Apply(Theta, Phi(I("b")))), B("b", Q)),
            All(Equal(Phi(Call("multiply", FP(I("p")), I("b"))),
                Apply(Call("aeval", Theta, I("p")), Phi(I("b")))), B("p", I("IntPolynomial")), B("b", Q)),
            All(Equal(Phi(Scale(I("z"), I("b"))), Scale(I("z"), Phi(I("b")))), B("z", I("Int")), B("b", Q)),
            All(Equal(Poly(I("b")), Call("AEvalOf", Theta, Phi(I("b")))), B("b", Q)),
            All(Equal(PhiInv(Stage(I("n"), I("v"))), StageB), B("n", I("Nat")), B("v", V)),
            All(Equal(Apply(E, Apply(U, I("x"))),
                Apply(Call("leftTranslation", Call("ofAdd", I("true"))), Apply(E, I("x")))), B("x", N)),
            Equal(U, Call("aeval", Theta, Call("W", I("q"))))
        ];
        Formula body = clauses[^1];
        for (int j = clauses.Length - 2; j >= 0; j--) body = And(clauses[j], body);
        return Scope(body);
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original native square-time quotient has four oriented integral arithmetic ring charts, a canonical projection, and bounded generation of every target unit by actual forward shifts.",
        H("Original native square-time arithmetic"),
        Blocks(
            Paragraph(Text("For every q>0, including q=1, R is literally MonoidAlgebra Int Sign, "
                + "Sign is Multiplicative Bool, resetLabel is single (ofAdd true) 1, and QF(q) "
                + "is Int[X]/(F(q)) from ResetSignIntegerCyclic. Native(q) is the ORIGINAL "
                + "DimensionGroup(resetMatrix q), with the canonical AddCommGroup.toIntModule "
                + "instance used by the full rho owner. nativeStage is the original DirectLimit.of. "
                + "Theta is original forward resetTheta; U is actual groupAction(resetMatrix q)(ofAdd true). "
                + "These operators are distinguished until concrete coefficient naturality is proved.")),
            Describe.Lean(DescribeId.Create("native-integral-chart"), DeclarationHandle.Create(Prefix + "nativeIntEquiv"),
                H("An actual integral equivalence"),
                StatementSource.FromAuthor(Disp(Scope(Call("hasType", Call("nativeIntEquiv", I("q"), I("hq")),
                    Call("IntLinearEquiv", Q, N))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The map is the composite of ringEquiv.symm, the existing "
                    + "FiniteCompanionCyclicModule.cyclicEquiv at R/resetLabel, removal of its AEval wrapper, "
                    + "and resetNativeEquiv.symm. Additive equivalences are made integer-linear by "
                    + "toAddEquiv.toIntLinearEquiv. The inverse native map is actual stage zero; "
                    + "no rank or cardinality argument is used."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("native-polynomial-chart"), DeclarationHandle.Create(Prefix + "nativePolynomialEquiv"),
                H("The genuine polynomial module chart"),
                StatementSource.FromAuthor(Disp(Scope(Call("hasType", Call("nativePolynomialEquiv", I("q"), I("hq")),
                    Call("PolynomialLinearEquiv", Q, Call("AEval", Theta)))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Only after Phi([X]b)=Theta(Phi(b)) is proved does "
                    + "LinearEquiv.ofAEval promote Phi inverse from the native group to QF. "
                    + "Its inverse is QF equivalent over Int[X] to Module.AEval'(Theta). "
                    + "AEvalOf is the canonical integer-linear identification with that type synonym."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("native-presentation"), DeclarationHandle.Create(Prefix + "native_presentation"),
                H("Normalized time, stage and coefficient laws"), StatementSource.FromAuthor(Disp(Presentation())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("NatPositive(q) means 0<q; IntPolynomial is Polynomial Int. multiply "
                        + "is quotient-ring multiplication, integerScale is integer module action, inverse "
                        + "is the linear-equivalence inverse, and power is composition power of an "
                        + "endomorphism. The theorem supplies normalization at original stage-zero e0, "
                        + "forward X intertwining, all exact polynomial and integer scalar laws, the "
                        + "underlying map of the polynomial chart, the explicit inverse coordinate "
                        + "polynomial at every stage, concrete native Sign naturality and U=aeval(Theta)(W).")),
                    Paragraph(Text("At q=n+1, the original ResetSquareIntegralDefect.time_eq supplies the finite time bridge. Thus the existing coefficient-ring time "
                        + "is the original RIGHT-row forward transition, also when n=0. The ring bridge's "
                        + "X image and cyclicEquiv polynomial-linearity give the finite X law; "
                        + "resetNativeEquiv_theta gives the original native law. The promoted equivalence "
                        + "then supplies every polynomial action exactly. cyclic_presentation supplies "
                        + "the inverse coordinatePolynomial. resetNativeEquiv_stage supplies resetInverse "
                        + "raised to n: later stages use inverse time while X still denotes forward time.")),
                    Paragraph(Text("For concrete coefficient naturality, exhaust an arbitrary native x "
                        + "using resetNativeEquiv.symm_apply_apply. Its actual inverse is stage-zero "
                        + "DirectLimit.of. groupAction unfolds to DirectLimit.map, whose map_apply_of "
                        + "sends that representative to the stage-zero leftTranslation of its row. "
                        + "resetNativeEquiv_stage at zero closes the equality, without re-proving "
                        + "inverse-power commutation. In the literal commutative Sign algebra, left "
                        + "translation by ofAdd true equals RIGHT multiplication by resetLabel. "
                        + "cyclicEquiv's C(resetLabel) action and ringEquiv's C(resetLabel) "
                        + "image [W] therefore transfer to the actual native U. Surjectivity of Phi "
                        + "and its polynomial law yield the endomorphism identity U=aeval(Theta)(W). "
                        + "Only integer linearity of resetNativeEquiv is used."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("oriented-arithmetic-chart"), DeclarationHandle.Create(Prefix + "arithmeticChart"),
                H("Both inverse oriented ring maps"), StatementSource.FromAuthor(Disp(All(
                    Call("hasType", Call("arithmeticChart", I("q")),
                        Call("RingEquiv", Call("SquareRing", I("q")), Call("Target", Call("mod", I("q"), Num(4))))),
                    B("q", I("Nat"))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The chart selects the actual zero, binary, five or Gaussian RingEquiv according to q mod 4. "
                    + "Each has actual forward and reverse maps, left and right inverse laws, multiplicativity and one. "
                    + "Its polynomial law fixes the forward-time orientation."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("native-arithmetic-readout"), DeclarationHandle.Create(Prefix + "eta"),
                H("Canonical native arithmetic projection"), StatementSource.FromAuthor(Disp(Scope(
                    Call("hasType", Call("eta", I("q"), I("hq")),
                        Call("IntLinearMap", N, Call("Target", Call("mod", I("q"), Num(4)))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Eta is the actual native chart inverse followed by bProjection "
                    + "and arithmeticChart. Its kernel is the original nativeSquare range; eta(generator)=1 fixes scalar normalization."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("native-arithmetic-quotient"), DeclarationHandle.Create(Prefix + "nativeArithmeticEquiv"),
                H("Ring structure transported through the proved additive quotient"),
                StatementSource.FromAuthor(Disp(Scope(Call("hasType", Call("nativeArithmeticEquiv", I("q"), I("hq")),
                    Call("RingEquivWithTransportedStructure", Call("NativeSquare", I("q")),
                        Call("Target", Call("mod", I("q"), Num(4))), Call("nativeSquareRing", I("q"), I("hq"))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("NativeSquare remains the original quotient by range(id+Theta^2). "
                    + "The named nativeSquareRing transports its ring structure through nativeSquareEquiv. "
                    + "The canonical mkQ formula and original addition law are part of native_square_arithmetic."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("native-square-arithmetic"), DeclarationHandle.Create(Prefix + "native_square_arithmetic"),
                H("The canonical native quotient and its arithmetic"), StatementSource.FromAuthor(Disp(ArithmeticStatement())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("H is X^2+1 and joint(q) is the sum of the principal ideals generated by F(q) and H. "
                        + "SquareRing(q) is Int[X]/joint(q). bProjection uses DoubleQuot.quotQuotEquivQuotSup and the second "
                        + "canonical quotient map; Ideal.map_span identifies its second ideal with the principal ideal generated by [H]. "
                        + "The original nativeSquare is id+Theta^2. A quotient-kernel witness b yields the actual native preimage Phi(b); "
                        + "a native preimage y yields the coefficient Phi inverse(y). These explicit witnesses identify the canonical "
                        + "projection kernel with the original range alone. nativeSquareEquiv is the resulting integer-linear quotient "
                        + "equivalence. nativeSquareRing explicitly transports multiplication and one through that equivalence; "
                        + "nativeArithmeticEquiv then gives the actual inverse ring chart. The theorem also checks the original quotient addition.")),
                    Paragraph(Text("In Int[X]/(H), t^2=-1 and t^4=1. The four-term geometric sum is zero. Periodicity reduces "
                        + "S(q) to S(q mod 4), without division by X-1. Consequently F has residues 1,-2,1-2X,0 and W has residues "
                        + "1-X,2+X,2X,-1. Both ideal inclusions for residue two use the integral certificates "
                        + "5=4H+(2X+1)(1-2X), X-3=-3(1-2X)-5X, 1-2X=-2(X-3)-5, and H=(X-3)(X+3)+10.")),
                    Paragraph(Text("Target(r), time and label are respectively ZMod(1),1,1 for r=0; literal "
                        + "MonoidAlgebra(ZMod(2),Sign),single oddTau 1,single oddTau 1 for r=1; ZMod(5),3,1 for r=2; "
                        + "GaussianInt,i,-1 for r=3. The binary inverse uses actual coefficient reduction and liftNCRingHom. "
                        + "Its two inverse equations are checked on integer coefficients and both Sign elements. The Gaussian inverse "
                        + "uses Zsqrtd.lift and both inverse equations are checked on i and polynomial generators. The five-chart "
                        + "reuses quotientSpanCXSubCAlgEquiv and Int.quotientSpanNatEquivZMod. The zero chart has both unique maps. "
                        + "RingEquiv preserves one, integer scalars, multiplication and inverse maps; integerPolynomialEval means eval2 "
                        + "with the integer cast and the displayed forward-time element. principalIdeal and idealSup denote literal "
                        + "integral ideals. The stage equation keeps the original inverse-time power before the coordinate polynomial.")),
                    Paragraph(Text("The uniform integral period-four reduction identifies the joint ideal in every residue class. "
                        + "These ideal equalities determine the four arithmeticChart branches and hence the native projection eta "
                        + "and quotient equivalence nativeArithmeticEquiv. The normalized native chart connects the original "
                        + "time and coefficient operators to these integral polynomial quotients.")),
                    Paragraph(Text("Every target unit is reached by the actual numbered-history shift at the normalized generator. "
                        + "The exponent bounds targetBound are 1,2,4,4 in residue order. Units are respectively {1}, "
                        + "{1,tau}, {1,3,4,2}, and {1,i,-1,-i}. In the binary group algebra, expansion in the two literal "
                        + "coefficients and the augmentation ring map force a unit's coefficient sum to be one. The two "
                        + "coefficient possibilities give exactly 1 or tau. For Gaussian units, the standard norm-one "
                        + "criterion gives a^2+b^2=1. Integer bounds restrict each coefficient to -1,0,1 and yield the four "
                        + "displayed possibilities. In ZMod(5) each unit has one of the four explicit powers of 3. "
                        + "The actual rho_unitShift equation, map_pow, and the polynomial action law transport these powers "
                        + "to the original native action. unitValue denotes the underlying ring element of a unit; the final "
                        + "power is the group power of the actual history shift. targetTimeUnit has value targetTime and literal "
                        + "inverse 1,tau,2,-i in residue order, and every target unit equals its bounded group power."))), DescribeRole.Theorem),
            Paragraph(Text("Application to the full native action. Write N=DimensionGroup(resetMatrix q), "
                + "Theta=resetTheta q, e=generator q hq and Phi=nativeIntEquiv q hq. The ring B is literally "
                + "Int[X]/(F(q)); its polynomial scalar extension is fp:Int[X]->B, with x=fp(X). N has its "
                + "integer module structure. Put J=id+Theta^2, H=range(J), Q=N/H and pi=H.mkQ. Every product on "
                + "Q in this application is transported through nativeSquareEquiv; no product on N is used.")),
            Paragraph(Text("Let C be the actual subring centralizer of Theta in End_Int(N), with (f*g)(v)=f(g(v)). "
                + "Multiplication on B defines Psi(b)(Phi(c))=Phi(b*c). This is an oriented ring equivalence "
                + "B->C, whose inverse is f->Phi.inverse(f(e)). Indeed LinearMap.ofAEval promotes a commuting "
                + "integer-linear map to polynomial linearity. The surjectivity of Int[X]->B then makes it "
                + "B-linear, so its value on 1 determines it on every vector. The chart fixes Psi(x)=Theta and "
                + "Psi(1+x^2)=J. These constructions use the existing native_presentation and the standard "
                + "polynomial-module and conjugation universal properties.")),
            Paragraph(Text("For an actual h in ResetFullAut q, membership in fullAutSubgroup says h*shift=shift*h. Apply "
                + "multiplicativity of the actual full representation rho and rho_unitShift to obtain "
                + "rho(h)*Theta=Theta*rho(h). The inverse commutes as well, by the unit inverse commutation "
                + "law. Thus rho(h) is a unit of C. Define chi_B(h)=Psi.inverse(rho(h)) as a B-unit. It "
                + "preserves one, multiplication and inverses and satisfies "
                + "rho(h)(v)=Phi(chi_B(h)*Phi.inverse(v)) for every original native v. Its value is "
                + "Phi.inverse(rho(h)(e)); the actual forward shift has value x. Evaluation at e proves "
                + "uniqueness of the unit with this action law. Surjectivity of chi_B is not asserted.")),
            Paragraph(Text("Form the literal second quotient A=B/(1+x^2). Its canonical identification with "
                + "SquareRing(q) is the double-quotient equivalence, using Ideal.map_span to identify the "
                + "mapped square ideal. Composing with arithmeticChart identifies A with the displayed "
                + "arithmetic target. Define chi_A by applying the canonical quotient B->A to chi_B, including "
                + "its inverse. If eta_A is the corresponding native projection, then "
                + "eta_A(rho(h)(v))=chi_A(h)*eta_A(v) for every v, eta_A(e)=1, and chi_A(h)=eta_A(rho(h)(e)). "
                + "This proves uniqueness from the normalized generator and gives the exact induced action on "
                + "the original quotient.")),
            Paragraph(Text("The canonical quotient time is Theta_bar=H.mapQ(H,Theta). Let C_bar be its actual "
                + "centralizer subring in End_Int(Q). For f in C, the equality f*J=J*f preserves H. Define "
                + "res(f)=H.mapQ(H,f). It satisfies res(f)(pi(v))=pi(f(v)), res(1)=1, res(f+g)=res(f)+res(g), "
                + "and res(f*g)=res(f)*res(g), in the stated composition order. These equations also prove that "
                + "the image commutes with Theta_bar. Thus res:C->C_bar is an actual unital ring homomorphism "
                + "of End centralizers.")),
            Paragraph(Text("The native quotient chart identifies C_bar with A by the same polynomial-linearity argument. "
                + "If Psi_bar is this scalar equivalence, then res(Psi(b))=Psi_bar(b mod (1+x^2)). Every scalar "
                + "in A has a representative in B, so res is onto. Its kernel is exactly the image of L->J*L: "
                + "res(f)=0 if and only if there exists L in C with f=J*L. The reverse witness comes from "
                + "membership in the principal ideal generated by 1+x^2 in B and is transported by Psi. This "
                + "argument uses neither cancellation by J nor lifting of arbitrary units.")),
            Paragraph(Text("Let d be 1,2,4,4 in residue order. The accepted unit classification gives exhaustion by the "
                + "forward-time unit, and its exact arithmetic order is d: tau has order two in the binary "
                + "ring, 3 has order four modulo five, and i has order four in the Gaussian ring. The zero-ring "
                + "unit has order one. With these arithmetic hypotheses in place, pow_injOn_Iio_orderOf gives a "
                + "unique exponent j with 0<=j<d for every target unit. Every A-unit has the actual history "
                + "shift^j as a chi_A preimage. In particular chi_A is onto.")),
            Paragraph(Text("Every integer-linear automorphism of Q commuting with Theta_bar is exactly the action "
                + "induced by one of these actual shift powers, with unique j in that interval. The induced "
                + "actual forward shift has exact order d. For every integer-linear automorphism f of N "
                + "commuting with Theta, there is likewise a unique j in that interval such that f-Theta^j=J*L "
                + "for some L in C. This applies to every actual rho(h). The phase is unique; the correction "
                + "factor L is only existential here. Its uniqueness is not asserted, including when q mod 4 is "
                + "three.")),
            Paragraph(Text("The phase equation is equivalent both to pi(f(v))=pi(Theta^j(v)) for every native v and to "
                + "eta(f(e))=targetTime^j at the normalized generator. At phase zero these give the exact "
                + "all-vector and generator criteria for ker(chi_A). The first isomorphism theorem gives "
                + "FullAut/ker(chi_A) isomorphic to A-units. Composing with zmodMulEquivOfGenerator gives the "
                + "oriented equivalence with Multiplicative(ZMod d), carrying the class of the actual forward "
                + "shift to 1 modulo d.")),
            Paragraph(Text("For q mod 4 equal to two, the canonical identification of eta with ZMod(5) is the literal "
                + "clock resetFiveClock(resetNativeEquiv(v)). Its weights are exactly 1,2,0,4 in original "
                + "vertex order, applied to the sum of the two integer Sign coefficients. The kernel equality "
                + "reset_five_clock_image and the value one at the actual e0 fix the normalization. "
                + "RingHom.ext_zmod makes the prime-ring identification unique. Original forward Theta "
                + "multiplies this readout by 3. A native stage-n row is read after n inverse transitions, so "
                + "its clock is 2^n times the clock of the row. These are the original forward and stage "
                + "orientations.")),
            Paragraph(Text("At the same residue, q is even and the actual evenAut has rho(evenAut)=id+Theta by rho_even. "
                + "Therefore its clock action on every vector is multiplication by 4=1+3. Since 3^2=4 modulo "
                + "five, its unique phase is two, and rho(evenAut)-Theta^2=J*L for some actual native commuting "
                + "endomorphism L. The action and phase statements retain the entire original history domain; "
                + "no inertness or Sign-equivariance premise is imposed.")),
            Paragraph(Text("The chart is integral and includes q=1 directly. It assumes no parity, "
                + "q>=2, field, nontriviality, rational Sign splitting, native R-linearity, cone preservation "
                + "or history Sign-equivariance. The application above uses native_presentation, native_square_arithmetic, "
                + "rho_unitShift, rho_even, reset_five_clock_image and the indicated standard universal properties. "
                + "It does not require a nontrivial square quotient or injectivity of J. This is a repository synthesis of existing results "
                + "and standard polynomial/module universal properties, without a literature novelty claim.")))));
}

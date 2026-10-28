using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class PositivePauliClockOrderDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Dynamics/PositivePauliClockOrder.";
    private static Formula V => F.Id("v");
    private static Formula W => F.Id("w");
    private static Formula T => F.Id("t");
    private static Formula Tp => Seq(T, Underscore, Grp(Plus));
    private static Formula Tm => Seq(T, Underscore, Grp(Minus));
    private static Formula One => F.Id("I");
    private static Formula X => F.Id("X");
    private static Formula Z => F.Id("Z");
    private static Formula Imag => F.Id("i");
    private static Formula Half => Fraction(D(1), D(2));
    private static Formula NegOne => Seq(Minus, D(1));
    private static Formula R(Formula v) => Call("R", v);
    private static Formula N(Formula v) => Call("N", v);
    private static Formula Pulse(Formula v, Formula t) => Call("V", v, W, t);
    private static Formula Chi(Formula v, Formula t) => Call("chi", v, W, t);
    private static Formula Channel(Formula v, Formula t, Formula rho) => Call("Phi", v, W, t, rho);
    private static Formula GammaAt(Formula tp, Formula tm) => Call("gamma", W, tp, tm);
    private static Formula Control(Formula tp, Formula tm) => Call("rhoctrl", W, tp, tm);
    private static Formula Holo(Formula tp, Formula tm) => Call("H", W, tp, tm);
    private static Formula StarOf(Formula x) => Seq(Open, x, Close, Caret, Grp(Star));
    private static Formula Square(Formula x) => Seq(Open, x, Close, Caret, Grp(D(2)));
    private static Formula Fraction(Formula x, Formula y) => Seq(Frac, Grp(x), Grp(y));
    private static Formula Mul(params Formula[] xs) => Join(Sp, xs);
    private static Formula Equal(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    private static Formula And(params Formula[] xs) => Join(Seq(Sp, Land, RowBreak, Grp()),
        Array.ConvertAll(xs, x => Seq(Open, x, Close)));
    private static Formula Join(Formula separator, params Formula[] xs)
    {
        var output = new List<Formula>();
        foreach (var x in xs)
        {
            if (output.Count > 0) output.Add(separator);
            output.Add(x);
        }
        return Seq([.. output]);
    }
    private static Formula ForReal(Formula variables, Formula body) =>
        Seq(Forall, Sp, variables, Sp, InMacro, Sp, F.Id("R"), Comma, Sp, body);
    private static Formula Domain =>
        Seq(Bar, V, Bar, Sp, Lt, Sp, Sqrt, Grp(Fraction(D(3), D(2))));
    private static Formula Implies(Formula premise, Formula body) =>
        Seq(Open, premise, Close, Sp, Rightarrow, Sp, body);
    private static Formula Matrix2(Formula a, Formula b, Formula c, Formula d) => Seq(
        Begin, Grp(F.Id("pmatrix")), a, Amp, b, RowBreak, c, Amp, d,
        End, Grp(F.Id("pmatrix")));
    private static Formula Trace(Formula x) => Call("tr", x);
    private static Formula TrEnv(Formula x) => Call("trG", x);
    private static Formula Tensor(Formula x, Formula y) => Call("kron", x, y);
    private static Formula Block(Formula q, Formula p) => Call("B", q, p);
    private static Formula Phase(Formula t) => Call("exp", Mul(Seq(Minus, Imag), W, t));
    private static Formula Cos(Formula t) => Call("cos", Fraction(Mul(W, t), D(2)));
    private static Formula SinAt(Formula t) => Call("sin", Fraction(Mul(W, t), D(2)));
    private static Formula Polynomial(Formula tp, Formula tm) =>
        Seq(D(1), Minus, Mul(D(2), Square(SinAt(tp)), Square(SinAt(tm))));
    private static Formula Marginal(Formula g) => Mul(Half, Matrix2(D(1), StarOf(g), g, D(1)));
    private static Formula MinusState => Mul(Half, Matrix2(D(1), NegOne, NegOne, D(1)));
    private static Formula P => Call("P", W, Tp, Tm);
    private static Formula Q => Call("Q", W, Tp, Tm);

    private static DocumentBlock Theorem(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-')), DeclarationHandle.Create(Owner + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(DefinitionDsl.Text(prose))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The positive two-dimensional clock has equal isolated reduced channels and a nontrivial implemented order overlap.",
        H("Positive Pauli Clock Order"),
        Blocks(
            Paragraph(DefinitionDsl.Text(
                "This model instantiates QUANTUM-REALITY sections 101, 103 and theorem 107.2. "
                + "The overlap convention is section 85: branch zero implements Q and branch one P. "
                + "All velocities, frequencies and durations below are real. The source experiment takes positive frequency; "
                + "the algebraic identities also hold for arbitrary real frequency. Durations have no sign restriction.")),
            new DocumentBlock.DisplayFormula(Disp(And(
                Equal(Call("HG"), Seq(F.Id("C"), Caret, Grp(D(2)))),
                Equal(X, Matrix2(D(0), D(1), D(1), D(0))),
                Equal(Z, Matrix2(D(1), D(0), D(0), NegOne)),
                Equal(R(V), Seq(Open, Fraction(D(3),D(2)), Minus, Fraction(Square(V),D(4)), Close, One,
                    Plus, Mul(Fraction(Seq(D(1),Minus,V),D(2)),X), Plus,
                    Mul(Fraction(Seq(D(1),Plus,V),D(2)),Z))),
                Equal(N(V), Call("CFCsqrt",R(V))),
                Equal(SigmaLower,Mul(Half,One))))),
            new DocumentBlock.DisplayFormula(Disp(And(
                Equal(F.Id("A"),Seq(Mul(Fraction(D(3),D(2)),One),Plus,Mul(Half,Open,X,Plus,Z,Close))),
                Equal(F.Id("Bcoeff"),Mul(Fraction(D(1),D(4)),Open,Z,Minus,X,Close)),
                Equal(F.Id("Ccoeff"),Mul(Fraction(D(1),D(4)),One)),
                Equal(Pulse(V,T),Call("exp",Mul(Seq(Minus,Imag),W,T,N(V)))),
                Equal(Block(Q,P),Seq(Tensor(Call("E",D(0),D(0)),Q),Plus,Tensor(Call("E",D(1),D(1)),P)))))),
            new DocumentBlock.DisplayFormula(Disp(And(
                Equal(Call("U",V,W,T),Block(One,Pulse(V,T))),
                Equal(Channel(V,T,Rho),TrEnv(Mul(Call("U",V,W,T),Tensor(Rho,SigmaLower),StarOf(Call("U",V,W,T))))),
                Equal(Chi(V,T),Trace(Mul(SigmaLower,Pulse(V,T)))),
                Equal(P,Mul(Pulse(NegOne,Tm),Pulse(D(1),Tp))),
                Equal(Q,Mul(Pulse(D(1),Tp),Pulse(NegOne,Tm))),
                Equal(Holo(Tp,Tm),Mul(StarOf(Q),P)),
                Equal(GammaAt(Tp,Tm),Trace(Mul(SigmaLower,Holo(Tp,Tm)))),
                Equal(Call("rhoplus"),Mul(Half,Matrix2(D(1),D(1),D(1),D(1)))),
                Equal(Control(Tp,Tm),TrEnv(Mul(Block(Q,P),Tensor(Call("rhoplus"),SigmaLower),StarOf(Block(Q,P)))))))),
            Theorem("positive_clock_coefficients", "Standing coefficient witnesses", Coefficients(),
                "The Hermitian coefficients and the positive constants one half and one quarter are concrete derived data."),
            Theorem("positive_clock_model", "Positivity on the whole source interval",
                ForReal(V,Implies(Domain,Call("PosDef",R(V)))),
                "The determinant estimate is strict on the entire open interval. The model is not restricted to its two pulse directions."),
            Theorem("special_directions_mem", "Both pulse directions are admissible",
                And(Seq(Bar,D(1),Bar,Lt,Sqrt,Grp(Fraction(D(3),D(2)))),
                    Seq(Bar,NegOne,Bar,Lt,Sqrt,Grp(Fraction(D(3),D(2))))),
                "Both specified velocities lie strictly inside the source domain."),
            Theorem("positive_clock_speed", "The positive root is invertible",
                ForReal(V,Implies(Domain,Call("PosDef",N(V)))),
                "The speed is the CFC square root of the response. Response positivity proves root positivity and invertibility."),
            Theorem("positive_clock_special_roots", "Exact special positive roots", Roots(),
                "Positivity and the exact squares identify the candidates uniquely with the positive functional-calculus roots."),
            Describe.Lean(DescribeId.Create("sigma-pos-def"),
                DeclarationHandle.Create(Owner + "sigma_posDef"),
                H("Strict positivity of the mixed state"),
                StatementSource.FromAuthor(Disp(new Formula.Apply(QualifiedName("Matrix.PosDef"),
                    [QualifiedName("D5.S3.Quantum.Dynamics.PositivePauliClockOrder.sigma")]))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text(
                    "The maximally mixed qubit matrix sigma is positive definite."))),
                DescribeRole.Theorem),
            Theorem("mixed_state_full_support", "Canonical maximally mixed state",
                And(Equal(Call("matrix",Call("mixedState")),SigmaLower),Call("Surjective",Call("mulVec",SigmaLower))),
                "mixedState inhabits the current Foundation density carrier, with positivity and trace one proved. Its matrix has full range, so the standing support is the identity."),
            Theorem("pulse_eq_exp", "Existing propagator and source exponential agree",
                ForReal(Join(Comma,V,W,T),Equal(Pulse(V,T),Call("exp",Mul(Seq(Minus,Imag),W,T,N(V))))),
                "pulse reuses hamiltonianPropagator with Hamiltonian omega times the actual positive root."),
            Theorem("clock_propagators", "Unitary structure propagation",
                ForReal(Join(Comma,V,W,T),Implies(Domain,Call("Unitary",Pulse(V,T)))),
                "The normalized generator is skew-adjoint. No additional free structure evolution is inserted."),
            Theorem("controlled_clock_evolution", "Implemented controlled clock evolution", JointEvolution(),
                "The joint operator is the source's controlled expression. Its excited-clock block acts by the actual structure propagator."),
            Theorem("controlled_unitary", "Unitary controlled qubit matrices", ControlledUnitaryFormula(),
                "For any two unitary complex qubit matrices Q and P, the controlled matrix is unitary. "
                + "The matrix is block diagonal with blocks Q and P, with both pair coordinates swapped. "
                + "Thus the first coordinate selects Q for 0 and P for 1, while the second coordinate carries their action."),
            Theorem("controlled_partial_trace", "Mixed controlled-block trace identity", MixedTrace(),
                "Q, P and rho are arbitrary complex two-dimensional matrices. branch(Q,P,0) is Q and branch(Q,P,1) is P. "
                + "The identity directly expands the mixed partial trace; no damping or Gram hypothesis is assumed."),
            Theorem("clock_reduced_entries", "All entries of the actual reduced channel", Entries(),
                "The raw matrix identity specializes to every canonical density state. The conjugate occurs in the upper off-diagonal entry."),
            Theorem("clock_pulse_special_directions", "Special propagators with their global phase", Pulses(),
                "Pinned Mathlib's map_exp applied to the two-coordinate algebra map and exp_diagonal evaluate the actual exponentials. No Hadamard result is copied or reproved."),
            Theorem("isolated_clock_coherence", "Equal isolated coherence functions", IsolatedCoherence(),
                "The maximally mixed structure state gives the same coherence for both directions at every real duration."),
            Theorem("isolated_clock_channels_equal", "Equal isolated reduced channels", IsolatedChannels(),
                "Equality quantifies over the current canonical density-state carrier and the actual partial-trace maps."),
            Theorem("pi_clock_pulses", "Actual pi-pulse operators", PiPulses(),
                "The pulse equation yields iZ and iX, including the global phase inherited from the positive roots."),
            Theorem("pi_clock_orders_anticommute", "Opposite pulse orders differ by sign",
                ForReal(Join(Comma,W,T),Implies(Equal(Mul(W,T),Pi),Anti())),
                "The exponential identities specialize the existing canonical Pauli anticommutation theorem."),
            Theorem("order_control_marginal", "Actual coherent order marginal",
                ForReal(Join(Comma,W,Tp,Tm),Equal(Control(Tp,Tm),Marginal(GammaAt(Tp,Tm)))),
                "The same structure register is retained through both pulses. Branch zero carries Q and branch one P; the structure is discarded only after the coherent comparison."),
            Theorem("order_interference_formula", "General-duration interference coefficient",
                ForReal(Join(Comma,W,Tp,Tm),Equal(GammaAt(Tp,Tm),Polynomial(Tp,Tm))),
                "With a equal to omega tPlus over two and b equal to omega tMinus over two, the independent operator trace evaluates to one minus twice sin(a) squared sin(b) squared."),
            Theorem("pi_order_relative_phase", "Relative pi phase in the implemented control",
                ForReal(Join(Comma,W,T),Implies(Equal(Mul(W,T),Pi),PiReadout())),
                "The actual relative operator is minus the identity, the trace overlap is minus one, and the control state has negative off-diagonal entries."),
            Paragraph(DefinitionDsl.Text(
                "For the classical comparison, each run has a fixed label lambda and real scalar rates nPlus(lambda), nMinus(lambda). "
                + "Both phases read that same label. Define zPlus and zMinus by the scalar exponential at their respective durations, "
                + "and c(lambda) as the conjugate of zPlus zMinus multiplied by zMinus zPlus.")),
            new DocumentBlock.DisplayFormula(Disp(And(
                Equal(Call("zplus",LambdaLower),Call("exp",Mul(Seq(Minus,Imag),W,Tp,Call("nplus",LambdaLower)))),
                Equal(Call("zminus",LambdaLower),Call("exp",Mul(Seq(Minus,Imag),W,Tm,Call("nminus",LambdaLower)))),
                Equal(Call("c",LambdaLower),Mul(StarOf(Mul(Call("zplus",LambdaLower),Call("zminus",LambdaLower))),
                    Call("zminus",LambdaLower),Call("zplus",LambdaLower)))))),
            Theorem("fixed_scalar_clock_order", "Fixed-label scalar order", ScalarOrder(),
                "These scalar phases commute and have unit modulus. The relative coefficient is one, so it cannot be minus one."),
            Theorem("averaged_fixed_scalar_clock_order", "Arbitrary probability averaging", Average(),
                "The measure is any probability measure on the label space. Rates need no measurability assumption for the relative coefficient, "
                + "which is pointwise constant before integration. Pointwise equal ordered amplitudes also have equal Bochner integrals. "
                + "Their equality alone would not exclude a sign, since both averaged amplitudes can vanish."),
            Theorem("positive_pauli_clock_order_separation", "Positive-frequency source experiment", Complete(),
                "For positive omega, pi over omega supplies an actual duration satisfying the pulse equation. "
                + "The combined assertion retains the positive model, canonical state, implemented joint evolution, isolated equality, "
                + "general-duration overlap and pi witness, together with the fixed scalar probability-average boundary."),
            Paragraph(DefinitionDsl.Text(
                "The exclusion concerns only fixed commuting scalar clocks. Time-varying classical backgrounds, other apparatus actions, "
                + "and path-dependent models require separate exclusion. The coherent comparison consumes the actual implemented operators; "
                + "isolated channel tables alone do not specify controlled implementations. The reference time is the calibrated protocol parameter. "
                + "The response coefficients are clock-response operators, not a claimed complete quantum spacetime metric.")))));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula QualifiedName(string name)
    {
        var items = new List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(Operatorname);
            items.Add(Grp(F.Id(part)));
        }
        return Seq([.. items]);
    }
    private static Formula ControlledUnitaryFormula()
    {
        Formula q = F.Id("Q"), p = F.Id("P");
        Formula bits = Call("Fin", D(2));
        Formula pairs = Seq(bits, Sp, Times, Sp, bits);
        Formula matrices = Call("Matrix", bits, bits, F.Id("Complex"));
        Formula jointMatrices = Call("Matrix", pairs, pairs, F.Id("Complex"));
        Formula diagonal = new Formula.Apply(QualifiedName("Matrix.blockDiagonal"),
            [Seq(Bang, OpenBracket, q, Comma, Sp, p, CloseBracket)]);
        Formula matrix = new Formula.Apply(QualifiedName("Matrix.submatrix"),
            [diagonal, QualifiedName("Prod.swap"), QualifiedName("Prod.swap")]);
        Formula Member(Formula value, Formula type) =>
            new Formula.Relation(value, FormulaRelationOperator.MemberOf, Call("unitary", type));
        Formula Imp(Formula left, Formula right) =>
            new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
        return new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("Q"), matrices,
            new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("P"), matrices,
                Imp(Member(q, matrices), Imp(Member(p, matrices), Member(matrix, jointMatrices)))));
    }

    private static Formula Coefficients() => And(
        Call("Hermitian",F.Id("A")),Call("Hermitian",F.Id("Bcoeff")),Call("Hermitian",F.Id("Ccoeff")),
        Seq(Mul(Half,One),Sp,Le,Sp,F.Id("A")),
        ForReal(V,Equal(R(V),Seq(F.Id("A"),Plus,Mul(D(2),V,F.Id("Bcoeff")),Minus,Mul(Square(V),F.Id("Ccoeff"))))),
        ForReal(Xi,Equal(Mul(Square(Xi),F.Id("Ccoeff")),Mul(Fraction(Square(Xi),D(4)),One))));
    private static Formula Root(Formula k) => Seq(One,Plus,Mul(Half,k));
    private static Formula Roots() => And(Equal(N(D(1)),Root(Z)),Equal(N(NegOne),Root(X)),
        Call("PosDef",Root(Z)),Call("PosDef",Root(X)),Equal(Square(Root(Z)),R(D(1))),Equal(Square(Root(X)),R(NegOne)));
    private static Formula JointEvolution() => ForReal(Join(Comma,V,W,T),Implies(Domain,And(
        Call("Unitary",Block(One,Pulse(V,T))),
        Equal(Block(One,Pulse(V,T)),Seq(Tensor(Call("E",D(0),D(0)),One),Plus,Tensor(Call("E",D(1),D(1)),Pulse(V,T)))),
        Seq(Forall,Sp,F.Id("a"),Comma,F.Id("b"),InMacro,Call("Fin",D(2)),Comma,
            Equal(Call("entry",Block(One,Pulse(V,T)),Call("pair",D(1),F.Id("a")),Call("pair",D(1),F.Id("b"))),
                Call("entry",Pulse(V,T),F.Id("a"),F.Id("b")))))));
    private static Formula MixedTrace() => Seq(Forall,Sp,F.Id("Q"),Comma,F.Id("P"),Comma,Rho,InMacro,Call("Mat",D(2),F.Id("C")),Comma,
        Forall,Sp,F.Id("j"),Comma,F.Id("k"),InMacro,Call("Fin",D(2)),Comma,
        Equal(Call("entry",TrEnv(Mul(Block(F.Id("Q"),F.Id("P")),Tensor(Rho,SigmaLower),StarOf(Block(F.Id("Q"),F.Id("P"))))),F.Id("j"),F.Id("k")),
            Mul(Call("entry",Rho,F.Id("j"),F.Id("k")),Trace(Mul(SigmaLower,StarOf(Call("branch",F.Id("Q"),F.Id("P"),F.Id("k"))),Call("branch",F.Id("Q"),F.Id("P"),F.Id("j")))))));
    private static Formula Entry(byte i, byte j) => Call("entry",Rho,D(i),D(j));
    private static Formula Entries() => ForReal(Join(Comma,V,W,T),Implies(Domain,Seq(
        Forall,Sp,Rho,InMacro,Call("Mat",D(2),F.Id("C")),Comma,
        Equal(Channel(V,T,Rho),Matrix2(Entry(0,0),Mul(StarOf(Chi(V,T)),Entry(0,1)),Mul(Chi(V,T),Entry(1,0)),Entry(1,1))))));
    private static Formula Pulses() => ForReal(Join(Comma,W,T),And(
        Equal(Pulse(D(1),T),Mul(Phase(T),Open,Mul(Cos(T),One),Minus,Mul(Imag,SinAt(T),Z),Close)),
        Equal(Pulse(NegOne,T),Mul(Phase(T),Open,Mul(Cos(T),One),Minus,Mul(Imag,SinAt(T),X),Close))));
    private static Formula IsolatedCoherence(bool quantifyFrequency = true) => ForReal(quantifyFrequency ? Join(Comma,W,T) : T,And(
        Equal(Chi(D(1),T),Mul(Phase(T),Cos(T))),Equal(Chi(NegOne,T),Mul(Phase(T),Cos(T)))));
    private static Formula IsolatedChannels(bool quantifyFrequency = true) => ForReal(quantifyFrequency ? Join(Comma,W,T) : T,Seq(Forall,Sp,Rho,InMacro,Call("DensityState",Call("Fin",D(2))),Comma,
        Equal(Channel(D(1),T,Rho),Channel(NegOne,T,Rho))));
    private static Formula PiPulses() => ForReal(Join(Comma,W,T),Implies(Equal(Mul(W,T),Pi),And(
        Equal(Pulse(D(1),T),Mul(Imag,Z)),Equal(Pulse(NegOne,T),Mul(Imag,X)))));
    private static Formula Anti() => Equal(Mul(Pulse(NegOne,T),Pulse(D(1),T)),Seq(Minus,Open,Mul(Pulse(D(1),T),Pulse(NegOne,T)),Close));
    private static Formula PiReadout() => And(Equal(Holo(T,T),Seq(Minus,One)),Equal(GammaAt(T,T),NegOne),Equal(Control(T,T),MinusState));
    private static Formula ScalarOrder() => Seq(Forall,Sp,Lambda,Comma,
        Rates(ForReal(Join(Comma,W,Tp,Tm),Seq(Forall,Sp,LambdaLower,InMacro,Lambda,Comma,
        And(Equal(Mul(Call("zminus",LambdaLower),Call("zplus",LambdaLower)),Mul(Call("zplus",LambdaLower),Call("zminus",LambdaLower))),
            Equal(Call("c",LambdaLower),D(1)),Seq(Call("c",LambdaLower),Neq,NegOne))))));
    private static Formula Integral(Formula x) => Seq(Int,Sp,x,Sp,F.Id("d"),Mu);
    private static Formula Rates(Formula body) => Seq(Forall,Sp,F.Id("nplus"),Comma,F.Id("nminus"),Colon,Lambda,Sp,To,Sp,F.Id("R"),Comma,body);
    private static Formula Average(bool quantifyFrequency = true) => Seq(Forall,Sp,Lambda,Comma,
        Call("MeasurableSpace",Lambda),Comma,Forall,Sp,Mu,InMacro,Call("ProbabilityMeasures",Lambda),Comma,
        Rates(ForReal(quantifyFrequency ? Join(Comma,W,Tp,Tm) : Join(Comma,Tp,Tm),
        And(Equal(Integral(Call("c",LambdaLower)),D(1)),Seq(Integral(Call("c",LambdaLower)),Neq,NegOne),
            Equal(Integral(Mul(Call("zminus",LambdaLower),Call("zplus",LambdaLower))),Integral(Mul(Call("zplus",LambdaLower),Call("zminus",LambdaLower))))))));
    private static Formula Complete() => ForReal(W,Implies(Seq(W,Gt,D(0)),And(
        ForReal(V,Implies(Domain,And(Call("PosDef",R(V)),Call("PosDef",N(V)),Equal(Square(N(V)),R(V))))),
        Coefficients(),And(Equal(N(D(1)),Root(Z)),Equal(N(NegOne),Root(X))),
        And(Equal(Call("matrix",Call("mixedState")),SigmaLower),Call("Surjective",Call("mulVec",SigmaLower))),
        ForReal(Join(Comma,V,T),Implies(Domain,Call("Unitary",Block(One,Pulse(V,T))))),
        IsolatedCoherence(false),IsolatedChannels(false),
        ForReal(Join(Comma,Tp,Tm),And(Equal(GammaAt(Tp,Tm),Polynomial(Tp,Tm)),Equal(Control(Tp,Tm),Marginal(GammaAt(Tp,Tm))))),
        ForReal(T,Implies(Equal(Mul(W,T),Pi),And(Equal(Pulse(D(1),T),Mul(Imag,Z)),Equal(Pulse(NegOne,T),Mul(Imag,X)),Anti(),PiReadout()))),
        Equal(Mul(W,Fraction(Pi,W)),Pi),Average(false))));
}

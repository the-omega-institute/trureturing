using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds;

internal sealed class StatisticalStrengthMagicSquareDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/vandam2005statisticalstrength");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four joint settings on two literal singlets beat twice CHSH under all three statistical-strength conventions.",
        H("Statistical strength of the two-singlet magic square"),
        Blocks(
            Definition("uniform", "Uniform finite distributions", UniformFormula(),
                "Section IV.B, p. 8: “where σ° denotes the uniform distribution over the settings.” The existing Mathlib type stdSimplex NNReal (Fin n) consists of nonnegative masses summing to one. Fin n indexes n points by 0,…,n−1; [NeZero n] excludes an empty uniform law. Application uses the existing FunLike coercion of stdSimplex."),
            Definition("D", "Finite relative entropy in bits", DivergenceFormula(),
                "Section IV.A, p. 6: “For two (arbitrary) distributions Q and P defined over Z, the Kullback-Leibler (KL) divergence from Q to P is defined as” D(Q∥P) := ∑z∈Z Q(z) log(Q(z)/P(z)), “where the logarithm is taken here, as in the rest of the paper, to base 2.” The zero-mass conventions make a zero q mass contribute zero and a positive q mass above zero p mass contribute infinity. Real.log is the natural logarithm, so division by Real.log 2 converts to bits. The finite branch is coerced from R to EReal; ⊤ is EReal's positive infinity. The displayed expression uses Lean's total real division and logarithm, including log 0 = 0, only inside the absolutely continuous branch."),
            Definition("localBehavior", "All local response mixtures", LocalFormula(),
                "Section II.D, p. 5: “A local theory π may be viewed as a probability distribution for (X₁,X₂,Y₁,Y₂).” For s settings and o outcomes, the literal generalization is: μ is any normalized distribution on pairs of deterministic response functions Fin s → Fin o. The finite sum marginalizes the responses at x and y. It includes every local theory, including nonrational weights; the proof never limits μ to a list of strategies."),
            Definition("productLaw", "Independent setting laws", ProductFormula(),
                "Section IV.B, p. 8 requires that “the distribution for each party is uncorrelated with the distributions of the other parties”. Two marginal distributions alpha and beta yield their pointwise product on pairs of settings. The stdSimplex proofs verify its normalization."),
            Definition("uniformLaw", "Uniform pairs of settings", UniformLawFormula(),
                "This is the source's σ°: the product of the two uniform setting laws, with s² equally weighted pairs."),
            Definition("joint", "Settings and outcomes in one distribution", JointFormula(),
                "Section II.B, p. 5: “According to QM, the total outcome (X,Y,A,B) of a single trial is then distributed as Qσ, defined by” Qσ(X = x,Y = y,A = a,B = b) := σab Qab(X = x,Y = y). The index z groups the setting pair z.1 and the outcome pair z.2. Its four entries are selected using Lean's product projections. q is the conditional outcome law; sigma is a distribution of settings."),
            Definition("strengthAt", "Infimum over every local theory", StrengthAtFormula(),
                "Section IV.B, p. 8 defines D(Qσ∥Pσ) as the infimum of D(Qσ∥Pσ,π) over π∈Π. Here iInf is the infimum in EReal, over the entire stdSimplex of deterministic-response mixtures."),
            Definition("S_uni", "Strength for uniform settings", UniformStrengthFormula(),
                "Definition 1, Section IV.B, p. 8: “When each measurement setting is sampled with equal probability, the resulting strength S_Q^UNI is defined by” S_Q^UNI := D(Qσ°∥Pσ°) = infπ∈Π D(Qσ°∥Pσ°,π), “where σ° denotes the uniform distribution over the settings.” The source symbol S_Q^UNI is encoded by S_uni q; strengthAt supplies the infimum."),
            Definition("S", "Strength for uncorrelated settings", ProductStrengthFormula(),
                "Definition 2, Section IV.B, p. 8: “When the experimenter QM is allowed to choose any distribution on measurement settings, as long as the distribution for each party is uncorrelated with the distributions of the other parties, the resulting strength S_Q^UC is defined by” S_Q^UC := supσ∈ΣUC D(Qσ∥Pσ) = supσ∈ΣUC infπ∈Π D(Qσ∥Pσ,π), “where σ∈ΣUC denotes the use of uncorrelated settings.” S q is literally the supremum over pairs of marginal distributions, each giving productLaw alpha beta."),
            Definition("S_cor", "Strength for correlated settings", CorrelatedStrengthFormula(),
                "Definition 3, Section IV.B, p. 8: “When the experimeniter QM is allowed to choose any distribution on measurement settings (including correlated distributions), the resulting strength S_Q^COR is defined by” S_Q^COR := supσ∈Σ D(Qσ∥Pσ) = supσ∈Σ infπ∈Π D(Qσ∥Pσ,π), “where σ∈Σ denoted the use of correlated settings.” The words “experimeniter” and “denoted” reproduce the source. S_cor q takes the supremum over all normalized setting laws."),
            Definition("singletCoefficient", "The literal Bell singlet", SingletFormula(),
                "The two-qubit singlet is (|01⟩−|10⟩)/sqrt 2. These are its literal complex amplitudes in the computational basis. The minus sign distinguishes the singlet from Phi-plus. The inverse square root is in C."),
            Definition("twoSinglets", "Two singlets shared between the parties", TwoSingletsFormula(),
                "The global index z consists of Alice's two-qubit basis index z.1 and Bob's z.2. Multiplying singletCoefficient on each corresponding Alice–Bob pair is the literal tensor product of two singlets, regrouped by party. No entanglement proxy replaces that state."),
            Definition("IsPVM", "Four nonzero orthogonal projectors", PvmFormula(),
                "Under the four-nonzero-outcome measurement convention, each setting has four nonzero projectors. Each projector is self-adjoint and idempotent; distinct outcomes are orthogonal; their sum is the identity. star on matrices is conjugate transpose. The anonymous Fintype and DecidableEq brackets are Lean instance arguments, not new mathematical variables."),
            Definition("Experiment", "Two parties, four settings, four outcomes", ExperimentFormula(),
                "The structure has exactly the fields alice and bob, both with type Fin 4 → Fin 4 → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) C. The first argument indexes a local setting and the second an outcome. Each party's operator acts jointly on its two qubits. Together with Valid, this is the source's 2×4×4 experiment type."),
            Definition("Valid", "Validity of all eight settings", ValidFormula(),
                "Every Alice setting and every Bob setting satisfies IsPVM. In particular the four outcomes of every setting are nonzero."),
            Definition("ProductOperator", "Products of single-qubit operators", ProductOperatorFormula(),
                "A product operator is literally a Kronecker product A ⊗ₖ B of arbitrary two-by-two complex matrices. No rank or separability surrogate replaces that existential definition."),
            Definition("JointMeasurement", "A joint measurement on a pair", JointFormulaPredicate(),
                "Conjecture 5, Section VI.D, p. 11 requires “involving joint measurements on the pairs.” This means that at least one local projector, for Alice or Bob, is not a product of single-qubit operators. The existential quantifiers range over actual settings and outcomes."),
            Definition("born", "Born amplitudes of the two-singlet experiment", BornFormula(),
                "The expression is the literal Born expectation: dotProduct of star twoSinglets with the action of the Kronecker product of the two local outcome projectors. All four indices range over Fin 4."),
            Definition("quantum", "Conditional quantum probabilities", QuantumFormula(),
                "The quantum conditional law is Real.toNNReal of the real part of the Born expectation. Validity proves that this real part is nonnegative and that the probabilities sum to one; the truncation thus leaves every valid Born probability unchanged."),
            Definition("chshAlice", "Alice's CHSH projectors", ChshAliceFormula(),
                "Appendix III.C, pp. 18–20 gives the CHSH quantum table. These two-outcome projectors use frozen qubitZ and qubitX. Settings and outcomes have indices 0 and 1. The sign is +1 for outcome 0 and −1 for outcome 1."),
            Definition("chshBob", "Bob's singlet-conjugated CHSH projectors", ChshBobFormula(),
                "The source realizes its CHSH table with Phi-plus. Bob's observables are conjugated by the local singlet unitary. On a literal singlet they are −(Z+X)/sqrt 2 and −(Z−X)/sqrt 2; these projectors reproduce the source table, with probabilities (2+sqrt 2)/8 for a winning output and (2−sqrt 2)/8 otherwise."),
            Definition("chshBorn", "The CHSH Born expectation on a singlet", ChshBornFormula(),
                "The vector in both dotProduct and mulVec has entries singletCoefficient z.1 z.2. This expectation uses a literal singlet and the displayed CHSH PVMs, not the source's Phi-plus state."),
            Definition("chsh", "The physical CHSH conditional law", ChshFormula(),
                "The probabilities are Real.toNNReal of the real parts of the literal singlet Born expectations. The private source_chsh_born calculation connects this law to Appendix III.C's table and is used in the arbitrary-setting-law upper bound."),
            Definition("claim", "Conjecture 5", ClaimFormula(),
                "Conjecture 5, Section VI.D, p. 11: “There is an experiment on pairs of Bell singlets, of the 2×4×4 type, more than twice as strong as CHSH, and involving joint measurements on the pairs.” The encoding is: there exists e : Experiment with Valid e and JointMeasurement e, and S_uni (quantum e) > 2 * S_cor chsh. Since the uniform strength is no larger than the product-setting strength, which is no larger than the correlated-setting strength, this inequality implies the required comparison in each of the source's three senses."),
            Describe.Lean(DescribeId.Create("vdgg-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The two-singlet experiment proves the conjecture"),
                StatementSource.FromAuthor(ClaimFormula()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The commuting magic-square rows and columns give four nonzero-outcome PVMs on each side. Bob's transpose and local singlet conjugation give the Born trace identity, and losing parity outcomes have zero probability. Every pair of deterministic local response functions wins at most eight of the nine magic-square contexts. Averaging preserves that bound for every normalized local mixture. Coarse-graining the uniform joint law into outside, winning and losing bins and applying the frozen log-sum inequality proves S_uni ≥ (9/16) log(9/8)/log 2. A single local CHSH reference mixture gives S_cor CHSH ≤ c for every setting law. The fulfilled rational logarithm enclosures prove 2c < 93/1000 < 95/1000 < (9/16) log(9/8)/log 2. A nonzero product-operator minor proves that an Alice projector is joint. No exact optimal strength or global optimality claim is made."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("van-dam-gill-grunwald-2005-two-singlet-strength"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock.Describe Definition(string name, string heading, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("vdgg-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(heading), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Instance(string name, Formula[] args, Formula body) =>
        Seq(OpenBracket, Call(name, args), CloseBracket, Sp, body);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Pair(Formula a, Formula b) => Seq(a, Sp, Times, Sp, b);
    private static Formula Qualified(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula At(Formula value, params Formula[] args) => new Formula.Apply(value, [.. args]);
    private static Formula Field(Formula value, byte index) => Seq(value, Dot, D(index));
    private static Formula As(Formula value, Formula type) => Parenthesized(Seq(value, Colon, type));
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Name(string name) => Seq(Operatorname,Grp(F.Id(name)));
    private static Formula NNReal() => Name("NNReal");
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Fin(byte n) => Fin(D(n));
    private static Formula TwoQubits() => Parenthesized(Pair(Fin(2), Fin(2)));
    private static Formula Distribution(Formula type) => Call("stdSimplex", NNReal(), type);
    private static Formula Behavior(Formula s, Formula o) => Arrow(Fin(s), Arrow(Fin(s), Arrow(Fin(o), Arrow(Fin(o), NNReal()))));
    private static Formula Strategies(Formula s, Formula o) => Pair(Parenthesized(Arrow(Fin(s), Fin(o))), Parenthesized(Arrow(Fin(s), Fin(o))));
    private static Formula Matrix(Formula n) => Call("Matrix", n, n, Complex());
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(Seq(F.Id(name), Colon, type)), Sp, Parenthesized(body));
    private static Formula InfOver(string name, Formula type, Formula body) =>
        Seq(Operatorname, Grp(F.Id("iInf")), Underscore, Grp(Seq(F.Id(name), Colon, type)), Sp, Parenthesized(body));
    private static Formula SupOver(string name, Formula type, Formula body) =>
        Seq(Operatorname, Grp(F.Id("iSup")), Underscore, Grp(Seq(F.Id(name), Colon, type)), Sp, Parenthesized(body));
    private static Formula Strength(string suffix, Formula q) =>
        At(Seq(Operatorname, Grp(F.Id("S")), Underscore, Grp(F.Id(suffix))), q);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Parenthesized(a), op, Parenthesized(b));
    private static Formula And(params Formula[] clauses)
    {
        Formula body = clauses[^1];
        for (int i = clauses.Length - 2; i >= 0; i--) body = Logic(clauses[i], FormulaLogicOperator.And, body);
        return body;
    }
    private static Formula Equation(string name, Formula body, params Formula[] args) => Equal(Call(name, args), body);
    private static Formula Parameters(Formula body) => All("s", Nat(), All("o", Nat(), body));

    private static Formula UniformFormula() => Disp(All("n", Nat(), Instance("NeZero", [F.Id("n")],
        All("i", Fin(F.Id("n")), Equal(At(Call("uniform", F.Id("n")), F.Id("i")),
            new Formula.Power(As(F.Id("n"), NNReal()), new Formula.Negate(D(1))))))));

    private static Formula DivergenceFormula()
    {
        Formula alpha = F.Id("alpha"), q = F.Id("q"), p = F.Id("p"), z = F.Id("z");
        Formula ac = All("z", alpha, Logic(Equal(At(p,z),D(0)), FormulaLogicOperator.Implies, Equal(At(q,z),D(0))));
        Formula term = new Formula.Fraction(Multiply(As(At(q,z),Real()),
            Qualified("Real","log",new Formula.Fraction(As(At(q,z),Real()),As(At(p,z),Real())))),
            Qualified("Real","log",D(2)));
        Formula body = Equation("D", Call("ite", ac, As(SumOver("z",alpha,term),Name("EReal")),
            Qualified("Top","top")),q,p);
        return Disp(All("alpha",F.Id("Type"),Instance("Fintype",[alpha],
            All("q",Arrow(alpha,NNReal()),All("p",Arrow(alpha,NNReal()),body)))));
    }
    private static Formula LocalFormula()
    {
        Formula s=F.Id("s"),o=F.Id("o"),mu=F.Id("mu"),t=F.Id("t"),x=F.Id("x"),y=F.Id("y"),a=F.Id("a"),b=F.Id("b");
        Formula condition=And(Equal(At(Field(t,1),x),a),Equal(At(Field(t,2),y),b));
        Formula body=Equal(At(Call("localBehavior",mu),x,y,a,b),
            SumOver("t",Strategies(s,o),Call("ite",condition,At(mu,t),D(0))));
        return Disp(Parameters(All("mu",Distribution(Strategies(s,o)),
            All("x",Fin(s),All("y",Fin(s),All("a",Fin(o),All("b",Fin(o),body)))))));
    }
    private static Formula ProductFormula()
    {
        Formula s=F.Id("s"),alpha=F.Id("alpha"),beta=F.Id("beta"),z=F.Id("z");
        return Disp(All("s",Nat(),All("alpha",Distribution(Fin(s)),All("beta",Distribution(Fin(s)),
            All("z",Pair(Fin(s),Fin(s)),Equal(At(Call("productLaw",alpha,beta),z),
                Multiply(At(alpha,Field(z,1)),At(beta,Field(z,2)))))))));
    }
    private static Formula UniformLawFormula() => Disp(All("s",Nat(),Instance("NeZero",[F.Id("s")],
        Equation("uniformLaw",Call("productLaw",Call("uniform",F.Id("s")),Call("uniform",F.Id("s"))),F.Id("s")))));
    private static Formula JointFormula()
    {
        Formula s=F.Id("s"),o=F.Id("o"),sigma=F.Id("sigma"),q=F.Id("q"),z=F.Id("z");
        return Disp(Parameters(All("sigma",Distribution(Pair(Fin(s),Fin(s))),All("q",Behavior(s,o),
            All("z",Pair(Parenthesized(Pair(Fin(s),Fin(s))),Parenthesized(Pair(Fin(o),Fin(o)))),
                Equal(At(Call("joint",sigma,q),z),Multiply(At(sigma,Field(z,1)),
                    At(q,Field(Field(z,1),1),Field(Field(z,1),2),Field(Field(z,2),1),Field(Field(z,2),2)))))))));
    }
    private static Formula StrengthAtFormula()
    {
        Formula s=F.Id("s"),o=F.Id("o"),q=F.Id("q"),sigma=F.Id("sigma"),mu=F.Id("mu");
        return Disp(Parameters(All("q",Behavior(s,o),All("sigma",Distribution(Pair(Fin(s),Fin(s))),
            Equation("strengthAt",InfOver("mu",Distribution(Strategies(s,o)),
                Call("D",Call("joint",sigma,q),Call("joint",sigma,Call("localBehavior",mu)))),q,sigma)))));
    }
    private static Formula UniformStrengthFormula()
    {
        Formula s=F.Id("s"),o=F.Id("o"),q=F.Id("q");
        return Disp(Parameters(Instance("NeZero",[s],All("q",Behavior(s,o),
            Equal(Strength("uni",q),Call("strengthAt",q,Call("uniformLaw",s)))))));
    }
    private static Formula ProductStrengthFormula()
    {
        Formula s=F.Id("s"),o=F.Id("o"),q=F.Id("q"),alpha=F.Id("alpha"),beta=F.Id("beta");
        return Disp(Parameters(All("q",Behavior(s,o),Equation("S",
            SupOver("alpha",Distribution(Fin(s)),SupOver("beta",Distribution(Fin(s)),
                Call("strengthAt",q,Call("productLaw",alpha,beta)))),q))));
    }
    private static Formula CorrelatedStrengthFormula()
    {
        Formula s=F.Id("s"),o=F.Id("o"),q=F.Id("q"),sigma=F.Id("sigma");
        return Disp(Parameters(All("q",Behavior(s,o),Equal(Strength("cor",q),
            SupOver("sigma",Distribution(Pair(Fin(s),Fin(s))),Call("strengthAt",q,sigma))))));
    }
    private static Formula SingletFormula()
    {
        Formula a=F.Id("a"),b=F.Id("b");
        Formula inverse=new Formula.Power(As(Qualified("Real","sqrt",D(2)),Complex()),new Formula.Negate(D(1)));
        Formula body=Call("ite",And(Equal(a,D(0)),Equal(b,D(1))),inverse,
            Call("ite",And(Equal(a,D(1)),Equal(b,D(0))),new Formula.Negate(inverse),D(0)));
        return Disp(All("a",Fin(2),All("b",Fin(2),Equation("singletCoefficient",body,a,b))));
    }
    private static Formula TwoSingletsFormula()
    {
        Formula z=F.Id("z");
        return Disp(All("z",Pair(TwoQubits(),TwoQubits()),Equal(At(Name("twoSinglets"),z),
            Multiply(Call("singletCoefficient",Field(Field(z,1),1),Field(Field(z,2),1)),
                Call("singletCoefficient",Field(Field(z,1),2),Field(Field(z,2),2))))));
    }
    private static Formula PvmFormula()
    {
        Formula n=F.Id("n"),p=F.Id("P"),a=F.Id("a"),b=F.Id("b");
        Formula each=All("a",Fin(4),And(NotEqual(At(p,a),D(0)),Equal(Call("star",At(p,a)),At(p,a)),
            Equal(Multiply(At(p,a),At(p,a)),At(p,a))));
        Formula orthogonal=All("a",Fin(4),All("b",Fin(4),Logic(NotEqual(a,b),FormulaLogicOperator.Implies,
            Equal(Multiply(At(p,a),At(p,b)),D(0)))));
        return Disp(All("n",F.Id("Type"),Instance("Fintype",[n],Instance("DecidableEq",[n],
            All("P",Arrow(Fin(4),Matrix(n)),Equation("IsPVM",And(each,orthogonal,
                Equal(SumOver("a",Fin(4),At(p,a)),D(1))),p))))));
    }
    private static Formula ExperimentFormula()
    {
        Formula e=F.Id("e");
        Formula type=Arrow(Fin(4),Arrow(Fin(4),Matrix(TwoQubits())));
        return Disp(new Formula.Aligned([
            Seq(Name("Experiment"),Colon,F.Id("Type")),
            All("e",Name("Experiment"),Seq(Party("alice",e),Colon,type)),
            All("e",Name("Experiment"),Seq(Party("bob",e),Colon,type))]));
    }
    private static Formula Party(string party, Formula e, params Formula[] args) =>
        Qualified("Experiment",party,[e,..args]);
    private static Formula ValidFormula()
    {
        Formula e=F.Id("e");
        return Disp(All("e",Name("Experiment"),Equation("Valid",And(
            All("x",Fin(4),Call("IsPVM",Party("alice",e,F.Id("x")))),
            All("y",Fin(4),Call("IsPVM",Party("bob",e,F.Id("y"))))),e)));
    }
    private static Formula Tensor(Formula a, Formula b) => Qualified("Matrix","kroneckerMap",
        Parenthesized(Seq(LambdaLower, Sp, Parenthesized(Seq(F.Id("u"), Sp, F.Id("v"), Colon, Complex())), Comma, Sp, Multiply(F.Id("u"), F.Id("v")))),a,b);
    private static Formula ProductOperatorFormula()
    {
        Formula p=F.Id("P"),a=F.Id("A"),b=F.Id("B");
        return Disp(All("P",Matrix(TwoQubits()),Equation("ProductOperator",Some("A",Matrix(Fin(2)),
            Some("B",Matrix(Fin(2)),Equal(p,Tensor(a,b)))),p)));
    }
    private static Formula JointFormulaPredicate()
    {
        Formula e=F.Id("e");
        Formula alice=Some("x",Fin(4),Some("a",Fin(4),new Formula.Not(Call("ProductOperator",Party("alice",e,F.Id("x"),F.Id("a"))))));
        Formula bob=Some("y",Fin(4),Some("b",Fin(4),new Formula.Not(Call("ProductOperator",Party("bob",e,F.Id("y"),F.Id("b"))))));
        return Disp(All("e",Name("Experiment"),Equation("JointMeasurement",Logic(alice,FormulaLogicOperator.Or,bob),e)));
    }
    private static Formula FourIndices(Formula body) => All("x",Fin(4),All("y",Fin(4),All("a",Fin(4),All("b",Fin(4),body))));
    private static Formula TwoIndices(Formula body) => All("x",Fin(2),All("y",Fin(2),All("a",Fin(2),All("b",Fin(2),body))));
    private static Formula BornFormula()
    {
        Formula e=F.Id("e"),x=F.Id("x"),y=F.Id("y"),a=F.Id("a"),b=F.Id("b"),v=Name("twoSinglets");
        Formula body=Call("dotProduct",Call("star",v),Qualified("Matrix","mulVec",Tensor(Party("alice",e,x,a),Party("bob",e,y,b)),v));
        return Disp(All("e",Name("Experiment"),FourIndices(Equation("born",body,e,x,y,a,b))));
    }
    private static Formula QuantumFormula()
    {
        Formula e=F.Id("e"),x=F.Id("x"),y=F.Id("y"),a=F.Id("a"),b=F.Id("b");
        return Disp(All("e",Name("Experiment"),FourIndices(Equal(At(Call("quantum",e),x,y,a,b),
            Qualified("Real","toNNReal",Qualified("Complex","re",Call("born",e,x,y,a,b)))))));
    }
    private static Formula Sign(Formula a) => Call("ite",Equal(a,D(0)),D(1),new Formula.Negate(D(1)));
    private static Formula Smul(Formula a, Formula b) => Qualified("HSMul","hSMul",a,b);
    private static Formula ChshAliceFormula()
    {
        Formula x=F.Id("x"),a=F.Id("a");
        Formula observable=Call("ite",Equal(x,D(0)),Name("qubitZ"),Name("qubitX"));
        return Disp(All("x",Fin(2),All("a",Fin(2),Equation("chshAlice",
            Smul(As(new Formula.Fraction(D(1),D(2)),Complex()),Add(D(1),Smul(Sign(a),observable))),x,a))));
    }
    private static Formula ChshBobFormula()
    {
        Formula y=F.Id("y"),b=F.Id("b");
        Formula observable=Call("ite",Equal(y,D(0)),Add(Name("qubitZ"),Name("qubitX")),Subtract(Name("qubitZ"),Name("qubitX")));
        Formula scale=new Formula.Negate(new Formula.Power(As(Qualified("Real","sqrt",D(2)),Complex()),new Formula.Negate(D(1))));
        return Disp(All("y",Fin(2),All("b",Fin(2),Equation("chshBob",
            Smul(As(new Formula.Fraction(D(1),D(2)),Complex()),Add(D(1),Smul(Sign(b),Smul(scale,observable)))),y,b))));
    }
    private static Formula ChshBornFormula()
    {
        Formula x=F.Id("x"),y=F.Id("y"),a=F.Id("a"),b=F.Id("b"),z=F.Id("z");
        Formula v=Seq(LambdaLower,Sp,Parenthesized(Seq(z,Colon,Pair(Fin(2),Fin(2)))),Comma,Sp,
            Call("singletCoefficient",Field(z,1),Field(z,2)));
        Formula body=Call("dotProduct",Call("star",Parenthesized(v)),Qualified("Matrix","mulVec",Tensor(Call("chshAlice",x,a),Call("chshBob",y,b)),Parenthesized(v)));
        return Disp(TwoIndices(Equation("chshBorn",body,x,y,a,b)));
    }
    private static Formula ChshFormula() => Disp(TwoIndices(Equal(At(Name("chsh"),F.Id("x"),F.Id("y"),F.Id("a"),F.Id("b")),
        Qualified("Real","toNNReal",Qualified("Complex","re",Call("chshBorn",F.Id("x"),F.Id("y"),F.Id("a"),F.Id("b")))))));
    private static Formula ClaimFormula()
    {
        Formula e=F.Id("e");
        Formula inequality=new Formula.Relation(Strength("uni",Call("quantum",e)),FormulaRelationOperator.GreaterThan,
            Multiply(D(2),Strength("cor",Name("chsh"))));
        return Disp(Some("e",Name("Experiment"),And(Call("Valid",e),Call("JointMeasurement",e),inequality)));
    }
}

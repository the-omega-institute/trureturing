using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class MayerZeroFidelityTightnessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/QuantumChannels/MayerZeroFidelityTightness.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/mayer2021zerofidelity");

    private static readonly LibraryNoteRef SicSource =
        LibraryNoteRef.Create("D5/L/QuantumStates/renes2004sic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The product SIC states test an n-qubit channel through their survival probabilities. Process fidelity tests the same channel on one half of a maximally entangled state.",
        H("Mayer zero fidelity and process fidelity"),
        Blocks(
            SicNode("sic", "Qubit SIC vectors", SicFormula(), "IsQubitSIC",
                "The normalization uses the Hermitian inner product on the two complex coordinates. Each pair of distinct vectors has squared overlap one third.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            SicNode("frame", "The symmetric second moment", FrameFormula(), "sic_frame",
                "Write Pk for the outer product of the kth vector with its conjugate. The trace of the square of their tensor sum is sixteen thirds. Its trace against identity plus exchange is eight, and the square of identity plus exchange has trace twelve. Consequently, the squared Hilbert-Schmidt norm of the difference from two thirds times identity plus exchange vanishes.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(SicSource)),
            SicNode("bilinear", "Bilinear second moments", BilinearFormula(), "sic_bilinear",
                "The exchange matrix is the swapMatrix of CompositeConeProperness. Contracting the second moment with the tensor product of two arbitrary matrices gives the trace identity. The exchange term contributes the trace of their product.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(SicSource)),
            Node("product", "Product SIC states", ProductFormula(), "productState",
                "At each position a label chooses one of four single-qubit SIC vectors. The coordinate of their tensor product is the product of their coordinates.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("zero", "Zero fidelity", ZeroFormula(), "zeroFidelity",
                "For d equal to two to the power n, zero fidelity is d to the power minus two times the sum of the survival probabilities over all product SIC labels. The channel acts by the sum of Kj rho Kj conjugate transpose.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("process", "Process fidelity", ProcessFormula(), "processFidelity",
                "The channel acts on the second register, with Kraus operators identity tensor Kj. Process fidelity is the expectation of the resulting density matrix in the maxEntangledVector of PeritoTsirelson on the qubit register. Its rank-one matrix is maxEntangled.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("support", "Pauli support of weight at most one", SupportFormula(), "HasWeightOneSupport",
                "Pauli weight is the Hamming distance from the constant identity word. Every Kraus operator has zero Hilbert-Schmidt coefficient on every Pauli string of weight at least two. Equivalently, each operator belongs to the span of identity and the three single-position Pauli operators at every position.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("covariance", "Product Pauli moments", CovarianceFormula(), "product_pauli_covariance",
                "The rank-one density matrix of a product vector is the tensor product of its single-qubit projectors. Its Pauli expectation therefore factors position by position. The bilinear SIC moment gives four for the identity factor, four thirds for a matching nonidentity factor, and zero for unequal factors. Multiplying these moments gives the stated covariance.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("parseval", "The Pauli second-moment expansion", ParsevalFormula(), "product_pauli_parseval",
                "Expand an arbitrary matrix in the orthogonal Pauli basis. The word_hermitian lemma of StabilizerPovmMaximalEntanglementRefutation states that every Pauli word is Hermitian, so its expectations in pure states are real. Expanding the squared modulus produces a double sum of Pauli coefficients; the product covariance removes all unequal pairs. Its factor four to the power n cancels the squared inverse dimension in the coefficients, leaving one third to the Pauli weight times each squared trace coefficient.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("survival", "Kraus survival amplitudes", SurvivalFormula(), "kraus_survival",
                "Each Kraus term maps a pure projector to the projector of the transformed vector. Its expectation in the original vector is the squared modulus of their inner product. Additivity gives the sum over the Kraus family.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("bell-amplitude", "Bell amplitude of an operator", BellAmplitudeFormula(), "bell_amplitude",
                "The maximally entangled trace contraction with identity on the first register gives the operator trace divided by the register dimension, which is two to the power n.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("mass", "Total Pauli probability", MassFormula(), "pauli_total_mass",
                "The Pauli expansion gives the sum of squared trace coefficients as d times the Hilbert-Schmidt squared norm of each Kraus operator. Trace preservation makes the sum of those norms equal to d. Division by d squared gives total probability one.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("weights", "The weighted probability bound", WeightBoundFormula(), "weight_bound",
                "The gap is a sum of nonnegative probability terms. The coefficient vanishes at weights zero and one, and is strictly positive at every weight at least two. The gap vanishes exactly when every such probability vanishes.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("process-trace", "Process fidelity in trace coordinates", ProcessTraceFormula(), "process_trace",
                "Apply the Kraus survival identity to the normalized Bell vector and then use its operator amplitude. The resulting fidelity is the sum of squared Kraus traces divided by d squared.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("zero-trace", "Zero fidelity in Pauli coordinates", ZeroTraceFormula(), "zero_trace",
                "Apply the Kraus survival identity to every product SIC vector. The Pauli second moment and interchange of the two finite sums give one third to the Pauli weight times the normalized coefficient probability.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("bound", "Lower bound and its equality cases", BoundFormula(true), "channel_bound",
                "Trace preservation supplies a nonnegative Pauli probability distribution. Process fidelity is its identity probability, and zero fidelity is its weighted sum. The scalar bound gives the lower inequality. Equality requires every coefficient probability of weight at least two to vanish; a sum of squared moduli vanishes precisely when every individual Kraus trace coefficient vanishes.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("tight", "A channel attaining every permitted fidelity", TightFormula(), "tight_channel",
                "Choose p equal to three f minus one divided by two and t equal to one minus p divided by three. Both parameters are nonnegative. The Kraus operators are square root p times identity and square root t times each of the three Pauli operators on position zero. Their squared operators sum to identity. Every Kraus word has weight at most one: every Pauli coefficient of higher weight has a traceless factor at another position. The three nonidentity Kraus traces vanish, so process fidelity is p. The equality characterization then forces zero fidelity to equal f.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("lower-bound", "Mayer's lower inequality", BoundFormula(false), "lower_bound",
                "The lower inequality in Theorem 1 bounds the process fidelity by one minus three halves of the zero infidelity.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The sharp lower bound", Disp(Iff(Named("claim"), ClaimBody())), "claim",
                "For every positive number of qubits and every choice of local SIC vectors, the lower bound has equality precisely for Kraus operators of Pauli weight at most one. Every zero fidelity between one third and one is to be attained at that bound.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Describe.Lean(DescribeId.Create("mayer-tightness-result"),
                Handle("result"), H("Tightness in every qubit dimension"),
                StatementSource.FromAuthor(Disp(ClaimBody())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every positive number of qubits and every choice of local SIC vectors, the process fidelity is bounded below by one minus three halves of the zero infidelity. Equality holds precisely when all Kraus coefficients on Pauli words of weight at least two vanish. Noise acting on one qubit supplies a trace-preserving Kraus family that attains this bound at every zero fidelity from one third to one."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("mayer-2021-zero-fidelity-tightness"), ResolutionKind.Proved))), []));

    private static DeclarationHandle Handle(string declaration) => DeclarationHandle.Create(Prefix + declaration);

    private static DocumentBlock SicNode(string id, string title, Formula formula, string declaration,
        string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("mayer-sic-" + id), Handle(declaration),
            H(title), StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);

    private static DocumentBlock Node(string id, string title, Formula formula, string declaration,
        string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("mayer-tightness-" + id), Handle(declaration),
            H(title), StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Field(string x) => Seq(Mathbb, Grp(F.Id(x)));
    private static Formula Named(string x) => Seq(Operatorname, Grp(F.Id(x)));
    private static Formula Call(string x, params Formula[] args) => new Formula.Apply(Named(x), [.. args]);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula All(string x, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), type, body);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(Par(a), FormulaBinaryOperator.Multiply, Par(b));
    private static Formula Fin(byte n) => Call("Fin", D(n));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Vectors() => Arrow(Fin(4), Arrow(Fin(2), Field("C")));
    private static Formula Reg(Formula n) => Arrow(Call("Fin", n), Fin(2));
    private static Formula States(Formula n) => Arrow(Call("Fin", n), Vectors());
    private static Formula Mat(Formula n) => Call("Matrix", Reg(n), Reg(n), Field("C"));
    private static Formula Kraus(Formula n, Formula r) => Arrow(Call("Fin", r), Mat(n));
    private static Formula Dim(Formula n) => new Formula.Power(D(2), n);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, Par(b));
    private static Formula Exists(string x, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(x), type, body);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(Par(a), FormulaBinaryOperator.Subtract, Par(b));
    private static Formula Lower(Formula f) => Sub(D(1), Mul(new Formula.Fraction(D(3), D(2)), Sub(D(1), f)));
    private static Formula At(Formula a, Formula b) => new Formula.Apply(a, [b]);
    private static Formula SumAt(string x, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(F.Id(x), Colon, type)), Sp, body);


    private static Formula Add(Formula a, Formula b) => new Formula.Binary(Par(a), FormulaBinaryOperator.Add, Par(b));
    private static Formula Mat() => Call("Matrix", Fin(2), Fin(2), Field("C"));
    private static Formula Tensor(Formula a, Formula b) => Call("tensor", a, b);
    private static Formula Proj(Formula s, Formula k) => Call("rankOneDensity", At(s, k));

    private static Formula SicFormula()
    {
        Formula s = F.Id("s"), k = F.Id("k"), l = F.Id("l");
        Formula unit = All("k", Fin(4), Eqn(Call("inner", At(s, k), At(s, k)), D(1)));
        Formula pair = All("k", Fin(4), All("l", Fin(4), Imp(new Formula.Not(Eqn(k, l)),
            Eqn(new Formula.Power(new Formula.Norm(Call("inner", At(s, k), At(s, l))), D(2)),
                new Formula.Fraction(D(1), D(3))))));
        return Disp(All("s", Vectors(), new Formula.Logic(Call("IsQubitSIC", s),
            FormulaLogicOperator.Iff, Par(And(unit, pair)))));
    }

    private static Formula FrameFormula()
    {
        Formula s = F.Id("s"), k = F.Id("k");
        return Disp(All("s", Vectors(), Imp(Call("IsQubitSIC", s),
            Eqn(SumAt("k", Fin(4), Tensor(Proj(s, k), Proj(s, k))),
                Mul(new Formula.Fraction(D(2), D(3)), Add(D(1), Named("swapMatrix")))))));
    }

    private static Formula BilinearFormula()
    {
        Formula s = F.Id("s"), k = F.Id("k"), a = F.Id("A"), b = F.Id("B");
        Formula lhs = SumAt("k", Fin(4), Mul(Call("trace", Mul(Proj(s, k), a)), Call("trace", Mul(Proj(s, k), b))));
        Formula rhs = Mul(new Formula.Fraction(D(2), D(3)), Add(Mul(Call("trace", a), Call("trace", b)), Call("trace", Mul(a, b))));
        return Disp(All("s", Vectors(), Imp(Call("IsQubitSIC", s), All("A", Mat(), All("B", Mat(), Eqn(lhs, rhs))))));
    }

    private static Formula ProductFormula()
    {
        Formula n = F.Id("n"), s = F.Id("s"), k = F.Id("k"), x = F.Id("x"), i = F.Id("i");
        Formula value = Seq(new Formula.Subscript(F.Prod, Seq(i, Colon, Call("Fin", n))), Sp,
            At(At(At(s, i), At(k, i)), At(x, i)));
        return Disp(All("n", Field("N"), All("s", States(n), All("k", Arrow(Call("Fin", n), Fin(4)),
            All("x", Reg(n), Eqn(At(Call("productState", s, k), x), value))))));
    }
    private static Formula ZeroFormula()
    {
        Formula n = F.Id("n"), r = F.Id("r"), s = F.Id("s"), k = F.Id("k"), ks = F.Id("K");
        Formula v = Call("productState", s, k);
        Formula value = Mul(new Formula.Fraction(D(1), new Formula.Power(Dim(n), D(2))),
            SumAt("k", Arrow(Call("Fin", n), Fin(4)), Call("real", Call("inner", v,
                Call("mulVec", Call("kraus", ks, Call("rankOneDensity", v)), v)))));
        return Disp(All("n", Field("N"), All("r", Field("N"), All("s", States(n), All("K", Kraus(n, r),
            Eqn(Call("zeroFidelity", s, ks), value))))));
    }
    private static Formula ProcessFormula()
    {
        Formula n = F.Id("n"), r = F.Id("r"), ks = F.Id("K"), v = Call("maxEntangledVector", Reg(n));
        Formula value = Call("real", Call("inner", v,
            Call("mulVec", Call("kraus", Call("liftKraus", ks), Call("maxEntangled", Reg(n))), v)));
        return Disp(All("n", Field("N"), All("r", Field("N"), All("K", Kraus(n, r),
            Eqn(Call("processFidelity", ks), value)))));
    }
    private static Formula SupportFormula()
    {
        Formula n = F.Id("n"), r = F.Id("r"), ks = F.Id("K"), j = F.Id("j"), b = F.Id("b");
        Formula support = All("j", Call("Fin", r), All("b", Arrow(Call("Fin", n), Named("Pauli")),
            Imp(Le(D(2), Weight(b)), Eqn(Call("trace", Mul(Call("adjoint", Call("wordOp", b)), At(ks, j))), D(0)))));
        return Disp(All("n", Field("N"), All("r", Field("N"), All("K", Kraus(n, r),
            Iff(Call("HasWeightOneSupport", ks), support)))));
    }
    private static Formula CovarianceFormula()
    {
        Formula n = F.Id("n"), s = F.Id("s"), k = F.Id("k"), b = F.Id("b"), c = F.Id("c");
        Formula wordType = Arrow(Call("Fin", n), Named("Pauli"));
        Formula p = Call("rankOneDensity", Call("productState", s, k));
        Formula lhs = SumAt("k", Arrow(Call("Fin", n), Fin(4)),
            Mul(Call("trace", Mul(p, Call("wordOp", b))), Call("trace", Mul(p, Call("wordOp", c)))));
        Formula rhs = Mul(Call("indicator", Eqn(b, c)), Mul(new Formula.Power(D(4), n),
            new Formula.Power(new Formula.Fraction(D(1), D(3)), Weight(b))));
        Formula local = All("i", Call("Fin", n), Call("IsQubitSIC", At(s, F.Id("i"))));
        return Disp(All("n", Field("N"), All("s", States(n), Imp(local,
            All("b", wordType, All("c", wordType, Eqn(lhs, rhs)))))));
    }
    private static Formula ParsevalFormula()
    {
        Formula n = F.Id("n"), s = F.Id("s"), a = F.Id("A"), k = F.Id("k"), b = F.Id("b");
        Formula lhs = SumAt("k", Arrow(Call("Fin", n), Fin(4)),
            new Formula.Power(new Formula.Norm(Call("trace", Mul(Call("rankOneDensity", Call("productState", s, k)), a))), D(2)));
        Formula rhs = SumAt("b", Arrow(Call("Fin", n), Named("Pauli")),
            Mul(new Formula.Power(new Formula.Fraction(D(1), D(3)), Weight(b)),
                new Formula.Power(new Formula.Norm(Call("trace", Mul(Call("wordOp", b), a))), D(2))));
        Formula local = All("i", Call("Fin", n), Call("IsQubitSIC", At(s, F.Id("i"))));
        return Disp(All("n", Field("N"), All("s", States(n), Imp(local, All("A", Mat(n), Eqn(lhs, rhs))))));
    }
    private static Formula WordType(Formula n) => Arrow(Call("Fin", n), Named("Pauli"));
    private static Formula SqNorm(Formula x) => new Formula.Power(new Formula.Norm(x), D(2));
    private static Formula InvDimSq(Formula n) => new Formula.Fraction(D(1), new Formula.Power(Dim(n), D(2)));
    private static Formula Coeff(Formula ks, Formula b, Formula j) =>
        Call("trace", Mul(Call("wordOp", b), At(ks, j)));
    private static Formula Prob(Formula n, Formula r, Formula ks, Formula b) =>
        Mul(InvDimSq(n), SumAt("j", Call("Fin", r), SqNorm(Coeff(ks, b, F.Id("j")))));
    private static Formula Weight(Formula b) => Call("hammingDist", b,
        Seq(LambdaLower, Sp, F.Id("i"), Sp, Mapsto, Sp, Named("I")));
    private static Formula Moment(Formula b) => new Formula.Power(new Formula.Fraction(D(1), D(3)), Weight(b));
    private static Formula LocalSic(Formula n, Formula s) => All("i", Call("Fin", n), Call("IsQubitSIC", At(s, F.Id("i"))));
    private static Formula SurvivalFormula()
    {
        Formula a = F.Id("a"), r = F.Id("r"), v = F.Id("v"), ks = F.Id("K");
        Formula mat = Call("Matrix", a, a, Field("C"));
        Formula lhs = Call("real", Call("inner", v, Call("mulVec", Call("kraus", ks, Call("rankOneDensity", v)), v)));
        Formula rhs = SumAt("j", Call("Fin", r), SqNorm(Call("inner", v, Call("mulVec", At(ks, F.Id("j")), v))));
        return Disp(All("a", Named("finiteSet"), All("r", Field("N"), All("v", Arrow(a, Field("C")),
            All("K", Arrow(Call("Fin", r), mat), Eqn(lhs, rhs))))));
    }
    private static Formula BellAmplitudeFormula()
    {
        Formula n = F.Id("n"), a = F.Id("A"), v = Call("maxEntangledVector", Reg(n));
        Formula lhs = Call("inner", v, Call("mulVec", Call("tensor", D(1), a), v));
        return Disp(All("n", Field("N"), All("A", Mat(n), Eqn(lhs,
            new Formula.Fraction(Call("trace", a), Dim(n))))));
    }
    private static Formula MassFormula()
    {
        Formula n = F.Id("n"), r = F.Id("r"), ks = F.Id("K"), b = F.Id("b");
        return Disp(All("n", Field("N"), All("r", Field("N"), All("K", Kraus(n, r),
            Imp(TracePreserving(r, ks), Eqn(SumAt("b", WordType(n), Prob(n, r, ks, b)), D(1)))))));
    }
    private static Formula WeightBoundFormula()
    {
        Formula n = F.Id("n"), q = F.Id("q"), b = F.Id("b");
        Formula p = At(q, Call("identityWord", n));
        Formula z = SumAt("b", WordType(n), Mul(Moment(b), At(q, b)));
        Formula nonneg = All("b", WordType(n), Le(D(0), At(q, b)));
        Formula mass = Eqn(SumAt("b", WordType(n), At(q, b)), D(1));
        Formula support = All("b", WordType(n), Imp(Le(D(2), Weight(b)), Eqn(At(q, b), D(0))));
        return Disp(All("n", Field("N"), All("q", Arrow(WordType(n), Field("R")),
            Imp(And(nonneg, mass), And(Le(Lower(z), p), Iff(Eqn(p, Lower(z)), support))))));
    }
    private static Formula ProcessTraceFormula()
    {
        Formula n = F.Id("n"), r = F.Id("r"), ks = F.Id("K");
        Formula rhs = Mul(InvDimSq(n), SumAt("j", Call("Fin", r), SqNorm(Call("trace", At(ks, F.Id("j"))))));
        return Disp(All("n", Field("N"), All("r", Field("N"), All("K", Kraus(n, r),
            Eqn(Call("processFidelity", ks), rhs)))));
    }
    private static Formula ZeroTraceFormula()
    {
        Formula n = F.Id("n"), r = F.Id("r"), s = F.Id("s"), ks = F.Id("K"), b = F.Id("b");
        Formula rhs = SumAt("b", WordType(n), Mul(Moment(b), Prob(n, r, ks, b)));
        return Disp(All("n", Field("N"), All("r", Field("N"), All("s", States(n),
            Imp(LocalSic(n, s), All("K", Kraus(n, r), Eqn(Call("zeroFidelity", s, ks), rhs)))))));
    }
    private static Formula BoundFormula(bool equality)
    {
        Formula n = F.Id("n"), r = F.Id("r"), s = F.Id("s"), ks = F.Id("K");
        Formula z = Call("zeroFidelity", s, ks), p = Call("processFidelity", ks);
        Formula body = Le(Lower(z), p);
        if (equality) body = And(body, Iff(Eqn(p, Lower(z)), Call("HasWeightOneSupport", ks)));
        return Disp(All("n", Field("N"), All("r", Field("N"), All("s", States(n),
            Imp(LocalSic(n, s), All("K", Kraus(n, r), Imp(TracePreserving(r, ks), body)))))));
    }
    private static Formula TightFormula()
    {
        Formula n = F.Id("n"), r = F.Id("r"), s = F.Id("s"), ks = F.Id("K"), f = F.Id("f");
        Formula witness = Exists("r", Field("N"), Exists("K", Kraus(n, r),
            And(TracePreserving(r, ks), And(Eqn(Call("zeroFidelity", s, ks), f),
                Eqn(Call("processFidelity", ks), Lower(f))))));
        return Disp(All("n", Field("N"), Imp(Le(D(1), n), All("s", States(n), Imp(LocalSic(n, s),
            All("f", Field("R"), Imp(Le(new Formula.Fraction(D(1), D(3)), f), Imp(Le(f, D(1)), witness))))))));
    }
    private static Formula TracePreserving(Formula r, Formula ks) =>
        Eqn(SumAt("j", Call("Fin", r), Mul(Call("adjoint", At(ks, F.Id("j"))), At(ks, F.Id("j")))), D(1));
    private static Formula ClaimBody()
    {
        Formula n = F.Id("n"), r = F.Id("r"), s = F.Id("s"), ks = F.Id("K"), f = F.Id("f");
        Formula z = Call("zeroFidelity", s, ks), p = Call("processFidelity", ks);
        Formula bounds = All("r", Field("N"), All("K", Kraus(n, r), Imp(TracePreserving(r, ks),
            And(Le(Lower(z), p), Iff(Eqn(p, Lower(z)), Call("HasWeightOneSupport", ks))))));
        Formula tight = All("f", Field("R"), Imp(Le(new Formula.Fraction(D(1), D(3)), f), Imp(Le(f, D(1)),
            Exists("r", Field("N"), Exists("K", Kraus(n, r), And(TracePreserving(r, ks), And(Eqn(z, f), Eqn(p, Lower(f)))))))));
        Formula local = All("i", Call("Fin", n), Call("IsQubitSIC", At(s, F.Id("i"))));
        return All("n", Field("N"), Imp(Le(D(1), n), All("s", States(n), Imp(local, And(bounds, tight)))));
    }
}

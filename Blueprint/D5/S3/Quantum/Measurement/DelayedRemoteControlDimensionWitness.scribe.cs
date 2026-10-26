using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class DelayedRemoteControlDimensionWitnessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/DelayedRemoteControlDimensionWitness.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/lin2026rcqc");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every Euclidean-unit complex data qubit admits positive preparations and a delayed remote-control dimension witness greater than four.",
        H("A dimension witness for delayed remote control"),
        Blocks(
            Node("gate-a", "The controlled-A data gate", "gateA", GateFormula(true),
                "Equation (3) gives the diagonal data gate A in the computational basis. Both parameters are real, and the exponential is complex.",
                AssessedProvenance.FromLiterature(Source)),
            Node("gate-b", "The controlled-B data gate", "gateB", GateFormula(false),
                "Equation (3) gives the data gate B in the computational basis. Its upper-right entry is minus one, and its lower-left entry has phase beta minus delta.",
                AssessedProvenance.FromLiterature(Source)),
            Node("circuit-state", "The three-qubit circuit state", "circuitState", CircuitFormula(),
                "The coordinates have the order program, data, remote control. The Bell vector is on the program and remote-control qubits. The two conditional terms are the entries of the controlled gate |0⟩⟨0| tensor A plus |1⟩⟨1| tensor B on the program and data qubits. The outer sum applies the Hadamard to the program qubit, as in Figure 3. All three sums range over Fin 2.",
                AssessedProvenance.FromLiterature(Source)),
            Node("remote", "The remote outcome-zero vector", "remote", RemoteFormula(),
                "The two entries are the complex conjugates of the coefficients in Equation (3), with the global phase alpha equal to zero. The same beta and delta occur in the gates and in this vector. Its projector and complementary projector give the binary remote measurement.",
                AssessedProvenance.FromLiterature(Source)),
            Node("data-projector", "The data measurement operators", "dataProjector", DataProjectorFormula(),
                "Outcome zero is the outer product of b with its complex conjugate, and outcome one is the identity matrix minus that outer product. For a Euclidean-unit b these are the two orthogonal projectors of the data measurement in Figure 3. The definition itself accepts every complex vector b.",
                AssessedProvenance.FromLiterature(Source)),
            Node("prep-prob", "The preparation probability", "prepProb", PreparationFormula(),
                "The preparation label is x = 2m + n. The program outcome m is the integer quotient of Fin.val x by two, and the data outcome n is its remainder modulo two; both are interpreted as elements of Fin 2. The data projection is applied before summing Complex.normSq over the remaining remote and data coordinates. For unit d and b, this is the Born-rule probability of the program and data outcomes together.",
                AssessedProvenance.FromLiterature(Source)),
            Node("joint-prob", "The joint outcome-zero probability", "jointProb", JointFormula(),
                "At remote setting y, gamma is gamma zero when y is zero and gamma one otherwise. Taking the inner product with the remote outcome-zero vector gives a sum over the remote coordinate. Complex.normSq is then summed over the data coordinate. The program and data outcomes use the same integer quotient and remainder as the preparation probability. For unit d and b, this is their joint Born-rule probability together with remote outcome zero.",
                AssessedProvenance.FromLiterature(Source)),
            Node("e", "The binary correlator", "E", CorrelatorFormula(),
                "When the preparation probability is positive, the quotient is the conditional probability of remote outcome zero. Twice this probability minus one is the difference between the two binary outcome probabilities. The real division in the definition is total, so the formula also defines a value at zero preparation probability.",
                AssessedProvenance.FromLiterature(Source)),
            Node("s", "The dimension-witness expression", "S", WitnessFormula(),
                "This is the eight-term expression of Equation (2), using the source's first preparation labeling x = 2m + n. The signs are plus, minus, minus, plus, minus, minus, plus, plus in the order (0,0), (0,1), (1,0), (1,1), (2,0), (2,1), (3,0), (3,1). The expression is defined without imposing the classical bound of four.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "A violation for every pure data qubit", "claim", ClaimFormula(),
                "The final paragraph of Section III conjectures a violation for every initial pure data qubit. Here the norm is the Euclidean norm on complex coordinate functions, obtained with WithLp.toLp 2. For each unit data vector, the four real parameters and a unit data-measurement vector may be chosen separately. Every preparation must have positive probability, and S must exceed four. The labeling is fixed to x = 2m + n.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("delayed-rcqc-unit-coordinates"),
                DeclarationHandle.Create(Prefix + "unit_coordinates"),
                H("Normalization in two coordinates"),
                StatementSource.FromAuthor(Disp(All(X("d"), VectorType(),
                    Implies(Equal(EuclideanNorm(X("d")), D(1)),
                        Equal(Add(NormSquared(At(X("d"), D(0))),
                            NormSquared(At(X("d"), D(1)))), D(1)))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The squared moduli of the two coordinates of a Euclidean-unit complex qubit sum to one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("delayed-rcqc-result"), DeclarationHandle.Create(Prefix + "result"),
                H("Every pure data qubit admits the violation"),
                StatementSource.FromAuthor(Disp(Local("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For a Euclidean-unit data vector d, choose β = 0, δ = −arg(conj(d₀)·d₁), γ₀ = π/2 and γ₁ = π. The vectors A d and e^{iδ} B d are orthonormal, including when either coordinate of d vanishes. Take b = cos(π/8)·A d + sin(π/8)·e^{iδ} B d. This vector is Euclidean-unit. Every preparation then has probability 1/4. In the order (0,0), (0,1), (1,0), (1,1), (2,0), (2,1), (3,0), (3,1), the correlators are √2/2 times the signs plus, minus, minus, plus, minus, minus, plus, plus. Consequently S = 4√2 > 4 for every pure data qubit."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("lin-wang-liu-huang-2026-delayed-rcqc-dimension-witness"),
                    ResolutionKind.Proved))
        )));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("delayed-rcqc-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula X(string name) => F.Id(name);
    private static Formula Qualified(params string[] names)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var name in names)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(X(name));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Local(string name) =>
        Qualified("D5", "S3", "Quantum", "Measurement", "DelayedRemoteControlDimensionWitness", name);
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula LocalCall(string name, params Formula[] arguments) => At(Local(name), arguments);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Reals() => Seq(Mathbb, Grp(X("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(X("C")));
    private static Formula Fin(byte size) => At(Qualified("Fin"), D(size));
    private static Formula VectorType() => Parenthesized(new Formula.TypeArrow(Fin(2), Complexes()));
    private static Formula MatrixType() => At(Qualified("Matrix"), Fin(2), Fin(2), Complexes());
    private static Formula TripleType() => Parenthesized(Seq(Fin(2), Sp, Times, Sp,
        Parenthesized(Seq(Fin(2), Sp, Times, Sp, Fin(2)))));
    private static Formula First(Formula value) => Seq(Parenthesized(value), Dot, D(1));
    private static Formula Second(Formula value) => Seq(Parenthesized(value), Dot, D(2));
    private static Formula Pair(Formula left, Formula right) => Parenthesized(Seq(left, Comma, Sp, right));
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(variable, type), Comma, Sp, body);
    private static Formula Some(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(variable, type), Comma, Sp, body);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Equivalent(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Fraction(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
    private static Formula Negate(Formula value) => new Formula.Negate(Parenthesized(value));
    private static Formula OfReal(Formula value) => At(Qualified("Complex", "ofReal"), value);
    private static Formula Conjugate(Formula value) => At(Qualified("starRingEnd"), Complexes(), value);
    private static Formula ComplexExponential(Formula angle) =>
        At(Qualified("Complex", "exp"), Multiply(OfReal(angle), Qualified("Complex", "I")));
    private static Formula NormSquared(Formula value) => At(Qualified("Complex", "normSq"), value);
    private static Formula EuclideanNorm(Formula value) => new Formula.Norm(Typed(
        At(Qualified("WithLp", "toLp"), D(2), value),
        At(Qualified("EuclideanSpace"), Complexes(), Fin(2))));
    private static Formula GammaSetting(byte setting) => new Formula.Subscript(GammaLower, D(setting));
    private static Formula SumOver(string variable, Formula body) => Seq(
        new Formula.Subscript(Sum, Typed(X(variable), Fin(2))), Sp, Parenthesized(body));
    private static Formula IfThenElse(Formula condition, Formula yes, Formula no) => Parenthesized(Seq(
        F.Text, Grp(X("if")), Sp, Parenthesized(condition), Sp, F.Text, Grp(X("then")), Sp,
        Parenthesized(yes), Sp, F.Text, Grp(X("else")), Sp, Parenthesized(no)));
    private static Formula MatrixTwo(Formula a, Formula b, Formula c, Formula d) => Seq(
        Begin, Grp(X("pmatrix")), a, Amp, b, RowBreak, c, Amp, d, End, Grp(X("pmatrix")));
    private static Formula ColumnTwo(Formula a, Formula b) => Seq(
        Begin, Grp(X("pmatrix")), a, RowBreak, b, End, Grp(X("pmatrix")));

    private static Formula GateFormula(bool a)
    {
        Formula matrix = a
            ? MatrixTwo(D(1), D(0), D(0), ComplexExponential(Add(Beta, DeltaLower)))
            : MatrixTwo(D(0), Negate(D(1)), ComplexExponential(Subtract(Beta, DeltaLower)), D(0));
        return All(Beta, Reals(), All(DeltaLower, Reals(),
            Equal(LocalCall(a ? "gateA" : "gateB", Beta, DeltaLower), matrix)));
    }

    private static Formula CircuitFormula()
    {
        Formula p = X("p"), q = X("q"), j = X("j"), k = X("k");
        Formula entry = Add(
            Multiply(IfThenElse(And(Equal(p, D(0)), Equal(q, D(0))), D(1), D(0)),
                LocalCall("gateA", Beta, DeltaLower, First(Second(k)), j)),
            Multiply(IfThenElse(And(Equal(p, D(1)), Equal(q, D(1))), D(1), D(0)),
                LocalCall("gateB", Beta, DeltaLower, First(Second(k)), j)));
        Formula bell = At(Qualified("D5", "S3", "QuantumBounds", "CHSHWitness", "bellVector"),
            Pair(q, Second(Second(k))));
        Formula hadamard = At(Qualified("D5", "S3", "Quantum", "Information",
            "BinaryStabilizerLocalInequivalence", "hadamard"), First(k), p);
        Formula sum = SumOver("p", Multiply(hadamard,
            Parenthesized(SumOver("q", SumOver("j", Multiply(Multiply(Parenthesized(entry), bell), At(X("d"), j)))))));
        return All(X("d"), VectorType(), All(Beta, Reals(), All(DeltaLower, Reals(), All(k, TripleType(),
            Equal(LocalCall("circuitState", X("d"), Beta, DeltaLower, k), sum)))));
    }

    private static Formula RemoteFormula()
    {
        Formula first = Conjugate(Multiply(ComplexExponential(Fraction(Negate(Add(Beta, DeltaLower)), D(2))),
            OfReal(At(Qualified("Real", "cos"), Fraction(GammaLower, D(2))))));
        Formula second = Conjugate(Multiply(ComplexExponential(Fraction(Negate(Subtract(Beta, DeltaLower)), D(2))),
            OfReal(At(Qualified("Real", "sin"), Fraction(GammaLower, D(2))))));
        return All(Beta, Reals(), All(DeltaLower, Reals(), All(GammaLower, Reals(),
            Equal(LocalCall("remote", Beta, DeltaLower, GammaLower), ColumnTwo(first, second)))));
    }

    private static Formula DataProjectorFormula()
    {
        Formula outer = At(Qualified("Matrix", "vecMulVec"), X("b"), At(Qualified("star"), X("b")));
        return All(X("b"), VectorType(), All(X("n"), Fin(2), Equal(LocalCall("dataProjector", X("b"), X("n")),
            IfThenElse(Equal(X("n"), D(0)), outer, Subtract(Typed(D(1), MatrixType()), outer)))));
    }

    private static Formula DataProjectedAmplitude()
    {
        Formula value = At(Qualified("Fin", "val"), X("x"));
        Formula program = new Formula.Floor(Fraction(value, D(2)));
        Formula outcome = new Formula.Modulo(value, D(2));
        return SumOver("j", Multiply(LocalCall("dataProjector", X("b"), outcome, X("i"), X("j")),
            LocalCall("circuitState", X("d"), Beta, DeltaLower, Pair(program, Pair(X("j"), X("r"))))));
    }

    private static Formula PreparationFormula() => All(X("d"), VectorType(), All(Beta, Reals(),
        All(DeltaLower, Reals(), All(X("b"), VectorType(), All(X("x"), Fin(4),
            Equal(LocalCall("prepProb", X("d"), Beta, DeltaLower, X("b"), X("x")),
                SumOver("r", SumOver("i", NormSquared(DataProjectedAmplitude())))))))));

    private static Formula JointFormula()
    {
        Formula angle = IfThenElse(Equal(X("y"), D(0)), GammaSetting(0), GammaSetting(1));
        Formula amplitude = SumOver("r", Multiply(Conjugate(LocalCall("remote", Beta, DeltaLower, angle, X("r"))),
            Parenthesized(DataProjectedAmplitude())));
        return ProbabilityBinders(Equal(
            LocalCall("jointProb", X("d"), Beta, DeltaLower, GammaSetting(0), GammaSetting(1), X("b"), X("x"), X("y")),
            SumOver("i", NormSquared(amplitude))), true);
    }

    private static Formula ProbabilityBinders(Formula body, bool outcomes) =>
        All(X("d"), VectorType(), All(Beta, Reals(), All(DeltaLower, Reals(),
            All(GammaSetting(0), Reals(), All(GammaSetting(1), Reals(), All(X("b"), VectorType(),
                outcomes ? All(X("x"), Fin(4), All(X("y"), Fin(2), body)) : body))))));

    private static Formula CorrelatorFormula() => ProbabilityBinders(Equal(
        LocalCall("E", X("d"), Beta, DeltaLower, GammaSetting(0), GammaSetting(1), X("b"), X("x"), X("y")),
        Subtract(Multiply(D(2), Parenthesized(Fraction(
            LocalCall("jointProb", X("d"), Beta, DeltaLower, GammaSetting(0), GammaSetting(1), X("b"), X("x"), X("y")),
            LocalCall("prepProb", X("d"), Beta, DeltaLower, X("b"), X("x"))))), D(1))), true);

    private static Formula WitnessFormula()
    {
        Formula Term(byte x, byte y) => LocalCall("E", X("d"), Beta, DeltaLower,
            GammaSetting(0), GammaSetting(1), X("b"), D(x), D(y));
        Formula expression = Add(Add(Subtract(Subtract(Add(Subtract(Subtract(
            Term(0, 0), Term(0, 1)), Term(1, 0)), Term(1, 1)), Term(2, 0)), Term(2, 1)), Term(3, 0)), Term(3, 1));
        return ProbabilityBinders(Equal(LocalCall("S", X("d"), Beta, DeltaLower,
            GammaSetting(0), GammaSetting(1), X("b")), expression), false);
    }

    private static Formula ClaimFormula()
    {
        Formula body = And(Equal(EuclideanNorm(X("b")), D(1)), And(
            All(X("x"), Fin(4), Less(D(0), LocalCall("prepProb", X("d"), Beta, DeltaLower, X("b"), X("x")))),
            Less(D(4), LocalCall("S", X("d"), Beta, DeltaLower, GammaSetting(0), GammaSetting(1), X("b")))));
        Formula choices = Some(Beta, Reals(), Some(DeltaLower, Reals(), Some(GammaSetting(0), Reals(),
            Some(GammaSetting(1), Reals(), Some(X("b"), VectorType(), body)))));
        return Equivalent(Local("claim"), All(X("d"), VectorType(),
            Implies(Equal(EuclideanNorm(X("d")), D(1)), choices)));
    }
}

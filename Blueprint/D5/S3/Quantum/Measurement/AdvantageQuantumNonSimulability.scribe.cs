using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class AdvantageQuantumNonSimulabilityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/AdvantageQuantumNonSimulability.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/arai2023diversity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "No binary advantage-quantum measurement admits an exact quantum simulation on any finite number of copies.",
        H("Advantage-quantum measurements cannot be simulated with finitely many copies"),
        Blocks(
            Paragraph(Text(
                "Consider two finite-dimensional complex systems and a binary measurement with effects E and I − E. "
                + "Arai's dual-operator-valued measurements have Hermitian effects that are nonnegative on every "
                + "product vector. The matrices below use Fin dA × Fin dB as the joint basis. The symbol 1 denotes "
                + "the identity matrix, and brackets on typeclasses denote anonymous assumptions.")),
            Node("binary-effect", "binaryEffect", "The two complementary effects", BinaryEffectFormula(),
                "Outcome zero has effect E and outcome one has effect I − E. Their sum is the identity, "
                + "without any positivity assumption on E."),
            Node("dovm", "IsDovm", "Hermitian effects nonnegative on product vectors", DovmFormula(),
                "Each effect is Hermitian and block positive. The displayed quadratic form tests every pair "
                + "of local vectors a and b: their product vector has coordinate a(x) b(y). Here star is "
                + "coordinatewise complex conjugation, dotProduct sums coordinate products, and mulVec is "
                + "matrix-vector multiplication. This is the dual cone of the separable cone in the thesis's "
                + "definition of a DOVM."),
            Node("least-eigenvalue", "aqLeastEigenvalue", "The infimum of the eigenvalues", EigenvalueFormula(false),
                "For a Hermitian matrix A on a finite index type, take the infimum of the range of its real "
                + "eigenvalue function. This definition also applies to an empty index type. On a nonempty "
                + "finite type the infimum is an attained least eigenvalue."),
            Node("greatest-eigenvalue", "aqGreatestEigenvalue", "The supremum of the eigenvalues", EigenvalueFormula(true),
                "The corresponding supremum defines the greatest eigenvalue. On a nonempty finite index "
                + "type it is attained. Neither extreme requires an ordering of the eigenvector indices."),
            Node("advantage-quantum", "IsAdvantageQuantum", "The advantage-quantum inequalities", AdvantageFormula(),
                "One of the two effects has a negative least eigenvalue, while its greatest eigenvalue is "
                + "strictly between one plus the least eigenvalue and one. These are exactly Arai's AQ "
                + "inequalities; hE supplies the Hermitian proof for each effect."),
            Node("measurement-domain", "InMeasurementDomain", "The density matrices with nonnegative probabilities", DomainFormula(),
                "A domain state is positive semidefinite, has complex trace equal to one, and gives a "
                + "nonnegative real trace pairing with each effect. Thus both outcome probabilities lie "
                + "between zero and one. This is the trace-one part of the thesis's domain, which also "
                + "allows unnormalized positive semidefinite matrices."),
            Node("copy-state", "copyState", "The tensor power in coordinates", CopyFormula(),
                "A basis index for n copies is a function from Fin n to the original basis. The matrix "
                + "entry of the tensor power is the product of the n corresponding entries of rho. "
                + "For zero copies the empty product gives the one-dimensional identity."),
            Node("quantum-simulable", "QuantumSimulable", "One POVM must reproduce every domain state", SimulableFormula(),
                "For the specified natural number n, there must be a binary POVM N on the n-copy space "
                + "whose real trace probabilities agree with those of the original effects for every "
                + "trace-one domain state and both outcomes. IsPOVM means that each N(i) is positive "
                + "semidefinite and their sum is the identity. The same N must work for every state."),
            Node("claim", "claim", "Finite-copy non-simulability of every AQ DOVM", ClaimFormula(),
                "For every pair of positive dimensions and every binary DOVM, the AQ condition rules out "
                + "quantum n-simulability for every natural n, including zero. This states the negative "
                + "answer to the AQ simulability question in Section 5.2 of the thesis. Requiring agreement "
                + "only on density matrices already suffices for the obstruction."),
            Describe.Lean(
                DescribeId.Create("advantage-quantum-non-simulability-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A zero probability at a full-rank state forces a contradiction"),
                StatementSource.FromAuthor(Disp(N("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Choose the AQ effect A. Every product-basis diagonal entry is nonnegative by "
                        + "block positivity, so Tr A ≥ 0. Write d = dA dB, and let lambda_1 and lambda_d "
                        + "be its least and greatest eigenvalues. Since lambda_1 < 0 and the sum of all "
                        + "eigenvalues is nonnegative, lambda_d > 0; the AQ hypothesis gives lambda_d < 1. For a unit "
                        + "top eigenvector w, the state rho_+ = |w⟩⟨w| has selected probability "
                        + "lambda_d in (0,1). Its complementary probability is 1 − lambda_d, so it "
                        + "belongs to the measurement domain.")),
                    Paragraph(Text(
                        "Let v be a unit bottom eigenvector, put a = Tr A / d ≥ 0, and set "
                        + "p = −lambda_1 / (a − lambda_1). Then 0 < p ≤ 1, and "
                        + "rho_0 = (p/d) I + (1 − p)|v⟩⟨v| is a trace-one positive definite matrix. "
                        + "Its selected probability is p a + (1 − p) lambda_1 = 0, and the "
                        + "complementary probability is one. Hence rho_0 is a full-rank domain state.")),
                    Paragraph(Text(
                        "If a POVM N simulated the measurement on n copies, its selected effect would "
                        + "satisfy Re Tr(rho_0 tensor-power n · N(i)) = 0. The tensor power of rho_0 "
                        + "is positive definite for every n, including zero. A positive semidefinite "
                        + "effect with zero trace pairing against a positive definite matrix is zero, "
                        + "so N(i) = 0. Its probability on rho_+ tensor-power n would then be zero, "
                        + "contradicting the required value lambda_d > 0. This proves claim. "
                        + "The argument uses the negative least eigenvalue and the greatest eigenvalue "
                        + "being below one; it does not need the additional AQ inequality "
                        + "1 + lambda_1 < lambda_d."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, Formula formula,
        string prose) => Describe.Lean(
            DescribeId.Create("advantage-quantum-non-simulability-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula N(string name) => new Formula.Symbol(FormulaIdentifier.Create(name));
    private static Formula Q(string name)
    {
        var parts = new System.Collections.Generic.List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (parts.Count > 0) parts.Add(Dot);
            parts.Add(Operatorname);
            parts.Add(Grp(N(part)));
        }
        return Seq([.. parts]);
    }
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => At(Q(name), arguments);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, type));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Instance(Formula type, Formula body) => Seq(OpenBracket, type, CloseBracket, Comma, Sp, body);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula IffFormula(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula Fin(Formula size) => Call("Fin", size);
    private static Formula Joint => Call("Prod", Fin(N("dA")), Fin(N("dB")));
    private static Formula Mat(Formula carrier) => Call("Matrix", carrier, carrier, N("Complex"));
    private static Formula Copies => Arrow(Fin(N("n")), Joint);
    private static Formula Dimensions(Formula body) => All("dA", N("Nat"), All("dB", N("Nat"), body));
    private static Formula Effect => Call("binaryEffect", N("E"), N("i"));
    private static Formula RealPart(Formula value) => Call("Complex.re", value);
    private static Formula Probability(Formula state, Formula effect) => RealPart(Call("Matrix.trace", Mul(state, effect)));
    private static Formula HermitianProof => Call("And.left", At(N("hE"), N("i")));
    private static Formula Least => Call("aqLeastEigenvalue", HermitianProof);
    private static Formula Greatest => Call("aqGreatestEigenvalue", HermitianProof);
    private static Formula ProductVector => Seq(Typed(N("j"), Joint), Sp, Mapsto, Sp,
        Mul(At(N("a"), Call("Prod.fst", N("j"))), At(N("b"), Call("Prod.snd", N("j")))));

    private static Formula BinaryEffectFormula() => Dimensions(All("E", Mat(Joint), All("i", Fin(D(2)),
        Equal(Effect, At(Seq(Bang, OpenBracket, N("E"), Comma, Sp, Sub(D(1), N("E")), CloseBracket), N("i"))))));

    private static Formula DovmFormula() => Dimensions(All("E", Mat(Joint),
        IffFormula(Call("IsDovm", N("E")), All("i", Fin(D(2)),
            And(Call("Matrix.IsHermitian", Effect),
                All("a", Arrow(Fin(N("dA")), N("Complex")),
                    All("b", Arrow(Fin(N("dB")), N("Complex")),
                        Le(D(0), RealPart(Call("dotProduct", Call("star", ProductVector),
                            Call("Matrix.mulVec", Effect, ProductVector)))))))))));

    private static Formula EigenvalueFormula(bool greatest) => All("I", N("Type"),
        Instance(Call("Fintype", N("I")), Instance(Call("DecidableEq", N("I")),
            All("A", Mat(N("I")), All("hA", Call("Matrix.IsHermitian", N("A")),
                Equal(Call(greatest ? "aqGreatestEigenvalue" : "aqLeastEigenvalue", N("hA")),
                    Call(greatest ? "sSup" : "sInf", Call("Set.range", Call("Matrix.IsHermitian.eigenvalues", N("hA"))))))))));

    private static Formula AdvantageFormula() => Dimensions(All("E", Mat(Joint),
        All("hE", Call("IsDovm", N("E")), IffFormula(Call("IsAdvantageQuantum", N("E"), N("hE")),
            Some("i", Fin(D(2)), And(Less(Least, D(0)),
                And(Less(Add(D(1), Least), Greatest), Less(Greatest, D(1)))))))));

    private static Formula DomainFormula() => Dimensions(All("E", Mat(Joint), All("rho", Mat(Joint),
        IffFormula(Call("InMeasurementDomain", N("E"), N("rho")),
            And(Call("Matrix.PosSemidef", N("rho")), And(Equal(Call("Matrix.trace", N("rho")), D(1)),
                All("i", Fin(D(2)), Le(D(0), Probability(N("rho"), Effect)))))))));

    private static Formula CopyFormula() => All("I", N("Type"),
        All("n", N("Nat"), All("rho", Mat(N("I")),
            All("x", Arrow(Fin(N("n")), N("I")), All("y", Arrow(Fin(N("n")), N("I")),
                Equal(At(Call("copyState", N("n"), N("rho")), N("x"), N("y")),
                    Seq(new Formula.Subscript(Prod, Typed(N("k"), Fin(N("n")))),
                        Parenthesized(At(N("rho"), At(N("x"), N("k")), At(N("y"), N("k")))))))))));

    private static Formula SimulableFormula() => Dimensions(All("E", Mat(Joint), All("n", N("Nat"),
        IffFormula(Call("QuantumSimulable", N("E"), N("n")),
            Some("N", Arrow(Fin(D(2)), Mat(Copies)), And(Call("IsPOVM", N("N")),
                All("rho", Mat(Joint), Imp(Call("InMeasurementDomain", N("E"), N("rho")),
                    All("i", Fin(D(2)), Equal(Probability(Call("copyState", N("n"), N("rho")), At(N("N"), N("i"))),
                        Probability(N("rho"), Effect)))))))))));

    private static Formula ClaimFormula() => IffFormula(N("claim"), Dimensions(
        Imp(Le(D(1), N("dA")), Imp(Le(D(1), N("dB")), All("E", Mat(Joint),
            All("hE", Call("IsDovm", N("E")), Imp(Call("IsAdvantageQuantum", N("E"), N("hE")),
                All("n", N("Nat"), new Formula.Not(Parenthesized(Call("QuantumSimulable", N("E"), N("n"))))))))))));
}

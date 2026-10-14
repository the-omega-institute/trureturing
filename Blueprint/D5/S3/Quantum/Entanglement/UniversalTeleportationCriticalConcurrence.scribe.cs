using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class UniversalTeleportationCriticalConcurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/UniversalTeleportationCriticalConcurrence.";
    private const string Owner = "D5.S3.Quantum.Entanglement.UniversalTeleportationCriticalConcurrence";
    private const string Companion = "D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction";
    private const string KrausOwner = "D5.S3.QuantumChannels.SwitchUselessConcatenationRefutation";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/ghosal2021qubitchannelsteleportation");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every pure two-qubit input sqrt(a)|00> + sqrt(1 - a)|11> with 1/2 < a < 1, a qubit channel acting on Bob can make the shared state useful for universal quantum teleportation exactly when its initial concurrence exceeds sqrt(5 - 2 sqrt(3))/3. Necessity holds for every finite Kraus family, and a non-unital amplitude-damping channel attains sufficiency.",
        H("The exact critical concurrence for universal quantum teleportation"),
        Blocks(
            Node("psi", "The initial pure vector", PsiFormula(),
                "Section V uses the vector sqrt(a)|00> + sqrt(1 - a)|11>. Alice is the first qubit and Bob the second. Its only nonzero coordinates for 0 < a < 1 are sqrt(a) at (0, 0) and sqrt(1 - a) at (1, 1), viewed as complex numbers. The definition is given for every real a using Real.sqrt.",
                "psi", DescribeRole.Definition),
            Node("initial", "The initial two-qubit operator", InitialFormula(),
                "The initial operator is D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity applied to psi(a), the outer product |psi(a)><psi(a)| with pointwise complex conjugation. For 0 <= a <= 1 this is a rank-one density matrix.",
                "initial", DescribeRole.Definition),
            Node("non-unital", "Failure to preserve the identity", NonUnitalFormula(),
                "The Kraus family is non-unital when the sum of K_k K_k adjoint differs from the identity. Thus its action on the identity does not return the identity.",
                "NonUnital", DescribeRole.Definition),
            Node("out", "Sending Bob's qubit through the channel", OutFormula(),
                "Bob's channel acts on the second tensor factor. D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus is applied to two copies of the family k maps to I tensor K_k and then to the initial operator. Its action is the sum of conjugations by that family, with Matrix.kronecker denoting the tensor product of matrices.",
                "out", DescribeRole.Definition),
            Node("useful-uqt", "Usefulness for universal quantum teleportation", UsefulUQTFormula(),
                "There are local unitaries U and V and a real t > 1/3 for which the conjugated operator has correlation matrix -t I, with zero off-diagonal entries. The correlation matrix is D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.corr, whose entries are the real parts of tr(rho (sigma_i tensor sigma_j)). For two-qubit states this is the source's Section II.C criterion |t11| = |t22| = |t33| > 1/3 in the canonical form of Section II.B, Eq. (3), with lambda_k = -1. The displayed definition permits any complex two-qubit operator rho.",
                "UsefulUQT", DescribeRole.Definition),
            Node("cstar", "The critical concurrence", CstarFormula(),
                "The exact threshold is sqrt(5 - 2 sqrt(3))/3 = sqrt((2/3)(4 + sqrt(3))(1 - (4 + sqrt(3))/6)), approximately 0.4131. The latter radical is the sufficient threshold after Eq. (50) in Section V.2; the source rounds it to 0.41.",
                "Cstar", DescribeRole.Definition),
            Node("conc", "Concurrence of the input vector", ConcFormula(),
                "Section V gives the initial pure-state concurrence as 2 sqrt(a(1 - a)). The function is defined for every real a; on 1/2 < a < 1 its value is strictly between zero and one.",
                "conc", DescribeRole.Definition),
            Node("claim", "The exact threshold statement", ClaimFormula(),
                "For each 1/2 < a < 1, every finite Kraus channel producing a useful universal-teleportation state requires concurrence strictly above Cstar. Conversely, above Cstar there is a non-unital finite Kraus channel producing such a state. This gives the precise critical value sought in Section V.2, Conjecture 1, using the source's exact radical.",
                "claim", DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ghosal-uqt-result"), DeclarationHandle.Create(Prefix + "result"),
                H("Necessity and non-unital attainment"), StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Put r = 2a - 1, so the squared initial concurrence is 1 - r squared. Bob's trace-preserving channel leaves Alice's marginal unchanged, and local unitaries preserve the length r of Alice's Bloch vector. In a frame with correlation matrix -t I, let n be the unit direction of Alice's Bloch vector and beta Bob's Bloch component along n. Positivity of the corner on the two negative spin projections gives r + beta <= 1 - t. Cauchy-Schwarz for the positive trace form, applied to the opposite spin projections and their product with the swap matrix, gives (r - beta) squared <= (1 - t)(1 + 3t). Eliminating beta yields r squared + rt + t squared <= r + t. Since t > 1/3, this forces r < (1 + sqrt(3))/3 and hence concurrence strictly greater than Cstar.")),
                    Paragraph(Text(
                    "For sufficiency take t = (1 - r + sqrt((1 - r)(1 + 3r)))/2 and gamma = (1 - t)/(1 + r). Above the concurrence threshold one has 1/3 < t < 1 and gamma > 0. The amplitude-damping Kraus pair K_0 = diag(sqrt(1 - gamma), 1), K_1 = sqrt(gamma)|1><0| is trace preserving and non-unital. The identity t squared = (1 - r)(t + r) gives output correlation matrix diag(t, -t, t); conjugating Bob by sigma_y changes it to -t I. Thus the exact threshold is sqrt(5 - 2 sqrt(3))/3, with strict inequality required for usefulness."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("ghosal-das-banerjee-2021-critical-concurrence-universal-teleportation"),
                    ResolutionKind.Proved))
        ),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create("ghosal-uqt-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Qualified(params string[] parts)
    {
        Formula result = Seq(Operatorname, Grp(F.Id(parts[0])));
        for (var i = 1; i < parts.Length; i++)
            result = Seq(result, Dot, Operatorname, Grp(F.Id(parts[i])));
        return result;
    }

    private static Formula QCall(string owner, string name, params Formula[] arguments) =>
        new Formula.Apply(Qualified([.. owner.Split('.'), name]), [.. arguments]);
    private static Formula Local(string name, params Formula[] arguments) =>
        arguments.Length == 0 ? Qualified([.. Owner.Split('.'), name]) : QCall(Owner, name, arguments);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula LessThan(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.LessThan, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula And(params Formula[] clauses)
    {
        Formula body = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--)
            body = new Formula.Logic(Parenthesized(clauses[i]), FormulaLogicOperator.And, Parenthesized(body));
        return body;
    }

    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Natural() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Qubits() => Parenthesized(Seq(Fin(D(2)), Sp, Times, Sp, Fin(D(2))));
    private static Formula QubitOperators() => Call("Matrix", Fin(D(2)), Fin(D(2)), Complex());
    private static Formula TwoQubitOperators() => Call("Matrix", Qubits(), Qubits(), Complex());
    private static Formula KrausFamily(Formula m) => Arrow(Fin(m), QubitOperators());
    private static Formula Pair(Formula left, Formula right) => Parenthesized(Seq(left, Comma, Sp, right));
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula SqrtOf(Formula value) => QCall("Real", "sqrt", value);
    private static Formula Adjoint(Formula matrix) => QCall("Matrix", "conjTranspose", matrix);
    private static Formula Kron(Formula left, Formula right) => QCall("Matrix", "kronecker", left, right);
    private static Formula Conjugate(Formula matrix, Formula state) =>
        Multiply(Multiply(matrix, state), Adjoint(matrix));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(Seq(F.Id(name), Colon, Sp, type)), Sp, Parenthesized(body));

    private static Formula PsiFormula()
    {
        var a = F.Id("a");
        var p = F.Id("p");
        var value = Call("ite", Equal(p, Pair(D(0), D(0))), Typed(SqrtOf(a), Complex()),
            Call("ite", Equal(p, Pair(D(1), D(1))), Typed(SqrtOf(Subtract(D(1), a)), Complex()), D(0)));
        return All("a", Real(), All("p", Qubits(), Equal(Local("psi", a, p), value)));
    }

    private static Formula InitialFormula()
    {
        var a = F.Id("a");
        var vector = Local("psi", a);
        return All("a", Real(), Equal(Local("initial", a),
            QCall("D5.S3.Quantum.PureState.PureStateHandshake", "rankOneDensity", vector)));
    }

    private static Formula NonUnitalFormula()
    {
        var m = F.Id("m");
        var k = F.Id("K");
        var entry = At(k, F.Id("k"));
        return All("m", Natural(), All("K", KrausFamily(m), Iff(Local("NonUnital", k),
            Rel(SumOver("k", Fin(m), Multiply(entry, Adjoint(entry))),
                FormulaRelationOperator.NotEqual, Typed(D(1), QubitOperators())))));
    }

    private static Formula OutFormula()
    {
        var m = F.Id("m");
        var a = F.Id("a");
        var k = F.Id("K");
        var action = Kron(Typed(D(1), QubitOperators()), At(k, F.Id("k")));
        var family = Parenthesized(Seq(LambdaLower, Sp, Typed(F.Id("k"), Fin(m)),
            Sp, Mapsto, Sp, action));
        var supplier = Seq(Qualified("D5", "S3", "Quantum", "Foundation", "FiniteKrausChannel",
            "PhyslibLeaf", "MatrixMap"), Dot, Operatorname, Grp(F.Id("of")),
            Underscore, Grp(F.Id("kraus")));
        return All("m", Natural(), All("a", Real(), All("K", KrausFamily(m), Equal(Local("out", a, k),
            new Formula.Apply(supplier, [family, family, Local("initial", a)])))));
    }

    private static Formula UsefulUQTFormula()
    {
        var rho = F.Id("rho");
        var u = F.Id("U");
        var v = F.Id("V");
        var t = F.Id("t");
        var unitary = QCall("Matrix", "unitaryGroup", Fin(D(2)), Complex());
        var isotropic = Parenthesized(Seq(LambdaLower, Sp,
            Typed(F.Id("i"), Fin(D(3))), Sp, Typed(F.Id("j"), Fin(D(3))),
            Sp, Mapsto, Sp, Call("ite", Equal(F.Id("i"), F.Id("j")), new Formula.Negate(t), D(0))));
        var condition = Some("U", QubitOperators(), Some("V", QubitOperators(), Some("t", Real(), And(
            Rel(u, FormulaRelationOperator.MemberOf, unitary),
            Rel(v, FormulaRelationOperator.MemberOf, unitary),
            LessThan(new Formula.Fraction(D(1), D(3)), t),
            Equal(QCall(Companion, "corr", Conjugate(Kron(u, v), rho)), isotropic)))));
        return All("rho", TwoQubitOperators(), Iff(Local("UsefulUQT", rho), condition));
    }

    private static Formula CstarFormula() => Equal(Local("Cstar"),
        new Formula.Fraction(SqrtOf(Subtract(D(5), Multiply(D(2), SqrtOf(D(3))))), D(3)));

    private static Formula ConcFormula()
    {
        var a = F.Id("a");
        return All("a", Real(), Equal(Local("conc", a),
            Multiply(D(2), SqrtOf(Multiply(a, Subtract(D(1), a))))));
    }

    private static Formula ClaimFormula() => Iff(Local("claim"), ClaimBody());

    private static Formula ClaimBody()
    {
        var a = F.Id("a");
        var m = F.Id("m");
        var k = F.Id("K");
        var channel = QCall(KrausOwner, "IsKrausChannel", k);
        var above = LessThan(Local("Cstar"), Local("conc", a));
        var useful = Local("UsefulUQT", Local("out", a, k));
        var necessity = All("m", Natural(), All("K", KrausFamily(m),
            Implies(channel, Implies(useful, above))));
        var attainment = Some("m", Natural(), Some("K", KrausFamily(m),
            And(channel, Local("NonUnital", k), useful)));
        return All("a", Real(), Implies(LessThan(new Formula.Fraction(D(1), D(2)), a),
            Implies(LessThan(a, D(1)), And(necessity, Implies(above, attainment)))));
    }
}

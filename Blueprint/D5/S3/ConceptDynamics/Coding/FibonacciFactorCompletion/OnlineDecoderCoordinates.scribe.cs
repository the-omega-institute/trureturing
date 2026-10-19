using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion;

internal sealed class OnlineDecoderCoordinatesDocument : IScribeDocumentDefinition
{
    private static Formula I(string name) => F.Id(name);
    private static Formula.BoundVariable B(string name, Formula type) =>
        new Formula.BoundVariable(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula body, params Formula.BoundVariable[] vars) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. vars], body);
    private static Formula Ex(Formula body, params Formula.BoundVariable[] vars) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. vars], body);
    private static Formula Ap(Formula f, Formula x) => new Formula.Apply(f, [x]);

    private static Formula Statement()
    {
        var a = I("a"); var x = I("x"); var d = I("d"); var p = I("p");
        var nat = I("Nat");
        var windows = All(Equal(Call("window", d, p), Call("labelWindow", Ap(a, p))),
            B("p", nat));
        var coordinates = All(Equal(Ap(x, p),
            Call("kappa", Call("bitShift", d,
                new Formula.Binary(D(3), FormulaBinaryOperator.Multiply, p)))), B("p", nat));
        var finiteTail = new Formula.Logic(Call("OperationFiniteSource", a),
            FormulaLogicOperator.Iff, Call("finiteTail", d));
        var conclusion = Ex(new Formula.Logic(windows, FormulaLogicOperator.And,
            new Formula.Logic(coordinates, FormulaLogicOperator.And, finiteTail)),
            B("d", I("LegalDigits")));
        return Disp(All(new Formula.Logic(Call("OperationOmega", a, x),
            FormulaLogicOperator.Implies, conclusion),
            B("a", new Formula.TypeArrow(nat, I("Label"))),
            B("x", new Formula.TypeArrow(nat, I("Real")))));
    }

    private static class BridgeDescriptions
    {
        private const string Prefix = "D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/OnlineDecoderCoordinates.";
        private static Formula I(string name) => F.Id(name);
        private static Formula.BoundVariable B(string name, Formula type) =>
            new Formula.BoundVariable(FormulaIdentifier.Create(name), type);
        private static Formula All(Formula body, params Formula.BoundVariable[] vars) =>
            new Formula.BindMany(FormulaQuantifier.ForAll, [.. vars], body);
        private static Formula Ex(Formula body, params Formula.BoundVariable[] vars) =>
            new Formula.BindMany(FormulaQuantifier.Exists, [.. vars], body);
        private static Formula And(params Formula[] clauses)
        {
            var result = clauses[^1];
            for (var i = clauses.Length - 2; i >= 0; --i)
                result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
            return result;
        }
        private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
        private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
        private static Formula Fn(Formula a, Formula b) => new Formula.TypeArrow(a, b);
        private static Formula Ap(Formula f, Formula x) => Call("apply", f, x);
        private static Formula Add(Formula a, Formula b) => Call("add", a, b);
        private static Formula Member(Formula value, Formula set) =>
            new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);
    
        private static Formula Bridge()
        {
            var nat = I("Nat"); var label = I("Label"); var guard = I("Guard");
            var real = I("Real");
            var a = I("a"); var x = I("x"); var d = I("d"); var path = I("path"); var p = I("p");
            var op = Call("OperationOmega", a, x);
            var windows = All(Equal(Call("window", d, p), Call("labelWindow", Ap(a, p))), B("p", nat));
            var guards = All(Equal(Call("actualGuard", Call("false"), d, p),
                Call("guardBool", Ap(path, p))), B("p", nat));
            var support = All(Member(Ap(x, p), Call("stateInterval", Call("guardBool", Ap(path, p)))), B("p", nat));
            var affine = All(Equal(Ap(x, p), Call("branch", Call("labelWindow", Ap(a, p)), Ap(x, Add(p, D(1))))), B("p", nat));
            var body = Ex(And(Equal(Ap(path, D(0)), I("G0")),
                All(Equal(Call("nextGuard", Ap(path, p), Ap(a, p)), Call("some", Ap(path, Add(p, D(1))))), B("p", nat)),
                windows, guards, support, affine), B("d", I("LegalDigits")), B("path", Fn(nat, guard)));
            return Disp(All(Imp(op, body), B("a", Fn(nat, label)), B("x", Fn(nat, real))));
        }
    
        private static Formula FiniteTail()
        {
            var nat = I("Nat"); var label = I("Label");
            var a = I("a"); var d = I("d"); var p = I("p");
            var windows = All(Equal(Call("window", d, p), Call("labelWindow", Ap(a, p))), B("p", nat));
            return Disp(All(Imp(windows, Iff(Call("OperationFiniteSource", a), Call("finiteTail", d))),
                B("a", Fn(nat, label)), B("d", I("LegalDigits"))));
        }
    
        public static DocumentBlock DigitBridge() =>
            Describe.Lean(DescribeId.Create("fib-online-operation-digit-bridge"),
                DeclarationHandle.Create(Prefix + "operation_digit_bridge"),
                H("Grouped legal digits and guard path"), StatementSource.FromAuthor(Bridge()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For arbitrary label and coordinate streams satisfying the original OperationOmega predicate, the declaration constructs one legal Boolean stream and a guard path. The five Coding labels are mapped to the low-to-high S1 windows 000, 010, 100, 001 and 101. The construction proves grouped window equality, the cross-block no-adjacent-one condition, agreement of the incoming guard with the previous block's highest bit, and transport of the original support interval to the S1 guard interval. It also proves the affine branch after normalizing the two definitions of the reciprocal golden ratio and the identity t cubed equals 2t minus 1.")),
                    Paragraph(Text("The declaration supplies a source correspondence and a scalar recurrence in the S1 branch model. It does not identify the supplied coordinate stream with the S1 kappa series, and it does not construct an observation record or an online decoder."))));

        public static DocumentBlock FiniteTailBridge() =>
            Describe.Lean(DescribeId.Create("fib-online-operation-finite-source-iff"),
                DeclarationHandle.Create(Prefix + "operation_finite_source_iff_of_bridge"),
                H("Finite Coding tails are finite S1 tails"), StatementSource.FromAuthor(FiniteTail()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Any legal digit stream whose grouped windows match the given label stream is eventually zero exactly when the label stream is eventually the empty-window label. The explicit window hypothesis identifies that same digit stream. Both directions use the exact three-to-one block index arithmetic; no separate coordinate or OperationOmega premise is required.")),
                    Paragraph(Text("The finite-tail statement does not assert finiteTail for arbitrary OperationOmega paths, and it does not transport OperationRecord, observe, ErrorBound or closed candidate ownership."))));
    }

    public DocumentDefinition Create()
    {
        var coordinate = Describe.Lean(DescribeId.Create("operation-coordinate-bridge"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/OnlineDecoderCoordinates.operation_coordinate_bridge"),
            H("One digit stream realizes every original coordinate"),
            StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "OperationOmega supplies a legal guard path, guard-dependent bounded coordinates, and the original affine recurrence. At each position the grouped digit window is exactly the prescribed label window. Its kappa series obeys the same recurrence, and both coordinate streams stay in the common bounded support. After n further windows, their difference equals the later difference multiplied by the nth power of negative g. The later difference has absolute value at most four; since zero is less than g and g is less than one, the initial difference is zero. This applies at every position p to the same digit stream. The explicit window equality also transfers eventual empty labels to eventual zero digits and conversely, so the coordinate and finite-tail conclusions concern that same stream.")),
                Paragraph(Text(
                    "The theorem allows every OperationOmega source, including sources that are not eventually empty. The deletion index is exactly three times p individual bits. It does not supply the converse construction from arbitrary legal digits, observation or error transport, finite certification of all closed candidates, or a streaming decoder and storage bound."))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "The supported affine coordinates of every OperationOmega source equal the series of its grouped legal digits.",
            H("Exact coordinates of grouped Fibonacci sources"),
            Blocks(BridgeDescriptions.DigitBridge(), BridgeDescriptions.FiniteTailBridge(), coordinate)));
    }
}

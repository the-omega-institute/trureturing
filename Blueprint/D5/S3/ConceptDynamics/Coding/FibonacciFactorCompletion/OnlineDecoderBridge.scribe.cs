using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion;

internal sealed class OnlineDecoderBridgeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/OnlineDecoderBridge.";
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
        var body = Ex(And(Call("LegalDigits", d), Equal(Ap(path, D(0)), I("G0")),
            All(Equal(Call("nextGuard", Ap(path, p), Ap(a, p)), Call("some", Ap(path, Add(p, D(1))))), B("p", nat)),
            windows, guards, support, affine), B("d", Call("LegalDigits")), B("path", Fn(nat, guard)));
        return Disp(All(Imp(op, body), B("a", Fn(nat, label)), B("x", Fn(nat, real))));
    }

    private static Formula FiniteTail()
    {
        var nat = I("Nat"); var label = I("Label"); var real = I("Real");
        var a = I("a"); var x = I("x"); var d = I("d"); var p = I("p");
        return Disp(All(Imp(Call("OperationOmega", a, x), Ex(Iff(Call("OperationFiniteSource", a),
            Call("finiteTail", d)), B("d", Call("LegalDigits")))), B("a", Fn(nat, label)), B("x", Fn(nat, real))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An OperationOmega path is encoded by grouped legal S1 digits.",
        H("Online decoder source correspondence"),
        Blocks(
            Describe.Lean(DescribeId.Create("fib-online-operation-digit-bridge"),
                DeclarationHandle.Create(Prefix + "operation_digit_bridge"),
                H("Grouped legal digits and guard path"), StatementSource.FromAuthor(Bridge()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For arbitrary label and coordinate streams satisfying the original OperationOmega predicate, the declaration constructs one legal Boolean stream and a guard path. The five Coding labels are mapped to the low-to-high S1 windows 000, 010, 100, 001 and 101. The construction proves grouped window equality, the cross-block no-adjacent-one condition, agreement of the incoming guard with the previous block's highest bit, and transport of the original support interval to the S1 guard interval. It also proves the affine branch after normalizing the two definitions of the reciprocal golden ratio and the identity t cubed equals 2t minus 1.")),
                    Paragraph(Text("The declaration supplies a source correspondence and a scalar recurrence in the S1 branch model. It does not identify the supplied coordinate stream with the S1 kappa series, and it does not construct an observation record or an online decoder.")))),
            Describe.Lean(DescribeId.Create("fib-online-operation-finite-source-iff"),
                DeclarationHandle.Create(Prefix + "operation_finite_source_iff_of_bridge"),
                H("Finite Coding tails are finite S1 tails"), StatementSource.FromAuthor(FiniteTail()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The canonical grouped stream is eventually zero exactly when the original label stream is eventually the empty-window label. Both directions use the exact three-to-one block index arithmetic. This result is conditional on OperationOmega so that the canonical grouped stream is legal.")),
                    Paragraph(Text("The finite-tail statement does not assert finiteTail for arbitrary OperationOmega paths, and it does not transport OperationRecord, observe, ErrorBound or closed candidate ownership.")))))));
}

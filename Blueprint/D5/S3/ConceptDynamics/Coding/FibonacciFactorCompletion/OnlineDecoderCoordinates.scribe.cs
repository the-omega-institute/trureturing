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

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The supported affine coordinates of every OperationOmega source equal the series of its grouped legal digits.",
        H("Exact coordinates of grouped Fibonacci sources"),
        Blocks(Describe.Lean(DescribeId.Create("operation-coordinate-bridge"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/OnlineDecoderCoordinates.operation_coordinate_bridge"),
            H("One digit stream realizes every original coordinate"),
            StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "OperationOmega supplies a legal guard path, guard-dependent bounded coordinates, and the original affine recurrence. At each position the grouped digit window is exactly the prescribed label window. Its kappa series obeys the same recurrence, and both coordinate streams stay in the common bounded support. After n further windows, their difference equals the later difference multiplied by the nth power of negative g. The later difference has absolute value at most four; since zero is less than g and g is less than one, the initial difference is zero. This applies at every position p to the same digit stream. The explicit window equality also transfers eventual empty labels to eventual zero digits and conversely, so the coordinate and finite-tail conclusions concern that same stream.")),
                Paragraph(Text(
                    "The theorem allows every OperationOmega source, including sources that are not eventually empty. The deletion index is exactly three times p individual bits. It does not supply the converse construction from arbitrary legal digits, observation or error transport, finite certification of all closed candidates, or a streaming decoder and storage bound.")))))));
}

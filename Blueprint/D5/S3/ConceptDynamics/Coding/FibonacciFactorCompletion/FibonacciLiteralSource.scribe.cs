using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion;

internal sealed class FibonacciLiteralSourceDocument : IScribeDocumentDefinition
{
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula And(params Formula[] clauses)
    {
        var result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; --i)
            result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula I(string name) => F.Id(name);
    private static Formula Words => Call("List", I("Label"));
    private static Formula Returns => Call("List", I("Return"));
    private static Formula Len(Formula word) => Call("length", word);
    private static Formula Coord(Formula word, Formula position) => Call("coordinate", word, position);
    private static Formula Comp(Formula word, Formula point) => Call("compose", word, point);
    private static Formula Add(Formula a, Formula b) => Call("add", a, b);
    private static Formula Sub(Formula a, Formula b) => Call("subtract", a, b);
    private static Formula Mul(Formula a, Formula b) => Call("multiply", a, b);
    private static Formula Pow(Formula a, Formula b) => Call("power", a, b);
    private static Formula Append(Formula a, Formula b) => Call("append", a, b);

    private static Formula Geometry()
    {
        var w = I("w"); var v = I("v"); var z = I("z");
        var s = I("s"); var e = I("e"); var p = I("p");
        var left = I("left"); var block = I("B"); var right = I("right");
        var x = I("x"); var y = I("y");
        return Disp(And(
            All(Imp(And(Call("LegalWord", s, e, w), Call("InSupport", e, z)),
                    Call("InSupport", s, Comp(w, z))),
                B("s", I("Guard")), B("e", I("Guard")), B("w", Words), B("z", I("Real"))),
            All(Imp(Call("le", p, Len(block)), Equal(
                    Coord(Append(Append(left, block), right), Add(Len(left), p)),
                    Add(Comp(Call("drop", block, p), I("c0")),
                        Mul(Pow(Call("negate", I("g")), Sub(Len(block), p)),
                            Sub(Coord(right, D(0)), I("c0")))))),
                B("left", Words), B("B", Words), B("right", Words), B("p", I("Nat"))),
            All(Equal(Coord(Append(w, Call("replicate", I("n"), I("L0"))), p), Coord(w, p)),
                B("w", Words), B("n", I("Nat")), B("p", I("Nat"))),
            All(Equal(Comp(w, Add(x, y)),
                    Add(Comp(w, x), Mul(Pow(Call("negate", I("g")), Len(w)), y))),
                B("w", Words), B("x", I("Real")), B("y", I("Real"))),
            All(Equal(Comp(Append(w, v), z), Comp(w, Comp(v, z))),
                B("w", Words), B("v", Words), B("z", I("Real")))));
    }

    private static Formula Reconstruction()
    {
        var j = I("j"); var model = I("model"); var xs = I("execution");
        var p = I("p"); var state = I("D");
        var prefix = Call("observedPrefix", j, model, xs);
        var full = Call("sourcePrefix", j, model, xs);
        var tail = Call("tailPrefix", j);
        var external = Call("externalWord", j, xs);
        Formula Signed(Formula value) => Add(I("c0"), Mul(Call("sign", j), value));
        var paidLength = Add(Call("observationOffset", model), Call("listWeight", xs));
        return Disp(All(And(
            Call("LegalWord", I("G0"), I("G0"), full),
            All(Equal(Call("source", j, model, xs, Add(Len(prefix), p)), Call("address", tail, p)),
                B("p", I("Nat"))),
            All(Equal(Coord(full, Add(Len(prefix), p)), Coord(tail, p)), B("p", I("Nat"))),
            Equal(Coord(Append(Append(external, Call("anchor", j, model)), tail), D(0)),
                Signed(Call("execute", j, xs, Call("initial", j, model)))),
            Equal(Len(prefix), paidLength), Equal(Len(Call("history", model, xs)), paidLength),
            All(Equal(Comp(I("C"), Signed(state)), Signed(Mul(I("chi"), state))), B("D", I("Real"))),
            All(Equal(Comp(Call("block", j), Signed(state)),
                Signed(Add(Call("aSide", j), Mul(I("rho"), state)))), B("D", I("Real"))),
            All(Equal(Comp(Call("returnWord", j, I("a")), Signed(state)),
                Signed(Call("returnMap", j, I("a"), state))), B("a", I("Return")), B("D", I("Real"))),
            All(Equal(Comp(Call("externalWord", j, I("xs")), Signed(state)),
                Signed(Call("execute", j, I("xs"), state))), B("xs", Returns), B("D", I("Real"))),
            Equal(Comp(tail, D(0)), Signed(Call("xSide", j)))),
            B("j", I("Side")), B("model", I("Model")), B("execution", Returns)));
    }


    private static Formula BoundaryGeometry()
    {
        var model = I("model"); var xs = I("execution"); var j = I("j");
        var p = I("p"); var n = I("n"); var k = I("k");
        Formula State(Formula side) => Call("execute", side, Call("take", xs, p),
            Call("initial", side, model));
        Formula Internal(Formula side) => Sub(Call("hSide", side),
            Mul(Pow(I("rho"), k), Sub(Call("hSide", side), Mul(Pow(I("chi"), n), State(side)))));
        var z = Internal(j);
        var signed = Add(I("c0"), Mul(Call("sign", j), z));
        return Disp(All(And(
            All(And(Call("lt", Call("aSide", j), State(j)), Call("lt", State(j), Call("hSide", j))),
                B("j", I("Side")), B("p", I("Nat"))),
            All(Call("lt", State(I("high")), State(I("low"))), B("p", I("Nat"))),
            All(And(Call("lt", D(0), z), Call("lt", z, Call("hSide", j)),
                Call("le", D(0), signed), Call("le", signed, I("T2"))),
                B("j", I("Side")), B("p", I("Nat")), B("n", I("Nat")), B("k", I("Nat"))),
            All(Call("lt", Internal(I("high")), Internal(I("low"))),
                B("p", I("Nat")), B("n", I("Nat")), B("k", I("Nat"))),
            All(Equal(Call("coordinate", Call("sourcePrefix", j, model, xs),
                    Add(Call("length", Call("stem", j)), Call("listWeight", Call("drop", xs, p)))),
                Add(I("c0"), Mul(Call("sign", j), State(j)))),
                B("j", I("Side")), B("p", I("Nat")))) ,
            B("model", I("Model")), B("execution", Returns)));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The five-label affine source uses its original legal guards, endpoint flags, literal blocks and eventually-empty tails. Each departure coordinate belongs to one complete suffix of that source.",
        H("Literal Fibonacci sources and occurrence coordinates"),
        Blocks(
            Paragraph(Text("This import entry point supplies the literal-source interface from "),
                Ref("D5/S3/ConceptDynamics/Coding/DecoderOperationTrace"),
                Text(" and complete boundary geometry from "),
                Ref("D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/StrictSupply"), Text(".")),
            new DocumentBlock.Section(H("One coordinate per occurrence"), Blocks(
                Paragraph(Text("Repository-derived statement: "),
                    Ref("D5/S3/ConceptDynamics/Coding/DecoderOperationTrace.literal_source_geometry"), Text(".")),
                new DocumentBlock.DisplayFormula(Geometry()),
                Paragraph(Text("Induction over the literal word proves support preservation and its affine suffix law. Extending the finite cutoff by empty labels leaves every coordinate unchanged. The displacement in an occurrence formula is the coordinate of the actual complete right suffix minus the fixed center.")))),
            new DocumentBlock.Section(H("Reconstruct both prescribed sources"), Blocks(
                Paragraph(Text("Repository-derived statement: "),
                    Ref("D5/S3/ConceptDynamics/Coding/DecoderOperationTrace.paired_source_reconstruction"), Text(".")),
                new DocumentBlock.DisplayFormula(Reconstruction()),
                Paragraph(Text("The finite block calculation uses every original cycle label. Induction reconstructs the reversed execution list without reversing block letters. Both templates have legal seams, the exact original tail at the unobserved terminal, the actual scalar return action, and observation lengths 26 plus the variable weight or 52 plus that weight.")))),
            new DocumentBlock.Section(H("Actual complete boundaries and internal inputs"), Blocks(
                Paragraph(Text("Repository-derived statement: "),
                    Ref("D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/StrictSupply.actual_complete_boundary_geometry"), Text(".")),
                new DocumentBlock.DisplayFormula(BoundaryGeometry()),
                Paragraph(Text("For every prefix of the common execution list, both actual initial states retain A_j < D_j < h_j and the high displacement is smaller than the low displacement. Internal inputs obtained by any number of C contractions and six-letter affine iterates remain positive and below h_j, keep the same side ordering, and their signed coordinates belong to [0,T2]. Each complete boundary is identified with the coordinate at stem length plus the weight of the unexecuted suffix in the same fixed source. The lower bound A_j is asserted only at complete boundaries, not at arbitrary internal cuts.")))),
            Paragraph(Text("The complete boundary and internal-input statements use the same execution list in both models, including empty executions, zero-length prefixes and zero internal exponents."))),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ConceptDynamics/Coding/DecoderOperationTrace")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/StrictSupply")),
         DocumentEdge.NarrativeReference.ToDocument(
             GidRef.Create("D5/S3/ConceptDynamics/Coding/DecoderOperationTrace")),
         DocumentEdge.NarrativeReference.ToDocument(
             GidRef.Create("D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/StrictSupply"))]));
}

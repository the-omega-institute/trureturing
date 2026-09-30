using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class PhysicalRationalResponseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full complex partition has one reduced positive binary rational response.",
        H("Physical Rational Responses"),
        Blocks(Describe.Lean(
            DescribeId.Create("physical-reply-run"),
            DeclarationHandle.Create("D5/S0/Computability/PhysicalRationalResponse.physical_reply_run"),
            H("Unique ordinary response, length and actual count recovery"),
            StatementSource.FromAuthor(Presentation()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "PhysicalReply relates a response word to a positive rational whose "
                + "complex cast equals the full matrix exponential trace at beta log two. "
                + "The word is the ordinary binary numerator, a slash, and the binary "
                + "denominator of the reduced rational. The denominator one is written "
                + "explicitly. This relation contains no counting or dyadic premise.")),
                Paragraph(Text(
                "For every raw clause family over n declared variables, normalization "
                + "of the actual trace yields one such word. Its length is at most "
                + "n plus twice (n plus one) times the number of clauses plus five. "
                + "Divisibility by three and a dyadic denominator follow from the trace "
                + "and reducedness. The fixed postprocessor reaches its exact clean "
                + "output in at most three times the response length plus ten steps, "
                + "and that output denotes the independently defined satisfying count.")),
                Paragraph(Text(
                "The construction includes zero variables, empty formulas and clauses, "
                + "unused variables, repetitions and tautologies. Arithmetic suitability "
                + "alone does not assert that a word is a physical response."))),
            DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Quantum/Dynamics/ClauseHamiltonian")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/RationalResponseRefinement"))]));

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Presentation()
    {
        var n = Id("n");
        var f = Id("F");
        var w = Id("w");
        var other = Id("v");
        var reply = Call("PhysicalReply", f, w);
        var unique = All("v", Call("List", Id("ResponseSymbol")),
            new Formula.Logic(Call("PhysicalReply", f, other), FormulaLogicOperator.Implies,
                Equal(other, w)));
        var k = Multiply(Add(n, Num(1)), Call("length", f));
        var bound = new Formula.Relation(Call("length", w),
            FormulaRelationOperator.LessThanOrEqual, Add(Add(n, Multiply(Num(2), k)), Num(5)));
        var output = Call("totalPostOutput", w);
        var run = Call("Nonempty", Call("TM2OutputsInTime", Id("postMachine"), w,
            Call("some", Call("binaryWord", output)), Add(Multiply(Num(3), Call("length", w)), Num(10))));
        var count = Equal(Call("msbValue", output), Call("satisfyingCount", f));
        return All("n", Id("Nat"), All("F", Call("Formula", n),
            new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("w"),
                Call("List", Id("ResponseSymbol")),
                And(reply, And(unique, And(bound, And(Call("suitableResponse", w), And(run, count))))))));
    }
}

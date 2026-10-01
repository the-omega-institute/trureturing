using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class RationalResponseRefinementDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every raw ternary response executes to a canonical binary word in linear time.",
        H("Total Rational Response Refinement"),
        Blocks(Describe.Lean(
            DescribeId.Create("post-word-run"),
            DeclarationHandle.Create("D5/S0/Computability/RationalResponseRefinement.post_word_run"),
            H("Whole-word execution, arithmetic recovery and exact fault output"),
            StatementSource.FromAuthor(Presentation()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For every word over zero, one and slash, the fixed four-stack, "
                + "eleven-label machine reaches the exact clean haltList output in "
                + "at most three times the input length plus ten actual transitions. "
                + "All scratch is empty and the finite control is restored.")),
                Paragraph(Text(
                "Arithmetic suitability means a positive binary numerator, exactly "
                + "one slash and a denominator one followed by e zeros. The numerator "
                + "is divisible by three and is odd when e is positive. Suitable "
                + "words yield twice p divided by three when e is zero, and otherwise "
                + "the integer quotient of p divided by three and then by two to "
                + "the power e minus one. Every unsuitable word produces exactly "
                + "one zero. Every output is one zero or begins with one.")),
                Paragraph(Text(
                "Suitability is an arithmetic condition, independent of the physical "
                + "trace. The word 11/1 is suitable and yields two; the physical dummy "
                + "response 11/100 yields zero. Count correctness requires the "
                + "separate physical response relation. Zero output does not "
                + "characterize rejection."))),
            DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/RationalMalformedCleanup")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/RationalPostprocessor"))]));

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Presentation()
    {
        var w = Id("w");
        var xs = Id("xs");
        var e = Id("e");
        var output = Call("totalPostOutput", w);
        var p = Call("msbValue", Call("cons", Id("true"), xs));
        var value = Call("msbValue", output);
        var quotient = new Formula.Floor(new Formula.Fraction(p, Num(3)));
        var numeric = new Formula.Aligned([
            Implies(Equal(e, Num(0)), Equal(value, Multiply(Num(2), quotient))),
            Implies(new Formula.Relation(Num(0), FormulaRelationOperator.LessThan, e),
                Equal(value, new Formula.Floor(new Formula.Fraction(quotient,
                    new Formula.Power(Num(2), Subtract(e, Num(1)))))))
        ]);
        var arithmetic = All("xs", Call("List", Id("Bool")), All("e", Id("Nat"),
            Implies(Equal(w, Call("responseWord", xs, e)),
                Implies(new Formula.Relation(Num(3), FormulaRelationOperator.Divides, p),
                    Implies(Implies(new Formula.Relation(Num(0), FormulaRelationOperator.LessThan, e),
                        Call("Odd", p)), numeric)))));
        var zero = Call("singleton", Id("false"));
        var rejects = Implies(new Formula.Not(Call("suitableResponse", w)), Equal(output, zero));
        var canonical = new Formula.Logic(Equal(output, zero), FormulaLogicOperator.Or,
            new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("bs"),
                Call("List", Id("Bool")), Equal(output, Call("cons", Id("true"), Id("bs")))));
        var run = Call("Nonempty", Call("TM2OutputsInTime", Id("postMachine"), w,
            Call("some", Call("binaryWord", output)), Add(Multiply(Num(3), Call("length", w)), Num(10))));
        return All("w", Call("List", Id("ResponseSymbol")), And(run, And(arithmetic, And(rejects, canonical))));
    }
}

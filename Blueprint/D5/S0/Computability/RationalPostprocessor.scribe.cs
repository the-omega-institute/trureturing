using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class RationalPostprocessorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An ordinary dyadic rational word is decoded by a fixed finite stack machine.",
        H("Ordinary Rational Response Processing"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("dyadic-response-run"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/RationalPostprocessor.dyadic_response_run"),
                H("Clean native run and numerical decoding"),
                StatementSource.FromAuthor(Presentation()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The numerator is a positive binary word beginning with one. "
                        + "The denominator is one followed by e zeros, with a slash between "
                        + "the two words. The numerator p is divisible by three and is odd "
                        + "when e is positive. The fixed machine has four stacks, eleven "
                        + "labels, twenty-four control states and the alphabet zero, one, slash.")),
                    Paragraph(Text(
                        "The actual step relation starts at the library's clean input "
                        + "configuration and reaches its exact clean halt configuration. "
                        + "The input, quotient and shift stacks are empty and the finite "
                        + "state is reset. The run uses at most four times the complete "
                        + "response length plus four transitions.")),
                    Paragraph(Text(
                        "The emitted canonical binary word denotes twice p divided by "
                        + "three when e is zero. Otherwise it denotes the integer quotient "
                        + "of p divided by three and then by two to the power e minus one. "
                        + "Division uses three remainder states; each denominator shift "
                        + "is a physical stack mark. Zero is represented by one zero digit."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The theorem concerns the stated positive dyadic inputs. Universal "
                + "malformed-input correctness and the relation to a physical oracle "
                + "are separate obligations."))),
        []));

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Presentation()
    {
        var xs = Id("xs");
        var e = Id("e");
        var p = Call("msbValue", Call("cons", Id("true"), xs));
        var word = Call("responseWord", xs, e);
        var output = Call("responseOutput", xs, e);
        var divides = new Formula.Relation(Num(3), FormulaRelationOperator.Divides, p);
        var odd = new Formula.Logic(new Formula.Relation(Num(0),
            FormulaRelationOperator.LessThan, e), FormulaLogicOperator.Implies, Call("Odd", p));
        var run = Call("Nonempty", Call("TM2OutputsInTime", Id("postMachine"), word,
            Call("some", Call("binaryWord", output)), Add(Multiply(Num(4),
                Call("length", word)), Num(4))));
        var quotient = new Formula.Floor(new Formula.Fraction(p, Num(3)));
        var numerical = new Formula.Aligned([
            new Formula.Logic(Equal(e, Num(0)), FormulaLogicOperator.Implies,
                Equal(Call("msbValue", output), Multiply(Num(2), quotient))),
            new Formula.Logic(new Formula.Relation(Num(0), FormulaRelationOperator.LessThan, e),
                FormulaLogicOperator.Implies, Equal(Call("msbValue", output),
                    new Formula.Floor(new Formula.Fraction(quotient,
                        new Formula.Power(Num(2), Subtract(e, Num(1)))))))
        ]);
        return All("xs", Call("List", Id("Bool")), All("e", Id("Nat"),
            new Formula.Logic(new Formula.Logic(divides, FormulaLogicOperator.And, odd),
                FormulaLogicOperator.Implies,
                new Formula.Logic(run, FormulaLogicOperator.And, numerical))));
    }
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.PrimeAxis;

internal sealed class GenerationShadowDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var a = Id("a");
        var u = Id("u");
        var p = Id("p");

        var shadow = Equal(
            Call("n", Add(a, u)),
            Multiply(Call("n", a), Call("n", u)));

        var length = Equal(
            Call("L", a),
            Call("sum", p, Multiply(Call("exponent", a, p), Call("log", p))));

        var arrow = new Formula.Relation(
            Num(0), FormulaRelationOperator.LessThan, Call("L", a));

        const string declarationPrefix = "D5/S1/Digit/PrimeAxis/GenerationShadow.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "Multiplication is the decoded shadow of exponent generation, and motion has length.",
            H("Generation Shadow"),
            Blocks(
                Paragraph(Text(
                    "The clause reads the kernel's bottom layer as generation on a prime "
                        + "exponent ledger: the state advances by adding a control vector, and "
                        + "integer multiplication appears only as the decoded image of that "
                        + "motion. Multiplication is therefore not primitive here; the ledger "
                        + "step is, and multiplication is its shadow.")),
                Paragraph(Text(
                    "The decoder and the normalized step already existed. What is added is the "
                        + "length: a search for a state length on prime-axis tables returned "
                        + "nothing. Each axis contributes its exponent weighted by the prime's "
                        + "logarithm, and a state carrying any positive exponent has positive "
                        + "length, because every prime exceeds one.")),
                Describe.Lean(
                    DescribeId.Create("generation-decodes-to-multiplication"),
                    DeclarationHandle.Create(declarationPrefix + "decode_generation"),
                    H("Generation decodes to multiplication"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(shadow)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Adding control codes and renormalizing multiplies the decoded values, "
                            + "which is the existing one-step decoder result named at the "
                            + "generation step."))),
                    DescribeRole.Lemma),
                Describe.Lean(
                    DescribeId.Create("every-prime-contributes-positive-length"),
                    DeclarationHandle.Create(declarationPrefix + "log_prime_pos"),
                    H("Every prime contributes positive length"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(
                        new Formula.Relation(Num(0), FormulaRelationOperator.LessThan,
                            Call("log", p)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "A prime is at least two, so its logarithm is positive; this is the "
                            + "only arithmetic the length argument needs."))),
                    DescribeRole.Lemma),
                Describe.Lean(
                    DescribeId.Create("the-length-of-a-state"),
                    DeclarationHandle.Create(declarationPrefix + "stateLength_nonneg"),
                    H("The length of a state"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(length)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Length sums the exponents against the prime logarithms, and is never "
                            + "negative since each summand is a nonnegative exponent times a "
                            + "positive logarithm."))),
                    DescribeRole.Lemma),
                Describe.Lean(
                    DescribeId.Create("a-nonempty-state-has-positive-length"),
                    DeclarationHandle.Create(declarationPrefix + "stateLength_pos_of_axis"),
                    H("A nonempty state has positive length"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(arrow)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The pointwise lemma the arrow of time rests on. One positive exponent "
                            + "on one axis already exceeds zero, and the remaining summands are "
                            + "nonnegative, so the whole length is positive. Dropping the "
                            + "hypothesis makes the module fail to build, so the statement is "
                            + "not a claim that length is always positive."))),
                    DescribeRole.Theorem))));
    }
}

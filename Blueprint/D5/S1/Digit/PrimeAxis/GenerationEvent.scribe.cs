using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.PrimeAxis;

internal sealed class GenerationEventDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var u = Id("u");
        var p = Id("p");

        var finite = Call("Finite", Call("support", u));

        var offSupport = Equal(Call("exponent", u, p), Num(0));

        var legal = new Formula.Logic(
            finite,
            FormulaLogicOperator.And,
            new Formula.Logic(offSupport, FormulaLogicOperator.And,
                Call("Canonical", Call("digits", u, p))));

        const string declarationPrefix = "D5/S1/Digit/PrimeAxis/GenerationEvent.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "A legal generation event is a finitely supported vector of prime exponents.",
            H("Generation Event"),
            Blocks(
                Paragraph(Text(
                    "The clause defines a legal generation event as a finitely supported "
                        + "vector on the prime axes. In this repository that finiteness is not "
                        + "a side condition to be checked: the state type carries its digits as "
                        + "a finitely supported function, so support is finite by construction "
                        + "and every axis outside it contributes nothing.")),
                Paragraph(Text(
                    "Stating it is still the content of the clause. Without these, a reader has "
                        + "the type but no theorem saying what the type buys, and the "
                        + "definition's own claim - finite support, so only finitely many axes "
                        + "are ever active - is left to be read off a signature.")),
                Describe.Lean(
                    DescribeId.Create("only-finitely-many-axes-are-active"),
                    DeclarationHandle.Create(declarationPrefix + "support_finite"),
                    H("Only finitely many axes are active"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(finite)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The support of a finitely supported function is a finite set, which is "
                            + "what the clause asks of a generation event."))),
                    DescribeRole.Lemma),
                Describe.Lean(
                    DescribeId.Create("outside-the-support-the-exponent-vanishes"),
                    DeclarationHandle.Create(
                        declarationPrefix + "axisExponent_eq_zero_of_not_mem"),
                    H("Outside the support the exponent vanishes"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(offSupport)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "An axis outside the support carries the zero row, and the zero row "
                            + "decodes to exponent zero, so inactive axes contribute nothing to "
                            + "any later reading."))),
                    DescribeRole.Lemma),
                Describe.Lean(
                    DescribeId.Create("a-generation-event-is-legal"),
                    DeclarationHandle.Create(declarationPrefix + "generation_event_is_legal"),
                    H("A generation event is legal"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(legal)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Finitely supported, zero off the support, canonical on every axis. "
                            + "Replacing the canonicity conjunct by a trivially true one makes "
                            + "the module fail to build, so it is carrying weight rather than "
                            + "padding the conjunction."))),
                    DescribeRole.Theorem))));
    }
}

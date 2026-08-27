using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Completion;

internal sealed class SequentialWordObservationResidualDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Instrument word expectations agree exactly on the generated orthogonal residual.",
        H("Sequential Word Observation Residual"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sequential-word-observation-residual"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Completion/SequentialWordObservationResidual."
                        + "sequential_observation_iff"),
                H("Bounded instrument words characterize the orthogonal residual"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a real Hermitian operator carrier, each instrument dual map "
                            + "acts on the identity effect. The public word-effect construction "
                            + "folds those maps in source order, matching the Heisenberg "
                            + "composition of a finite instrument word.")),
                    Paragraph(Text(
                        "Two represented states have equal expectations for every word of "
                            + "length at most n exactly when their difference is orthogonal to "
                            + "the real span of all generated word effects."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);

    private static Formula TheoremFormula()
    {
        Formula d = F.Id("d");
        Formula alphabet = F.Id("A");
        Formula state = F.Id("S");
        Formula carrier = Call("HermitianSpace", d);
        Formula word = F.Id("w");
        Formula n = F.Id("n");
        Formula instrumentDual = F.Id("J");
        Formula stateRepresentation = F.Id("X");
        Formula rho = F.Id("rho");
        Formula sigma = F.Id("sigma");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula wordEffect = Call("sequentialWordEffect", instrumentDual, word);
        Formula expectation(Formula stateValue) =>
            Call("inner", real, stateValue, wordEffect);
        Formula boundedWord = Seq(
            Forall, Sp, word, Colon, Sp, Call("List", alphabet), Comma, Sp,
            Call("length", word), Sp, Le, Sp, n, Sp, Rightarrow, Sp,
            Open, expectation(Apply(stateRepresentation, rho)), Sp, Eq, Sp,
            expectation(Apply(stateRepresentation, sigma)), Close);
        Formula generatedEffect = Seq(
            Open, Exists, Sp, F.Id("e"), Colon, Sp, carrier, Comma, Sp,
            Exists, Sp,
            word, Colon, Sp, Call("List", alphabet), Comma, Sp,
            Call("length", word), Sp, Le, Sp, n, Sp, Land, Sp,
            F.Id("e"), Sp, Eq, Sp, Call("sequentialWordEffect", instrumentDual, word),
            Close);
        Formula spanResidual = Seq(
            Open, Call("span", real, generatedEffect), Close, Caret,
            Grp(Perp));

        return Disp(Seq(
            Forall, Sp, d, Colon, Sp, F.Id("Nat"), Comma, Sp,
            alphabet, Comma, Sp, state, Colon, Sp, Seq(Operatorname, Grp(F.Id("Type"))),
            Comma, Sp, instrumentDual, Colon, Sp, alphabet, To, carrier, Sp,
            To, carrier, Comma, Sp,
            stateRepresentation, Colon, Sp, state, To, carrier, Comma, Sp,
            rho, Comma, Sp, sigma, Colon, Sp, state, Comma, Sp,
            n, Colon, Sp, F.Id("Nat"), Sp, Rightarrow, RowBreak, Grp(),
            Open, boundedWord, Close, Sp, Leftrightarrow, Sp,
            Open, Seq(
                Apply(stateRepresentation, rho), Sp, Minus, Sp,
                Apply(stateRepresentation, sigma), Sp, InMacro, Sp, spanResidual),
            Close, Dot));
    }
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Automata;

internal sealed class BinaryZeckendorfLanguageDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The successful language of the binary Zeckendorf base is exactly nonadjacency.",
        H("The Exact Binary Base Language"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("binary-base-success-iff-nonadjacency"),
                DeclarationHandle.Create(
                    "D5/S0/Automata/BinaryZeckendorfLanguage.base_success_iff_noAdjacentOnes"),
                H("Successful execution is equivalent to no adjacent ones"),
                StatementSource.FromAuthor(LanguageFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The word w is any list over Fin 2. The base begins in previousZero; "
                        + "q ranges over BinaryZeckendorfState. NoAdjacentOnes means that "
                        + "each adjacent pair contains a zero. There is no leading-one or "
                        + "nonempty-word premise.")),
                    Paragraph(Text(
                        "The proof strengthens the induction by recording the preceding bit "
                        + "in the initial base state. It handles both initial states and both "
                        + "symbols, so it also excludes undefined runs caused by adjacent ones."))),
                DescribeRole.Theorem)),
        []));

    private static Formula LanguageFormula() => F.Disp(F.Seq(
        F.Forall, F.Sp, F.Id("w"), F.Sp, F.Colon, F.Sp,
        Call("List", Call("Fin", F.D(2))), F.Comma, F.Sp,
        F.Grp(F.Exists, F.Sp, F.Id("q"), F.Sp, F.Colon, F.Sp,
            F.Id("BinaryZeckendorfState"), F.Comma, F.Sp,
            Call("evalBinaryZeckendorfBase", F.Id("w")), F.Sp, F.Eq, F.Sp,
            Call("some", F.Id("q"))),
        F.Sp, F.Iff, F.Sp, Call("NoAdjacentOnes", F.Id("w"))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}

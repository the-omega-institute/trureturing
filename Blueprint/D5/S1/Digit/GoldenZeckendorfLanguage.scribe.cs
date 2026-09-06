using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class GoldenZeckendorfLanguageDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical dense Zeckendorf words execute in the binary base for every natural number.",
        H("Arithmetic Inputs in the Base Language"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("canonical-msd-word-base-success"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/GoldenZeckendorfLanguage.zeckendorfMSDWord_base_success"),
                H("All canonical MSD inputs execute successfully"),
                StatementSource.FromAuthor(GeneralFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural n, including zero, the existing zeckendorfMSDWord "
                        + "generator is accepted from previousZero. The proof uses Mathlib's "
                        + "gap-separated occupied-index predicate and its list chain API to "
                        + "transfer nonadjacency through the reversed-range dense rendering.")),
                    Paragraph(Text(
                        "The theorem has no finite sample bound. It uses the current "
                        + "GoldenBase4AutomataOracle generator and does not assume the separate "
                        + "IsZeckendorfBitWord predicate described in the paper's alternate source."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("radix-four-power-input-base-success"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/GoldenZeckendorfLanguage.base4PowerWord_base_success"),
                H("Every sparse radix-four input executes in its base"),
                StatementSource.FromAuthor(PowerFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Instantiate the natural-number theorem at 4 raised to i. The input and "
                    + "base are precisely the fields of the existing base4Problem; no "
                    + "correct candidate machine or solver certificate is assumed."))),
                DescribeRole.Theorem)),
        []));

    private static Formula GeneralFormula() => F.Disp(F.Seq(
        F.Forall, F.Sp, F.Id("n"), F.Sp, F.Colon, F.Sp, F.Id("Nat"), F.Comma, F.Sp,
        F.Exists, F.Sp, F.Id("q"), F.Sp, F.Colon, F.Sp,
        F.Id("BinaryZeckendorfState"), F.Comma, F.Sp,
        Call("evalBinaryZeckendorfBase", Call("zeckendorfMSDWord", F.Id("n"))),
        F.Sp, F.Eq, F.Sp, Call("some", F.Id("q"))));

    private static Formula PowerFormula() => F.Disp(F.Seq(
        F.Forall, F.Sp, F.Id("i"), F.Sp, F.Colon, F.Sp, F.Id("Nat"), F.Comma, F.Sp,
        F.Exists, F.Sp, F.Id("q"), F.Sp, F.Colon, F.Sp,
        F.Id("BinaryZeckendorfState"), F.Comma, F.Sp,
        Call("evalBase4ProblemBase", Call("base4ProblemInput", F.Id("i"))),
        F.Sp, F.Eq, F.Sp, Call("some", F.Id("q"))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}

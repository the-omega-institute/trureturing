using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class GoldenBase4AutomataOracleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical Zeckendorf words and exact floor differences define the base-four golden-ratio DFAO specification.",
        H("The Base-Four Golden-Ratio Automata Oracle"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("base-four-floor-decomposition"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/GoldenBase4AutomataOracle.base4_floor_succ_decomposition"),
                H("Successive floors decompose into quotient and exact base-four digit"),
                StatementSource.FromAuthor(DigitFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The output digit is defined by an exact integer floor difference. A general radix-floor lemma proves that the difference lies in zero through three.")),
                    Paragraph(Text(
                        "The theorem freezes the quotient-remainder identity without floating-point evaluation of the golden ratio."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("base-four-finite-obstruction"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/GoldenBase4AutomataOracle.base4_state_lower_bound_of_finite_obstruction"),
                H("A finite prefix obstruction gives a global base-four state lower bound"),
                StatementSource.FromAuthor(ObstructionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The global sample maps i to the canonical Zeckendorf word of four to the i and labels it by the exact i-th base-four digit.")),
                    Paragraph(Text(
                        "Global correctness restricts to every finite prefix. The generic typed-sample theorem therefore turns any verified Fin k coloring obstruction into the strict global lower bound k < card(State)."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S0/Automata/TypedSampleIdentification")),
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S0/Conventions/WDigits")),
        ]));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula DigitFormula() => Disp(Seq(
        Call("base4Floor", Seq(F.Id("n"), Sp, Plus, Sp, D(1))),
        Sp, Eq, Sp,
        D(4), Sp, Cdot, Sp, Call("base4Floor", F.Id("n")),
        Sp, Plus, Sp,
        Call("base4GoldenDigit", F.Id("n")), Dot));

    private static Formula ObstructionFormula() => Disp(Seq(
        Call("NoSmallModel", F.Id("k"), Call("prefixSample", F.Id("N"))),
        Sp, Land, Sp,
        Call("Fits", F.Id("M"), Call("spec")),
        Sp, Implies, Sp,
        F.Id("k"), Sp, Lt, Sp, Call("card", F.Id("State")), Dot));
}

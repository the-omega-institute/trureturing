using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.CellularAutomata;

internal sealed class FormentiKamilyaRule115Document : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/StatisticalMechanics/CellularAutomata/FormentiKamilyaRule115.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Automata/formentikamilya2026resoca115");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nine-step returns in finite RESOCA 115 configurations are already three-step returns.",
        H("Question 1 for RESOCA 115 on the integer line"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("resoca115-nine-return-three-return"),
                DeclarationHandle.Create(Owner + "returns_three_of_returns_nine"),
                H("Nine-step returns from two finitely supported layers"),
                StatementSource.FromAuthor(NineStepReturn()), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("The state is the ordered pair of past and current Boolean layers on the integer line. Equation (1) on printed p. 96 gives the global reversible update. The new past layer is the old current layer. The new current bit at site i is b(i) XOR (NOT c(i) OR (c(i−1) AND NOT c(i+1))), using the elementary local rule in Table 1 on p. 97. The formula uses s₁ and s₂ for the past and current layers, respectively. The hypothesis is finiteness of the union of the two initial supports and equality of the full state after nine steps.")),
                    Paragraph(Text("Radius-one propagation gives the three-phase background on both spatial tails. At time n it applies outside the initial support bound enlarged by n. Encode each nine-periodic time column as a nine-bit mask. The kernel checks 31 candidate masks, 40 forward-reachable pairs and 52 forward edges, then 3 returning pairs and 5 returning edges. Closure from the left background and predecessor closure from the right background apply along arbitrary integer segments. Every surviving column is invariant under time shift three. The nine-return hypothesis supplies the temporal wraparound for both layers, giving the three-step return. The finite enumeration bounds the time-column graph and applies to arbitrary finite spatial widths."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("resoca115-question-one-refuted"),
                DeclarationHandle.Create(Owner + "result"),
                H("Least period nine is impossible"),
                StatementSource.FromAuthor(Disp(Seq(Neg, Sp, Named(F.Id("claim"))))), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Question 1 on printed p. 97 asks ‘For RESOCA 115, in the context of finite configurations, are all multiple of 3 periods?’ The claim requires a configuration for every positive multiple p of three, both initial layers finitely supported, with a p-step return and no earlier positive return. At p = 9 the preceding theorem forces a return at 3, contradicting least period nine."))),
                DescribeRole.Theorem))));

    private static Formula Named(params Formula[] parts) => Seq(Operatorname, Grp(parts));

    private static Formula NineStepReturn()
    {
        Formula state = F.Id("s"), site = F.Id("i");
        Formula On(byte layer) => Seq(state, Underscore, Grp(D(layer)), Open, site, Close,
            Sp, Eq, Sp, Named(F.Id("true")));
        Formula Returns(byte steps) => Seq(Named(F.Id("step")), Caret, Grp(D(steps)),
            Open, state, Close, Sp, Eq, Sp, state);
        Formula finite = Seq(Named(F.Id("Set"), Dot, F.Id("Finite")), Open,
            OpenBrace, site, Sp, InMacro, Sp, Mathbb, Grp(F.Id("Z")), Sp, Mid, Sp,
            On(1), Sp, Lor, Sp, On(2), CloseBrace, Close);
        return Disp(Seq(Forall, Sp, state, Sp, Colon, Sp, Named(F.Id("Config")), Comma, Sp,
            finite, Sp, Implies, Sp, Returns(9), Sp, Implies, Sp, Returns(3)));
    }
}

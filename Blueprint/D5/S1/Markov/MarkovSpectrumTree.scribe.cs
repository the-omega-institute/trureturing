using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Markov;

internal sealed class MarkovSpectrumTreeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S1/Markov/MarkovSpectrumTree",
            "Integer Markov triples are preserved by the Vieta-jump edge that generates the Markov tree."),
        H("The Markov Spectrum Tree"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("markov-vieta-step"),
                H("The Vieta jump preserves the Markov equation"),
                LeanTheorem(
                    "D5/S1/Markov/MarkovSpectrumTree.markov_vieta_step"),
                Disp(Seq(
                    F.Id("a"), Caret, Grp(D(2)), Plus,
                    F.Id("b"), Caret, Grp(D(2)), Plus,
                    F.Id("c"), Caret, Grp(D(2)), Eq,
                    D(3), F.Id("a"), F.Id("b"), F.Id("c"), Sp, Rightarrow, Sp,
                    F.Id("a"), Caret, Grp(D(2)), Plus,
                    F.Id("b"), Caret, Grp(D(2)), Plus,
                    Open, D(3), F.Id("a"), F.Id("b"), Minus, F.Id("c"), Close,
                    Caret, Grp(D(2)), Eq,
                    D(3), F.Id("a"), F.Id("b"),
                    Open, D(3), F.Id("a"), F.Id("b"), Minus, F.Id("c"), Close,
                    Comma, Sp, F.Id("c"), Mapsto, Sp,
                    D(3), F.Id("a"), F.Id("b"), Minus, F.Id("c"))),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "A Markov triple is an integer solution of the equation "
                        + "a^2 + b^2 + c^2 = 3abc. Holding a and b fixed, the theorem "
                        + "proves that replacing c by 3ab - c gives another solution. "
                        + "This is the Vieta-jump edge: the original c and its replacement "
                        + "are the two roots of the corresponding quadratic equation, whose "
                        + "sum is 3ab.")),
                    Paragraph(Text(
                        "The checked seed triples (1,1,1), (1,1,2), and (1,2,5) exhibit "
                        + "the base Markov numbers 1, 2, and 5. Applying the same edge to "
                        + "(1,2,1) produces (1,2,5), and applying it to (1,5,2) produces "
                        + "(1,5,13). Thus the formal statement supplies the algebraic tree "
                        + "step and the examples verify its first two generated branches.")))))));
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class GoldenMechanicalWordDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S1/Words/GoldenMechanicalWord",
                "Identify the exact fractional-coordinate window for a golden mechanical letter."),
            H("Golden Mechanical Word Window"),
            Blocks(
                Paragraph(Text(
                    "The lower golden mechanical word is defined by consecutive floor differences at slope one over the golden ratio. The theorem below gives an exact local test using the existing golden fractional coordinate.")),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("golden-mechanical-letter-window"),
                    H("A letter is one exactly on the local window"),
                    LeanTheorem(
                        "D5/S1/Words/GoldenMechanicalWord.golden_mechanical_letter_eq_one_iff"),
                    LatexStatement.Create(@"$$\forall n\in\mathbb{N},\ s_n=1\ \Leftrightarrow\ \{n\varphi\}\in[1-\varphi^{-1},1)$$"),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "For every natural index, the floor-difference letter equals one if and only if the golden fractional coordinate lies in the stated half-open interval. No complexity, substitution, or cut-and-project classification is asserted.")))
                ))));
}

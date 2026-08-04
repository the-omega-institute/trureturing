using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Solenoid;

internal sealed class ThroatTransitionCocycleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S1/Solenoid/ThroatTransitionCocycle",
                "Equal visible projections determine unique hidden-fiber differences, which compose additively."),
            H("Throat-Transition Cocycle"),
            Blocks(
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("three-lift-difference-cocycle"),
                    H("Visible agreement determines the hidden-fiber cocycle"),
                    LeanTheorem(
                        "D5/S1/Solenoid/ThroatTransitionCocycle."
                        + "three_lift_difference_cocycle"),
                    LatexStatement.Create(
                        @"$$\pi\circ s_{\alpha}=\pi\circ s_{\beta},\quad "
                        + @"\pi\circ s_{\beta}=\pi\circ s_{\gamma}\quad\Rightarrow\quad "
                        + @"\begin{gathered}"
                        + @"\exists!\,k_{\alpha\beta}:U\to\mathcal S,\ "
                        + @"\pi(k_{\alpha\beta}(u))=0,\ "
                        + @"s_{\beta}(u)=s_{\alpha}(u)+k_{\alpha\beta}(u),\\"
                        + @"\exists!\,k_{\beta\gamma}:U\to\mathcal S,\ "
                        + @"\pi(k_{\beta\gamma}(u))=0,\ "
                        + @"s_{\gamma}(u)=s_{\beta}(u)+k_{\beta\gamma}(u),\\"
                        + @"\exists!\,k_{\alpha\gamma}:U\to\mathcal S,\ "
                        + @"\pi(k_{\alpha\gamma}(u))=0,\ "
                        + @"s_{\gamma}(u)=s_{\alpha}(u)+k_{\alpha\gamma}(u),\\"
                        + @"k_{\alpha\gamma}(u)=k_{\alpha\beta}(u)+k_{\beta\gamma}(u)"
                        + @"\end{gathered}\qquad(u\in U),$$"),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Each difference is constructed pointwise by subtraction. "
                        + "The additive projection sends it to zero, group cancellation "
                        + "gives uniqueness, and the cocycle identity follows by "
                        + "telescoping the two successive differences.")))))));
}

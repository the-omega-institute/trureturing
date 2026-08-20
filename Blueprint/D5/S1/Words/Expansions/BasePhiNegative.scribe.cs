using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Expansions;

internal sealed class BasePhiNegativeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Negative base-phi prefixes have canonical local constraints and Lucas-gap sequence interfaces.",
        H("Negative Base-Phi Prefix Interfaces"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("positive-gaps-give-increasing-trident-components"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Expansions/BasePhiNegative.gap_sequence_strict_mono"),
                H("Positive gap letters make each trident component strictly increasing"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("a"), Gt, D(0), Sp, Land, Sp, F.Id("b"), Gt, D(0), Sp,
                    Rightarrow, Sp, Operatorname, Grp(F.Id("StrictMono")), Open,
                    F.Id("V"), Underscore, F.Id("X"), Open, F.Id("a"), Comma,
                    F.Id("b"), Comma, F.Id("r"), Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The three sequence families accumulate one of two integer gaps at every step. "
                        + "When both gaps are positive, each next value is larger, independently of the "
                        + "chosen Sturmian family.")),
                    Paragraph(Text(
                        "The module also proves that Lucas parameters are positive, that adjacent negative "
                        + "digits cannot both be true, and hence that any prefix containing 11 is not "
                        + "admissible. The one-digit prefix occurrence sets form a disjoint cover of "
                        + "expansions reaching negative depth one.")),
                    Paragraph(Text(
                        "These interface theorems do not prove the conjectural Lucas formulas for the "
                        + "one-digit prefixes. That step still requires a formal bridge from canonical "
                        + "Zeckendorf digits to the two-sided base-phi expansion."))),
                DescribeRole.Theorem))));
}

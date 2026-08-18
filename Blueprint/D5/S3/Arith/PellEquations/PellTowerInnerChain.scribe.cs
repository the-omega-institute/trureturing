using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.PellEquations;

internal sealed class PellTowerInnerChainDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The inner-chain map preserves the Pell-type tower equation.",
        H("Pell Tower Inner-Chain Preservation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pell-tower-inner-chain-preservation"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/PellEquations/PellTowerInnerChain."
                    + "pell_tower_inner_chain"),
                H("The inner-chain map preserves the tower equation"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("D"), Comma, Sp, F.Id("d"), Comma, Sp, F.Id("k"),
                    Sp, InMacro, Sp, Mathbb, Grp(F.Id("Z")), Comma, Esc,
                    Open, F.Id("d"), Plus, D(1), Close, Cdot, Sp,
                    Open, F.Id("d"), Minus, D(3), Close, Eq,
                    F.Id("D"), Cdot, Sp, F.Id("k"), Caret, Grp(D(2)), Sp, Rightarrow, Sp,
                    Open,
                    Open, F.Id("d"), Cdot, Sp, Open, F.Id("d"), Minus, D(2), Close,
                    Plus, D(1), Close, Cdot, Sp,
                    Open, F.Id("d"), Cdot, Sp, Open, F.Id("d"), Minus, D(2), Close,
                    Minus, D(3), Close,
                    Close, Eq, F.Id("D"), Cdot, Sp,
                    Open, Open, F.Id("d"), Minus, D(1), Close, Cdot, Sp, F.Id("k"), Close,
                    Caret, Grp(D(2))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For integers D, d, and k, suppose (d + 1)(d - 3) = Dk^2. Set "
                        + "d' = d(d - 2). Then (d' + 1)(d' - 3) = D((d - 1)k)^2, so "
                        + "the transformed dimension remains on the same Pell-type tower and "
                        + "its new Pell coordinate is explicit.")),
                    Paragraph(Text(
                        "The proof factors the transformed left-hand side as "
                        + "(d - 1)^2(d + 1)(d - 3), substitutes the assumed tower equation, "
                        + "and normalizes the remaining polynomial identity with Mathlib's "
                        + "ring tactic. Pinned Mathlib Pell declarations and source search had "
                        + "no exact theorem for this transformation. Online Loogle returned "
                        + "zero matches for the formula-shaped query.")),
                    Paragraph(Text(
                        "This node closes only the inner-chain sentence in remark 27.594, namely "
                        + "that d maps to d(d - 2) within a fixed Pell-type tower. It does not "
                        + "formalize the atom's unit-norm dichotomy, Lucas identities, SIC "
                        + "classification data, torsion spectrum, or numerical searches."))),
                DescribeRole.Theorem))));
}

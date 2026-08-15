using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Admissibility;

internal sealed class OddIndexFreedomDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Odd natural indices free every subset from adjacency and give the full powerset count.",
        H("Odd-Index Zeckendorf Freedom"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("odd-index-subsets-are-admissible-and-counted"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/Admissibility/OddIndexFreedom"
                    + ".odd_index_subsets_are_admissible_and_counted"),
                H("Odd-index subsets are nonadjacent and exactly counted"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("I"), Subset, Underscore,
                    Grp(Mathrm, Grp(F.Id("fin"))), Mathbb, Grp(F.Id("N")), Comma, Esc,
                    Open, Forall, Sp, F.Id("n"), InMacro, Sp, F.Id("I"), Comma,
                    F.Id("n"), Esc, F.Text, Grp(Sp, F.Id("odd")), Close,
                    Sp, Rightarrow, Sp, Left, Open,
                    Open, Forall, Sp, F.Id("S"), Subseteq, Sp, F.Id("I"), Comma,
                    Forall, Sp, F.Id("n"), InMacro, Sp, F.Id("S"), Comma, Neg,
                    Open, F.Id("n"), Plus, D(1), InMacro, Sp, F.Id("S"), Close, Close,
                    Sp, Land, Sp,
                    Lvert, Open, Operatorname, Grp(F.Id("powerset")),
                    Open, F.Id("I"), Close, Setminus, OpenBrace, Emptyset,
                    CloseBrace, Close, Rvert, Eq,
                    D(2), Caret, Grp(Lvert, Sp, F.Id("I"), Rvert), Minus, D(1),
                    Right, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let I be any finite set of odd natural indices. Every subset S of I "
                        + "inherits oddness, while the successor of an odd index is even. Thus S "
                        + "cannot contain both n and n+1, which is exactly the local "
                        + "Zeckendorf nonadjacency condition used by the source atom.")),
                    Paragraph(Text(
                        "Pinned Mathlib was searched before proving. No combined theorem was found. "
                        + "The proof directly reuses Nat.Odd.add_one and Nat.not_even_iff_odd for "
                        + "the parity exclusion, then Finset.card_powerset and "
                        + "Finset.card_erase_of_mem for the exact nonempty-subset count. When "
                        + "the index set has cardinality twelve, the formula evaluates to 4095.")),
                    Paragraph(Text(
                        "This closes only the odd-index freedom and exact-count assertion in the "
                        + "first paragraph of source remark 27.192. The cone-series expansion, its "
                        + "numerical approximations, the missing second family, and the longer "
                        + "research roadmap in the same atom are not asserted here."))),
                DescribeRole.Theorem)),
        []));
}

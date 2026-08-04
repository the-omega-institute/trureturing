using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Phase;

internal sealed class SeatTowerConsequencesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S1/Phase/SeatTowerConsequences",
                "Record exact residue, Jacobi, cosecant, gap, and combination-counting consequences from the seat-tower frontier."),
            H("Seat-Tower Consequences"),
            Blocks(
                Paragraph(Text(
                    "This module records six formal consequences with every structural premise exposed. It does not supply the finite conflict table, the selector-numerator bridge, an orbit-to-choice bijection, or any finite experimental certificate. No finite observation or measurable claim is closed.")),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("mod-ninety-six-refinement"),
                    H("A residue modulo ninety-six fixes its coarser residues"),
                    LeanTheorem(
                        "D5/S1/Phase/SeatTowerConsequences.mod_ninety_six_refines_twenty_four_and_forty_eight"),
                    In(Seq(Forall, Sp, F.Id("a"), Comma, F.Id("b"), InMacro, Mathbb, Grp(F.Id("Z")), Comma, Esc, F.Id("a"), Equiv, Sp, F.Id("b"), Esc, OpenBracket, Operatorname, Grp(F.Id("mod")), Esc, D(9, 6), CloseBracket, Sp, Rightarrow, Sp, F.Id("a"), Equiv, Sp, F.Id("b"), Esc, OpenBracket, Operatorname, Grp(F.Id("mod")), Esc, D(2, 4), CloseBracket, Sp, Land, Sp, F.Id("a"), Equiv, Sp, F.Id("b"), Esc, OpenBracket, Operatorname, Grp(F.Id("mod")), Esc, D(4, 8), CloseBracket)),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "An explicit congruence modulo 96 implies congruence modulo 24 and modulo 48. This does not supply the finite conflict table or identify a residue with an orbit selector.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("jacobi-selector-factorization"),
                    H("An identified selector numerator splits into three Jacobi factors"),
                    LeanTheorem(
                        "D5/S1/Phase/SeatTowerConsequences.jacobi_factorization_of_selector_numerator"),
                    Disp(Seq(Forall, Sp, Beta, Comma, F.Id("j"), InMacro, Mathbb, Grp(F.Id("Z")), Comma, Esc, Forall, Sp, F.Id("n"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc, F.Id("j"), Eq, Left, Open, Frac, Grp(D(2), Open, Minus, D(1), Close, Beta), Grp(F.Id("n")), Right, Close, Sp, Rightarrow, Sp, F.Id("j"), Eq, Left, Open, Frac, Grp(D(2)), Grp(F.Id("n")), Right, Close, Left, Open, Frac, Grp(Minus, D(1)), Grp(F.Id("n")), Right, Close, Left, Open, Frac, Grp(Beta), Grp(F.Id("n")), Right, Close)),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "The selector is assumed to equal the Jacobi symbol with numerator 2(-1)beta. Multiplicativity then yields the three factors; the Zolotarev congruence bridge and the 144-case certificate remain open.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("cosecant-peak-rearrangement"),
                    H("The peak equation rearranges to the cosecant expression"),
                    LeanTheorem(
                        "D5/S1/Phase/SeatTowerConsequences.cosecant_peak_identity"),
                    Disp(Seq(Forall, Sp, F.Id("r"), Comma, Theta, InMacro, Mathbb, Grp(F.Id("R")), Comma, Esc, Sin, Theta, Neq, Sp, D(0), Sp, Land, Sp, D(2), F.Id("r"), Sin, Theta, Eq, Sqrt, Grp(D(3)), Sp, Rightarrow, Sp, F.Id("r"), Eq, Frac, Grp(Sqrt, Grp(D(3))), Grp(D(2), Sin, Theta))),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "A nonzero sine and the explicit peak equation imply the displayed quotient. The theorem does not derive that equation from pin data or choose an angle branch.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("dominant-term-gap-bound"),
                    H("The leading term controls the finite-sum gap"),
                    LeanTheorem(
                        "D5/S1/Phase/SeatTowerConsequences.dominant_term_gap_bound"),
                    Disp(Seq(Forall, Sp, Alpha, Comma, Esc, Forall, Sp, F.Id("a"), InMacro, Mathbb, Grp(F.Id("Z")), Comma, Esc, Forall, Sp, F.Id("S"), Subset, Underscore, Grp(Mathrm, Grp(F.Id("fin"))), Alpha, Comma, Esc, Forall, Sp, F.Id("f"), Colon, Alpha, To, Mathbb, Grp(F.Id("Z")), Comma, Esc, Bar, F.Id("a"), Bar, Minus, Sum, Underscore, Grp(F.Id("i"), InMacro, Sp, F.Id("S")), Bar, F.Id("f"), Open, F.Id("i"), Close, Bar, Leq, Left, Bar, F.Id("a"), Plus, Sum, Underscore, Grp(F.Id("i"), InMacro, Sp, F.Id("S")), F.Id("f"), Open, F.Id("i"), Close, Right, Bar)),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "The reverse triangle inequality bounds the absolute full sum below by the leading absolute value minus the total absolute remainder. No continued-fraction dominance premise or 66-case certificate is inferred.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("singleton-stationing-count"),
                    H("There are n singleton choices among n labeled factors"),
                    LeanTheorem(
                        "D5/S1/Phase/SeatTowerConsequences.singleton_stationing_choice_count"),
                    In(Seq(Forall, Sp, F.Id("n"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc, Operatorname, Grp(F.Id("card")), OpenBrace, F.Id("S"), Subseteq, Operatorname, Grp(F.Id("Fin")), Open, F.Id("n"), Close, Mid, Sp, Bar, F.Id("S"), Bar, Eq, D(1), CloseBrace, Eq, F.Id("n"))),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "The one-element subsets of n labeled factors have cardinality n. This is a combination-counting statement and does not identify actual orbits with those subsets.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("three-factor-singleton-count"),
                    H("Three labeled factors have three singleton choices"),
                    LeanTheorem(
                        "D5/S1/Phase/SeatTowerConsequences.three_split_primes_have_three_singleton_choices"),
                    In(Seq(Operatorname, Grp(F.Id("card")), OpenBrace, F.Id("S"), Subseteq, Operatorname, Grp(F.Id("Fin")), Open, D(3), Close, Mid, Sp, Bar, F.Id("S"), Bar, Eq, D(1), CloseBrace, Eq, D(3))),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Specializing the combination count to three gives three choices. This does not identify actual orbits of the 1729 example or prove the required orbit-to-choice bijection.")))
                ))));
}

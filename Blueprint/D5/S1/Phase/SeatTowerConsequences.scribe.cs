using static StrataLint.Scribe.DefinitionDsl;

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
                    LatexStatement.Create(@"$\forall a,b\in\mathbb{Z},\ a\equiv b\ [\operatorname{mod}\ 96] \Rightarrow a\equiv b\ [\operatorname{mod}\ 24] \land a\equiv b\ [\operatorname{mod}\ 48]$"),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "An explicit congruence modulo 96 implies congruence modulo 24 and modulo 48. This does not supply the finite conflict table or identify a residue with an orbit selector.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("jacobi-selector-factorization"),
                    H("An identified selector numerator splits into three Jacobi factors"),
                    LeanTheorem(
                        "D5/S1/Phase/SeatTowerConsequences.jacobi_factorization_of_selector_numerator"),
                    LatexStatement.Create(@"$$\forall \beta,j\in\mathbb{Z},\ \forall n\in\mathbb{N},\ j=\left(\frac{2(-1)\beta}{n}\right) \Rightarrow j=\left(\frac{2}{n}\right)\left(\frac{-1}{n}\right)\left(\frac{\beta}{n}\right)$$"),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "The selector is assumed to equal the Jacobi symbol with numerator 2(-1)beta. Multiplicativity then yields the three factors; the Zolotarev congruence bridge and the 144-case certificate remain open.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("cosecant-peak-rearrangement"),
                    H("The peak equation rearranges to the cosecant expression"),
                    LeanTheorem(
                        "D5/S1/Phase/SeatTowerConsequences.cosecant_peak_identity"),
                    LatexStatement.Create(@"$$\forall r,\theta\in\mathbb{R},\ \sin\theta\neq 0 \land 2r\sin\theta=\sqrt{3} \Rightarrow r=\frac{\sqrt{3}}{2\sin\theta}$$"),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "A nonzero sine and the explicit peak equation imply the displayed quotient. The theorem does not derive that equation from pin data or choose an angle branch.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("dominant-term-gap-bound"),
                    H("The leading term controls the finite-sum gap"),
                    LeanTheorem(
                        "D5/S1/Phase/SeatTowerConsequences.dominant_term_gap_bound"),
                    LatexStatement.Create(@"$$\forall \alpha,\ \forall a\in\mathbb{Z},\ \forall S\subset_{\mathrm{fin}}\alpha,\ \forall f:\alpha\to\mathbb{Z},\ |a|-\sum_{i\in S}|f(i)|\leq\left|a+\sum_{i\in S}f(i)\right|$$"),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "The reverse triangle inequality bounds the absolute full sum below by the leading absolute value minus the total absolute remainder. No continued-fraction dominance premise or 66-case certificate is inferred.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("singleton-stationing-count"),
                    H("There are n singleton choices among n labeled factors"),
                    LeanTheorem(
                        "D5/S1/Phase/SeatTowerConsequences.singleton_stationing_choice_count"),
                    LatexStatement.Create(@"$\forall n\in\mathbb{N},\ \operatorname{card}\{S\subseteq\operatorname{Fin}(n)\mid |S|=1\}=n$"),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "The one-element subsets of n labeled factors have cardinality n. This is a combination-counting statement and does not identify actual orbits with those subsets.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("three-factor-singleton-count"),
                    H("Three labeled factors have three singleton choices"),
                    LeanTheorem(
                        "D5/S1/Phase/SeatTowerConsequences.three_split_primes_have_three_singleton_choices"),
                    LatexStatement.Create(@"$\operatorname{card}\{S\subseteq\operatorname{Fin}(3)\mid |S|=1\}=3$"),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Specializing the combination count to three gives three choices. This does not identify actual orbits of the 1729 example or prove the required orbit-to-choice bijection.")))
                ))));
}

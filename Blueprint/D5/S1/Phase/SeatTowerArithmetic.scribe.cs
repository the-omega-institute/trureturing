using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Phase;

internal sealed class SeatTowerArithmeticDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S1/Phase/SeatTowerArithmetic",
                "Isolate the arithmetic reductions used by the seat-tower selector, walk formula, input gate, and divisibility floor."),
            H("Seat-Tower Arithmetic"),
            Blocks(
                Paragraph(Text(
                    "This module records five arithmetic reductions with all structural premises explicit. It does not prove the Jacobi selector, identify canonical W3 data, validate orbit inputs, or extend finite observations to measurable claims.")),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("mod-twenty-four-dichotomy"),
                    H("Multiples of twelve have two residues modulo twenty-four"),
                    LeanTheorem(
                        "D5/S1/Phase/SeatTowerArithmetic.mod_twenty_four_eq_zero_or_twelve"),
                    LatexStatement.Create(@"$\forall \psi,q\in\mathbb{Z},\ \psi=12q \Rightarrow (\psi\operatorname{mod}24=0 \lor \psi\operatorname{mod}24=12)$"),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "If an integer is explicitly written as twelve times a quotient, its residue modulo twenty-four is zero or twelve. No orbit divisibility premise is inferred.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("quotient-parity-selector"),
                    H("Divisibility by twenty-four is quotient parity"),
                    LeanTheorem(
                        "D5/S1/Phase/SeatTowerArithmetic.twenty_four_dvd_iff_even_quotient"),
                    LatexStatement.Create(@"$\forall \psi,q\in\mathbb{Z},\ \psi=12q \Rightarrow (24\mid\psi \Leftrightarrow 2\mid q)$"),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Under the same explicit factorization by twelve, divisibility by twenty-four is equivalent to evenness of the quotient. The theorem does not identify that parity with a Jacobi symbol.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("bhk-algebraic-rearrangement"),
                    H("The BHK and Rademacher hypotheses rearrange to the walk expression"),
                    LeanTheorem(
                        "D5/S1/Phase/SeatTowerArithmetic.bhk_implies_w3_walk"),
                    LatexStatement.Create(@"$$\forall s,a,l,r,l',r',c,\phi\in\mathbb{Q},\ c\neq 0 \land 12s=-3+\frac{l'+r'}{c}-a \land \phi=\frac{l+r}{c}-12s \Rightarrow \phi=3+a+\frac{(l+r)-(l'+r')}{c}$$"),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "For rational variables and a nonzero denominator, the displayed conclusion follows algebraically from explicit BHK and Rademacher equations. This is not a typed identification theorem for canonical W3 data.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("pythagorean-gate-normalization"),
                    H("The Pythagorean equation normalizes to an Eisenstein norm"),
                    LeanTheorem(
                        "D5/S1/Phase/SeatTowerArithmetic.pythagorean_gate_iff_eisenstein_norm"),
                    LatexStatement.Create(@"$$\forall \beta,\gamma_{0},m\in\mathbb{Z},\ (\gamma_{0}-2\beta)^{2}+3\gamma_{0}^{2}=4m(m+1) \Leftrightarrow \beta^{2}-\beta\gamma_{0}+\gamma_{0}^{2}=m(m+1)$$"),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "The two integer polynomial equations are equivalent by normalization. The theorem does not prove that actual orbit parameters satisfy either equation and does not validate narrative input data.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("nonzero-divisibility-floor"),
                    H("A nonzero multiple of twelve has absolute value at least twelve"),
                    LeanTheorem(
                        "D5/S1/Phase/SeatTowerArithmetic.twelve_le_abs_of_dvd_of_ne_zero"),
                    LatexStatement.Create(@"$\forall \psi\in\mathbb{Z},\ 12\mid\psi \land \psi\neq 0 \Rightarrow 12\leq |\psi|$"),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Explicit divisibility by twelve and nonzeroness imply the absolute-value floor. No sampled congruence, asymptotic law, or measurable statement is closed.")))
                ))));
}

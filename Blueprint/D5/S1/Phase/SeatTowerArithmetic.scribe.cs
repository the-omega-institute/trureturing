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
                new DocumentBlock.Describe(
                    DescribeId.Create("mod-twenty-four-dichotomy"),
                    DescribeKind.Theorem,
                    H("Multiples of twelve have two residues modulo twenty-four"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Phase/SeatTowerArithmetic.mod_twenty_four_eq_zero_or_twelve")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "If an integer is explicitly written as twelve times a quotient, its residue modulo twenty-four is zero or twelve. No orbit divisibility premise is inferred.")))),
                new DocumentBlock.Describe(
                    DescribeId.Create("quotient-parity-selector"),
                    DescribeKind.Theorem,
                    H("Divisibility by twenty-four is quotient parity"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Phase/SeatTowerArithmetic.twenty_four_dvd_iff_even_quotient")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Under the same explicit factorization by twelve, divisibility by twenty-four is equivalent to evenness of the quotient. The theorem does not identify that parity with a Jacobi symbol.")))),
                new DocumentBlock.Describe(
                    DescribeId.Create("bhk-algebraic-rearrangement"),
                    DescribeKind.Theorem,
                    H("The BHK and Rademacher hypotheses rearrange to the walk expression"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Phase/SeatTowerArithmetic.bhk_implies_w3_walk")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "For rational variables and a nonzero denominator, the displayed conclusion follows algebraically from explicit BHK and Rademacher equations. This is not a typed identification theorem for canonical W3 data.")))),
                new DocumentBlock.Describe(
                    DescribeId.Create("pythagorean-gate-normalization"),
                    DescribeKind.Theorem,
                    H("The Pythagorean equation normalizes to an Eisenstein norm"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Phase/SeatTowerArithmetic.pythagorean_gate_iff_eisenstein_norm")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "The two integer polynomial equations are equivalent by normalization. The theorem does not prove that actual orbit parameters satisfy either equation and does not validate narrative input data.")))),
                new DocumentBlock.Describe(
                    DescribeId.Create("nonzero-divisibility-floor"),
                    DescribeKind.Theorem,
                    H("A nonzero multiple of twelve has absolute value at least twelve"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Phase/SeatTowerArithmetic.twelve_le_abs_of_dvd_of_ne_zero")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Explicit divisibility by twelve and nonzeroness imply the absolute-value floor. No sampled congruence, asymptotic law, or measurable statement is closed.")))))));
}

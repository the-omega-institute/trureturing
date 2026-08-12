using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Phase;

internal sealed class SeatTowerArithmeticDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeNode.Create("Isolate the arithmetic reductions used by the seat-tower selector, walk formula, input gate, and divisibility floor.",
H("Seat-Tower Arithmetic"),
Blocks(
                Paragraph(Text(
                    "This module records five arithmetic reductions with all structural premises explicit. It does not prove the Jacobi selector, identify canonical W3 data, validate orbit inputs, or extend finite observations to measurable claims.")),
                Describe.Lean(
                    DescribeId.Create("mod-twenty-four-dichotomy"),
                    DeclarationHandle.Create("D5/S1/Phase/SeatTowerArithmetic.mod_twenty_four_eq_zero_or_twelve"),
                    H("Multiples of twelve have two residues modulo twenty-four"),
                    StatementSource.FromAuthor(In(Seq(Forall, Sp, Psi, Comma, F.Id("q"), InMacro, Mathbb, Grp(F.Id("Z")), Comma, Esc, Psi, Eq, D(1, 2), F.Id("q"), Sp, Rightarrow, Sp, Open, Psi, Operatorname, Grp(F.Id("mod")), D(2, 4), Eq, D(0), Sp, Lor, Sp, Psi, Operatorname, Grp(F.Id("mod")), D(2, 4), Eq, D(1, 2), Close))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "If an integer is explicitly written as twelve times a quotient, its residue modulo twenty-four is zero or twelve. No orbit divisibility premise is inferred."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("quotient-parity-selector"),
                    DeclarationHandle.Create("D5/S1/Phase/SeatTowerArithmetic.twenty_four_dvd_iff_even_quotient"),
                    H("Divisibility by twenty-four is quotient parity"),
                    StatementSource.FromAuthor(In(Seq(Forall, Sp, Psi, Comma, F.Id("q"), InMacro, Mathbb, Grp(F.Id("Z")), Comma, Esc, Psi, Eq, D(1, 2), F.Id("q"), Sp, Rightarrow, Sp, Open, D(2, 4), Mid, Psi, Sp, Leftrightarrow, Sp, D(2), Mid, Sp, F.Id("q"), Close))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Under the same explicit factorization by twelve, divisibility by twenty-four is equivalent to evenness of the quotient. The theorem does not identify that parity with a Jacobi symbol."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("bhk-algebraic-rearrangement"),
                    DeclarationHandle.Create("D5/S1/Phase/SeatTowerArithmetic.bhk_implies_w3_walk"),
                    H("The BHK and Rademacher hypotheses rearrange to the walk expression"),
                    StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("s"), Comma, F.Id("a"), Comma, F.Id("l"), Comma, F.Id("r"), Comma, F.Id("l"), Apos, Comma, F.Id("r"), Apos, Comma, F.Id("c"), Comma, Phi, InMacro, Mathbb, Grp(F.Id("Q")), Comma, Esc, F.Id("c"), Neq, Sp, D(0), Sp, Land, Sp, D(1, 2), F.Id("s"), Eq, Minus, D(3), Plus, Frac, Grp(F.Id("l"), Apos, Plus, F.Id("r"), Apos), Grp(F.Id("c")), Minus, F.Id("a"), Sp, Land, Sp, Phi, Eq, Frac, Grp(F.Id("l"), Plus, F.Id("r")), Grp(F.Id("c")), Minus, D(1, 2), F.Id("s"), Sp, Rightarrow, Sp, Phi, Eq, D(3), Plus, F.Id("a"), Plus, Frac, Grp(Open, F.Id("l"), Plus, F.Id("r"), Close, Minus, Open, F.Id("l"), Apos, Plus, F.Id("r"), Apos, Close), Grp(F.Id("c"))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "For rational variables and a nonzero denominator, the displayed conclusion follows algebraically from explicit BHK and Rademacher equations. This is not a typed identification theorem for canonical W3 data."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("pythagorean-gate-normalization"),
                    DeclarationHandle.Create("D5/S1/Phase/SeatTowerArithmetic.pythagorean_gate_iff_eisenstein_norm"),
                    H("The Pythagorean equation normalizes to an Eisenstein norm"),
                    StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Beta, Comma, GammaLower, Underscore, Grp(D(0)), Comma, F.Id("m"), InMacro, Mathbb, Grp(F.Id("Z")), Comma, Esc, Open, GammaLower, Underscore, Grp(D(0)), Minus, D(2), Beta, Close, Caret, Grp(D(2)), Plus, D(3), GammaLower, Underscore, Grp(D(0)), Caret, Grp(D(2)), Eq, D(4), F.Id("m"), Open, F.Id("m"), Plus, D(1), Close, Sp, Leftrightarrow, Sp, Beta, Caret, Grp(D(2)), Minus, Beta, GammaLower, Underscore, Grp(D(0)), Plus, GammaLower, Underscore, Grp(D(0)), Caret, Grp(D(2)), Eq, F.Id("m"), Open, F.Id("m"), Plus, D(1), Close))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The two integer polynomial equations are equivalent by normalization. The theorem does not prove that actual orbit parameters satisfy either equation and does not validate narrative input data."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("nonzero-divisibility-floor"),
                    DeclarationHandle.Create("D5/S1/Phase/SeatTowerArithmetic.twelve_le_abs_of_dvd_of_ne_zero"),
                    H("A nonzero multiple of twelve has absolute value at least twelve"),
                    StatementSource.FromAuthor(In(Seq(Forall, Sp, Psi, InMacro, Mathbb, Grp(F.Id("Z")), Comma, Esc, D(1, 2), Mid, Psi, Sp, Land, Sp, Psi, Neq, Sp, D(0), Sp, Rightarrow, Sp, D(1, 2), Leq, Sp, Bar, Psi, Bar))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Explicit divisibility by twelve and nonzeroness imply the absolute-value floor. No sampled congruence, asymptotic law, or measurable statement is closed."))),
                    DescribeRole.Theorem))));
}

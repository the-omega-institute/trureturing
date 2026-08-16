using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Sharpness;

internal sealed class SpectralPairingCapacityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Doubly stochastic mixing cannot increase spectral pairing capacity.",
        H("Spectral Pairing Capacity Is Monotone under Majorization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("spectral-pairing-capacity-monotone"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Sharpness/SpectralPairingCapacity."
                    + "spectral_pairing_capacity_monotone_of_doubly_stochastic"),
                H("Doubly stochastic mixing cannot increase spectral pairing capacity"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("C"), Underscore, F.Id("a"), Open, F.Id("r"), Close, Sp, Eq, Sp,
                    Frac, Grp(D(1)), Grp(D(2)), Sum, Underscore, F.Id("i"), Sp,
                    F.Id("r"), Underscore, F.Id("i"),
                    Open, F.Id("a"), Underscore, F.Id("i"), Sp, Minus, Sp,
                    F.Id("a"), Underscore,
                    Grp(Operatorname, Grp(F.Id("rev")), Sp, F.Id("i")), Close,
                    RowBreak,
                    F.Id("r"), Sp, Eq, Sp, F.Id("S"), Sp, F.Id("r"), Apos, Sp, Land, Sp,
                    Operatorname, Grp(F.Id("DS")), Open, F.Id("S"), Close, Sp, Land, Sp,
                    Operatorname, Grp(F.Id("Antitone")), Open, F.Id("r"), Apos, Close, Sp,
                    Land, Sp, Operatorname, Grp(F.Id("Antitone")), Open, F.Id("a"), Close,
                    Sp, Rightarrow, Sp,
                    F.Id("C"), Underscore, F.Id("a"), Open, F.Id("r"), Close, Sp, Le, Sp,
                    F.Id("C"), Underscore, F.Id("a"), Open, F.Id("r"), Apos, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a finite state spectrum r and observable spectrum a, the spectral "
                        + "pairing capacity is C_a(r) = (1/2) sum_i r_i (a_i - a_{rev i}). "
                        + "Suppose r' and a are nonincreasing and r = S r' for a doubly stochastic "
                        + "matrix S. This is the standard doubly stochastic witness that r is "
                        + "majorized by r'. Then C_a(r) is at most C_a(r').")),
                    Paragraph(Text(
                        "The observable gap i maps to a_i - a_{rev i}; it is nonincreasing because "
                        + "a is nonincreasing while reversal changes the order. The proof applies "
                        + "the existing bilinear doubly-stochastic inequality to this gap and r'. "
                        + "That inequality is built from the Birkhoff-von Neumann decomposition and "
                        + "mathlib's rearrangement inequality, so those results are reused rather "
                        + "than reproved.")),
                    Paragraph(Text(
                        "This statement closes only the majorization-monotonicity clause of the "
                        + "source theorem and records its spectral-pairing closed form as a "
                        + "definition. It does not claim the full unitary trace range, the pure-state "
                        + "distance formula, the qubit Bloch-radius reduction, or the source's "
                        + "remaining geometric interpretation."))),
                DescribeRole.Theorem))));
}

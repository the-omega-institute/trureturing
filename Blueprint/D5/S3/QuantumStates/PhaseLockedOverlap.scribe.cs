using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumStates;

internal sealed class PhaseLockedOverlapDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unit-phase conjugation locks a complex overlap to a rotated real line.",
        H("Phase-Locked Overlaps"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unit-phase-conjugation-locks-an-overlap-to-a-rotated-real-line"),
                DeclarationHandle.Create(
                    "D5/S3/QuantumStates/PhaseLockedOverlap.phase_locked_overlap_is_rotated_real"),
                H("A phase-locked overlap lies on a rotated real line"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("u"), Comma, F.Id("c"), InMacro, Sp,
                    Mathbb, Grp(F.Id("C")), Comma, Esc,
                    Vert, Sp, F.Id("u"), Sp, Vert, Eq, D(1), Sp, Land, Sp,
                    Overline, Grp(F.Id("c")), Eq,
                    Open, F.Id("u"), Caret, Grp(Minus, D(1)), Close,
                    Caret, Grp(D(2)), Sp, F.Id("c"), Sp, Rightarrow, Sp,
                    Exists, Sp, F.Id("r"), InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Esc,
                    F.Id("c"), Eq, F.Id("u"), Sp, F.Id("r")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let u be a complex unit phase and c a complex overlap. If conjugating c multiplies it by the square of the inverse phase, then c equals u times a real number. Thus the overlap lies on the real axis rotated by u.")),
                    Paragraph(Text(
                        "The proof rotates the overlap back by the inverse phase. Mathlib identifies the inverse of a unit-modulus complex number with its conjugate; the locking equation then makes the rotated value self-adjoint, and Mathlib's self-adjoint complex-number lemma realizes it as a real scalar.")),
                    Paragraph(Text(
                        "This declaration closes only the scalar phase-line conclusion of the source's two-torsion theorem. It does not construct Weyl displacement operators, certify the dimension-eight or dimension-twenty-four data, classify three-torsion or six-torsion orbits, or claim the later visibility mechanism."))),
                DescribeRole.Theorem))));
}

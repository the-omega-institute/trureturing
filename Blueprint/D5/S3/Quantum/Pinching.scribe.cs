using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum;

internal sealed class PinchingDocument : IScribeDocumentDefinition
{
    private static LeanDeclarationRef LeanDefinition(string value) =>
        LeanDeclarationRef.Create(
            value,
            expectedKind: LeanDeclarationKind.Definition,
            requireNoSorry: true);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Quantum/Pinching",
            "Standard-basis qubit pinching is an idempotent Hilbert-Schmidt projection with exact forcing tests."),
        H("Standard-Basis Qubit Pinching"),
        Blocks(
            DocumentBlock.Describe.Definition(
                DescribeId.Create("standard-basis-pinching-is-zero-retention-phase-damping"),
                H("Standard-basis pinching is zero-retention phase damping"),
                LeanDefinition("D5/S3/Quantum/Pinching.pinching"),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "For an arbitrary complex two-by-two matrix rho, pinching is exactly the existing phaseDamping map at coherence-retention coefficient zero. Thus diagonal entries are preserved and all off-diagonal entries are annihilated. No parallel channel definition, positivity premise, Hermiticity premise, or trace-one premise is introduced."))),
                Disp(Seq(
                    F.Id("P"), Open, Rho, Close, Eq,
                    Operatorname, Grp(F.Id("phaseDamping")), Open, D(0), Comma, Rho, Close))
            ),
            DocumentBlock.Describe.Definition(
                DescribeId.Create("the-hilbert-schmidt-pairing-is-the-trace-pairing"),
                H("The Hilbert-Schmidt pairing is the trace pairing"),
                LeanDefinition("D5/S3/Quantum/Pinching.hilbertSchmidtInner"),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "For qubit matrices A and B, the scalar pairing is trace of the conjugate transpose of A times B. Mathlib supplies matrix trace and conjugate transpose, but its Frobenius matrix scope does not install an Inner instance for Matrix, so this declaration is the minimal formula-level wrapper rather than a competing inner-product-space structure."))),
                Disp(Seq(
                    Langle, Sp, F.Id("A"), Comma, Sp, F.Id("B"), Rangle,
                    Underscore, Grp(F.Id("HS")), Eq,
                    Operatorname, Grp(F.Id("Tr")), Open,
                    F.Id("A"), Caret, Grp(Star), F.Id("B"), Close))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("pinching-is-idempotent"),
                H("Pinching is idempotent"),
                LeanTheorem("D5/S3/Quantum/Pinching.pinching_idempotent"),
                Disp(Seq(F.Id("P"), Sp, Circ, Sp, F.Id("P"), Eq, F.Id("P"))),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "Applying standard-basis pinching twice is the same function as applying it once. The equality is extensional over every complex two-by-two input and every matrix entry.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("pinching-is-hilbert-schmidt-self-adjoint"),
                H("Pinching is Hilbert-Schmidt self-adjoint"),
                LeanTheorem(
                    "D5/S3/Quantum/Pinching.pinching_hilbert_schmidt_self_adjoint"),
                Disp(Seq(
                    Forall, Sp, F.Id("A"), Comma, F.Id("B"), Sp, InMacro, Sp,
                    F.Id("M"), Underscore, Grp(D(2)), Open, Mathbb, Grp(F.Id("C")), Close,
                    Comma, Esc,
                    Langle, Sp, F.Id("P"), Open, F.Id("A"), Close, Comma, Sp, F.Id("B"),
                    Rangle, Underscore, Grp(F.Id("HS")), Eq,
                    Langle, Sp, F.Id("A"), Comma, Sp, F.Id("P"), Open, F.Id("B"), Close,
                    Rangle, Underscore, Grp(F.Id("HS")))),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "The Hilbert-Schmidt pairing is unchanged when pinching is moved from the first argument to the second. Entrywise expansion leaves exactly the two diagonal contributions on both sides, proving the full scalar equality rather than only equality of real parts, norms, or zero sets.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("zero-entries-force-complete-off-diagonal-elimination"),
                H("Zero entries force complete off-diagonal elimination"),
                LeanTheorem("D5/S3/Quantum/Pinching.pinching_entry_eq_zero_iff"),
                Disp(Seq(
                    Forall, Sp, Rho, Comma, F.Id("i"), Comma, F.Id("j"), Comma, Esc,
                    Open, F.Id("P"), Open, Rho, Close, Close,
                    Underscore, Grp(F.Id("ij")), Eq, D(0), Sp, Leftrightarrow, Sp,
                    F.Id("i"), Neq, Sp, F.Id("j"), Sp, Lor, Sp,
                    Rho, Underscore, Grp(F.Id("ij")), Eq, D(0))),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "For every matrix and every pair of standard-basis indices, a pinched entry is zero exactly when it is off diagonal or the original entry was already zero. A weakened map retaining any nonzero multiple of a nonzero off-diagonal entry cannot satisfy this equivalence.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("pinching-annihilates-the-purely-off-diagonal-pauli-x"),
                H("Pinching annihilates the purely off-diagonal Pauli X"),
                LeanTheorem(
                    "D5/S3/Quantum/Pinching.pinching_annihilates_offdiagonal"),
                Disp(Seq(
                    Langle, Sp, F.Id("P"), Open, F.Id("X"), Close, Comma, Sp, F.Id("X"),
                    Rangle, Underscore, Grp(F.Id("HS")), Eq, D(0), Sp, Land, Sp,
                    Langle, Sp, F.Id("X"), Comma, Sp, F.Id("X"),
                    Rangle, Underscore, Grp(F.Id("HS")), Neq, Sp, D(0))),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "The Pauli X matrix is purely off diagonal, so pinching sends it to zero while its own Hilbert-Schmidt norm stays nonzero. Any map that merely attenuates coherence, retaining a nonzero multiple of the off-diagonal weight, falsifies the first conjunct, so this pair separates pinching from every partial damping channel."))
            )))));
}

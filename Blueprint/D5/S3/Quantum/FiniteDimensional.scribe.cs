using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum;

internal sealed class FiniteDimensionalDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Schwinger = LibraryNoteRef.Create("D5/L/schwinger1960unitary");
    private static readonly LibraryNoteRef Murphy = LibraryNoteRef.Create("D5/L/murphy1990calgebras");
    private static readonly LibraryNoteRef Gleason = LibraryNoteRef.Create("D5/L/gleason1957measures");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Quantum/FiniteDimensional",
            "Finite-dimensional Pauli, no-character, and trace-probability skeletons."),
        H("Finite-Dimensional Quantum Skeletons"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("the-standard-qubit-weyl-pair-has-the-pauli-star-skeleton"),
                H("The standard qubit Weyl pair has the Pauli star skeleton"),
                LeanTheorem("D5/S3/Quantum/FiniteDimensional.qubit_weyl_star"),
                In(Seq(F.Id("ZX"), Eq, Minus, Open, F.Id("XZ"), Close, Sp, Land, Sp, F.Id("X"), Caret, Grp(Star), Eq, F.Id("X"), Sp, Land, Sp, F.Id("Z"), Caret, Grp(Star), Eq, F.Id("Z"), Sp, Land, Sp, F.Id("X"), Caret, Grp(D(2)), Eq, F.Id("I"), Sp, Land, Sp, F.Id("Z"), Caret, Grp(D(2)), Eq, F.Id("I"))),
                DescribeProvenance.LiteratureAttested(Schwinger),
                Blocks(Paragraph(Text(
                    "The standard two-dimensional Pauli X and Z matrices anticommute, are self-adjoint, and square to the identity. This is only the d = 2 Weyl specialization: it does not identify an arbitrary observer window with a full matrix algebra, prove prime-power tensor factorization or a general qudit relation, or derive the structure from a classical ontology. Original numerical-certificate claim not formalized: the source atom's matrix-unit relations with exact zero certificate error.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("the-qubit-matrix-algebra-has-no-complex-algebra-character"),
                H("The qubit matrix algebra has no complex-algebra character"),
                LeanTheorem("D5/S3/Quantum/FiniteDimensional.qubit_matrix_algebra_has_no_character"),
                In(Seq(Operatorname, Grp(F.Id("IsEmpty")), Open, Operatorname, Grp(F.Id("QubitMatrix")), To, Underscore, Grp(Mathbb, Grp(F.Id("C")), F.Text, Grp(Minus, F.Id("alg"))), Mathbb, Grp(F.Id("C")), Close)),
                DescribeProvenance.LiteratureAttested(Murphy),
                Blocks(Paragraph(
                    Text("No unital complex-algebra homomorphism from the two-by-two full matrix algebra to the complex numbers exists. The proof uses the stronger global additive and multiplicative laws of an algebra character. "),
                    Ref("D5/L/kochen1968problem"),
                    Text(" is contextual background only: this declaration is not the Kochen-Specker valuation theorem, does not exclude qubit noncontextual projection valuations, and proves neither the arbitrary M_n result for n greater than one nor any CHSH, hidden-address, or probability-is-not-ignorance claim.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("positive-trace-one-matrices-give-nonnegative-projection-weights"),
                H("Positive trace-one matrices give nonnegative projection weights"),
                LeanTheorem("D5/S3/Quantum/FiniteDimensional.born_probability_skeleton"),
                Disp(Seq(Forall, Sp, F.Id("n"), Esc, OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, F.Id("n"), Close, CloseBracket, Esc, OpenBracket, Operatorname, Grp(F.Id("DecidableEq")), Open, F.Id("n"), Close, CloseBracket, Comma, Esc, Forall, Sp, Rho, Sp, InMacro, Sp, F.Id("M"), Underscore, Grp(F.Id("n")), Open, Mathbb, Grp(F.Id("C")), Close, Comma, Esc, Operatorname, Grp(F.Id("PosSemidef")), Open, Rho, Close, Sp, Land, Sp, Operatorname, Grp(F.Id("tr")), Open, Rho, Close, Eq, D(1), Sp, Rightarrow, Sp, Operatorname, Grp(F.Id("bornProbability")), Open, Rho, Comma, F.Id("I"), Close, Eq, D(1), Sp, Land, Sp, Open, Forall, Sp, F.Id("P"), Comma, F.Id("Q"), Comma, Esc, Operatorname, Grp(F.Id("bornProbability")), Open, Rho, Comma, F.Id("P"), Plus, F.Id("Q"), Close, Eq, Operatorname, Grp(F.Id("bornProbability")), Open, Rho, Comma, F.Id("P"), Close, Plus, Operatorname, Grp(F.Id("bornProbability")), Open, Rho, Comma, F.Id("Q"), Close, Close, Sp, Land, Sp, Open, Forall, Sp, F.Id("P"), Comma, Esc, F.Id("P"), Caret, Grp(Star), Eq, F.Id("P"), Sp, Rightarrow, Sp, F.Id("P"), Caret, Grp(D(2)), Eq, F.Id("P"), Sp, Rightarrow, Sp, D(0), Leq, Operatorname, Grp(F.Id("bornProbability")), Open, Rho, Comma, F.Id("P"), Close, Close)),
                DescribeProvenance.LiteratureAttested(Gleason),
                Blocks(Paragraph(
                    Text("For a positive semidefinite finite complex matrix rho with trace one, P maps to trace(rho P), is normalized at the identity, is additive, and is nonnegative for every self-adjoint idempotent P. Positivity follows from the compression P rho P* and does not assume that rho commutes with P. "),
                    Ref("D5/L/born1926zur"),
                    Text(" records the historical Born context only. The declaration proves no Gleason representation or uniqueness theorem, no rank-one pure-state modulus-square reduction, no ledger-derived noncontextuality, no harmonic or quartic numerical certificate, and no forced classical-to-quantum origin. Original numerical-certificate claim not formalized: the source atom's separate Born control group balance to 10^-16.")))
            ))));
}

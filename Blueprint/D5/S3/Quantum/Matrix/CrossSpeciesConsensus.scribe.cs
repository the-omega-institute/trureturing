using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class CrossSpeciesConsensusDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/CrossSpeciesConsensus.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A shared irreducible complex symmetry forces every equivariant Hermitian "
            + "observable to have one common real reading across normalized probes.",
        H("Conditional Cross-Species Consensus"),
        Blocks(
            Paragraph(Text(
                "Let U be a representation of any group by finite complex matrices. "
                    + "The physical inputs remain explicit: all species use this same U, "
                    + "and h_irreducible says its invariant-subspace order is simple. "
                    + "The observable A is Hermitian and commutes with every U(g). "
                    + "No claim derives these assumptions from an observer principle. "
                    + "Unitary representations are included; unitarity is not needed "
                    + "for the stated conditional result.")),
            Result("equivariant-scalar", "equivariant_selfAdjoint_eq_smul_id_of_irreducible",
                "Equivariant observables are real scalar matrices",
                "Transport U and A through the matrix-to-linear-map algebra equivalence. "
                    + "Commutation makes A an intertwining endomorphism. Schur's lemma "
                    + "makes it a complex scalar identity; Hermitian diagonal entries "
                    + "make that scalar real. The argument permits every finite dimension.",
                Disp(Seq(Call("Irreducible", F.Id("U")), Sp, Land, Sp,
                    Call("Hermitian", F.Id("A")), Sp, Land, Sp,
                    Call("Equivariant", F.Id("U"), F.Id("A")), Sp, Rightarrow, Sp,
                    Call("RealScalarIdentity", F.Id("A"))))),
            Result("species-readings", "cross_species_consensus",
                "Every normalized probe reads the same scalar",
                "For any species-indexed family rho_s with trace rho_s = 1, the theorem "
                    + "produces a single real r with A = r I and Re tr(rho_s A) = r for "
                    + "every species. Consequently any two readings agree. Positive "
                    + "density matrices satisfy the hypotheses; trace normalization "
                    + "alone suffices for the algebraic conclusion. This concerns the "
                    + "same observable, with the same calibration, for all species.",
                Disp(Seq(Call("ReTrProduct", F.Id("rho_s"), F.Id("A")), Sp, Eq, Sp,
                    F.Id("r"), Sp, Eq, Sp,
                    Call("ReTrProduct", F.Id("rho_t"), F.Id("A"))))))));

    private static DocumentBlock Result(
        string id, string declaration, string title, string text, Formula statement) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + declaration), H(title),
            StatementSource.FromAuthor(statement), AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/Quantum/mathlib2026irreducibleschur")),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}

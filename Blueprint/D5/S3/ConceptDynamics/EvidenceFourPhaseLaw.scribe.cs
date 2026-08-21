using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics;

internal sealed class EvidenceFourPhaseLawDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite evidence fiber with a decidable proposition has exactly one of four epistemic phases.",
        H("The Four-Phase Law for Finite Evidence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-evidence-fibers-have-exactly-one-phase"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/EvidenceFourPhaseLaw."
                        + "finite_classical_four_phase_law"),
                H("A finite evidence fiber has exactly one phase"),
                StatementSource.FromAuthor(FourPhaseFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The finset R represents the admissible evidence fiber R_E^A(b). "
                            + "Its membership is decidable, and the DecidablePred instance "
                            + "makes the proposition P decidable at every member.")),
                    Paragraph(Text(
                        "PhaseHolds gives the four source meanings without weakening them: "
                            + "the fiber is empty; it is nonempty and every member satisfies P; "
                            + "it is nonempty and every member refutes P; or it contains both a "
                            + "P-witness and a counterexample.")),
                    Paragraph(Text(
                        "The proof separates the empty case, the all-true case, the all-false "
                            + "case, and the remaining mixed case. In each branch, the displayed "
                            + "witnesses also refute every other phase, yielding existence and "
                            + "uniqueness rather than only a four-way disjunction.")),
                    Paragraph(Text(
                        "Repository searches found no existing four-phase evidence theorem. "
                            + "Pinned Mathlib supplies finite membership, decidable finite "
                            + "nonemptiness, and Finset.mem_filter; these generic results are "
                            + "reused directly. Four Boolean examples realize the four constructors, "
                            + "so none of the named phases is definitionally empty."))),
                DescribeRole.Theorem))));

    private static Formula FourPhaseFormula()
    {
        Formula carrier = F.Id("X");
        Formula fiber = F.Id("R");
        Formula predicate = F.Id("P");
        Formula phase = F.Id("phase");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula proposition = Seq(Operatorname, Grp(F.Id("Prop")));

        return Disp(Seq(
            Forall, Sp, carrier, Colon, Sp, type, Comma, Sp,
            fiber, Colon, Sp, Call("Finset", carrier), Comma, Sp,
            predicate, Colon, Sp, carrier, Sp, To, Sp, proposition, Comma, Esc,
            OpenBracket, Call("DecidableEq", carrier), CloseBracket, Comma, Sp,
            OpenBracket, Call("DecidablePred", predicate), CloseBracket, Comma, Esc,
            Exists, Bang, Sp, phase, Colon, Sp,
            Operatorname, Grp(F.Id("EvidencePhase")), Comma, Sp,
            Call("PhaseHolds", fiber, predicate, phase), Dot));
    }
}

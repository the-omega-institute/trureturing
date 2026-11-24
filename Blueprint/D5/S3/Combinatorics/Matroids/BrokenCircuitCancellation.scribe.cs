using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class BrokenCircuitCancellationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/BrokenCircuitCancellation";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/FiniteGeometry/leanpool2026nbccancellation");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite matroid broken-circuit cancellation by the least completer involution.",
        H("Broken-circuit cancellation for finite matroids"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("matroid-ground"),
                DeclarationHandle.Create(Module + ".matroidGround"),
                H("The finite ground subset"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a finite ambient type alpha and a matroid M on alpha, matroidGround M is the finite subset "
                    + "of M.E obtained by filtering the ambient finite universe. Elements outside M.E are excluded."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("nbc-candidate"),
                DeclarationHandle.Create(Module + ".IsNBCandidate"),
                H("A circuit-completing element"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a finite set A of the matroid ground and an element e, IsNBCandidate M A e means that "
                    + "there is a finite circuit C of M containing e, every f in C satisfies f <= e, and the "
                    + "finite set C.erase e is contained in A. Thus the broken circuit is defined by deleting a "
                    + "circuit maximum, with the full ambient carrier and ground containment retained."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("nbc-candidates"),
                DeclarationHandle.Create(Module + ".nbcCandidates"),
                H("All circuit-completing elements"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "nbcCandidates M A is the finite filter of matroidGround M consisting of all elements e for "
                    + "which a circuit witness as in IsNBCandidate M A e exists."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("nbc-bad"),
                DeclarationHandle.Create(Module + ".IsNBCBad"),
                H("A spanning-set broken-circuit witness"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "IsNBCBad M A means that nbcCandidates M A is nonempty. It records exactly the existence of "
                    + "a circuit C and a circuit maximum e whose deletion C.erase e lies in A; no loopless, rank, "
                    + "connectivity, representability, or nonempty-ground assumption is made."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("spanning-subsets"),
                DeclarationHandle.Create(Module + ".spanningSubsets"),
                H("Ground-contained spanning subsets"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "spanningSubsets M is the finite powerset of matroidGround M filtered by M.Spanning of the "
                    + "corresponding Set. It therefore ranges over every ground-contained spanning subset, including "
                    + "the empty and rank-zero cases when they occur."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-nbc-base-subsets"),
                DeclarationHandle.Create(Module + ".actualNBCBaseSubsets"),
                H("Actual no-broken-circuit bases"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "actualNBCBaseSubsets M is the finite filter of matroidGround M powerset elements A satisfying "
                    + "both M.IsBase (A : Set alpha) and not IsNBCBad M A. It is the exact actual-base survivor "
                    + "family, with M.E containment explicit and every broken circuit formed by deleting a circuit "
                    + "maximum. The family includes loops, disconnected matroids, empty grounds, and arbitrary "
                    + "ambient elements outside M.E whenever the definitions permit them."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-nbc-base-power-sum"),
                DeclarationHandle.Create(Module + ".actualNBCBasePowerSum"),
                H("The integer-power survivor sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "actualNBCBasePowerSum M sums (-1 : Int) ^ A.card over the exact actualNBCBaseSubsets M filter. "
                    + "The exponent is the finite-set cardinality and the coefficient ring is the integers."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("spanning-power-equals-actual-nbc-base-power"),
                DeclarationHandle.Create(Module + ".spanningPower_eq_actualNBCBasePower"),
                H("Broken-circuit cancellation identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "For every finite linearly ordered ambient type alpha and every Matroid alpha, the integer "
                        + "power sum (-1 : Int) ^ A.card over all A in spanningSubsets M equals "
                        + "actualNBCBasePowerSum M. The proof is the faithful least-circuit-completer port: on bad "
                        + "spanning subsets it toggles the least possible circuit maximum, whose witness remains stable "
                        + "under the toggle; this gives a span-preserving, parity-reversing, fixed-point-free involution. "
                        + "The survivors are identified using nbcBase_isBase and the base-implies-spanning direction.")),
                    Paragraph(Text(
                        "The statement covers empty ambient carriers, empty grounds, rank zero, loops, nonloopless and "
                        + "disconnected matroids, and ambient elements outside M.E. It asserts only this finite-matroid "
                        + "integer identity and makes no downstream Mayer, cohomology, characteristic-polynomial, or "
                        + "phase-convergence claim."))),
                DescribeRole.Theorem))));
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class SingleCoordinateSchurDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Schur complement bounds for pinching one coordinate.",
        H("Shifted determinants under one-coordinate pinching"),
        Blocks(Describe.Lean(
            DescribeId.Create("schur-det-log-bound"),
            DeclarationHandle.Create("D5/S3/Quantum/Divergence/SingleCoordinateSchur.schur_det_log_bound"),
            H("Schur term, determinant ratio and logarithmic deficit"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/mathlib2026schurcomplement")),
            Blocks(Paragraph(Text(
                "Let A have retained block F, coupling column h and last diagonal entry a. "
                + "Let A₀ be its pinching and let the reference be C ⊕ λ with C positive definite, "
                + "λ > 0 and C ≤ cI for c > 0. Assume u(C ⊕ λ) ≤ A ≤ v(C ⊕ λ) "
                + "in the Löwner order and 0 < d = (v − u)/2 < u. At each shift s ≥ 0, "
                + "the Schur term q = Re(h†(F + sI)⁻¹h) lies between zero and d²λc/(uc + s). "
                + "The ratio Re det(A + sI)/Re det(A₀ + sI) equals 1 − q/(a + s). "
                + "The correction q/(a + s) lies between zero and "
                + "d²λc/((uc + s)(uλ + s)), which is at most d²/u².")),
                Paragraph(Text(
                    "The signed midpoint of the two Löwner differences has diagonal blocks dC and dλ "
                    + "and coupling h. Its Schur complement yields hh† ≤ d²λC. A second block test "
                    + "uses F + sI ≥ (u + s/c)C to bound q. The logarithmic deficit "
                    + "log det(A₀ + sI) − log det(A + sI) lies between zero and "
                    + "d²λc/((uc + s)(uλ + s)(1 − d²/u²)). "
                    + "These are the pointwise estimates in Fibonacci observation entropy, proof.txt §18, "
                    + "lines 1098–1117. Section 20, lines 1259–1275, uses the integrated bound "
                    + "in the ladder comparison."))),
            DescribeRole.Theorem))));
}

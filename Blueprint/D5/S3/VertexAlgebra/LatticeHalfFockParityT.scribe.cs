using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockParityTDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeHalfFockParityT.";
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal oscillator parity on every actual finite half-Fock grade and its inserted trace.",
        H("Actual half-Fock parity and finite trace"),
        Blocks(
            Paragraph(Text("For arbitrary integral symmetric even-diagonal lattice data D, an "
                + "invertible Gram determinant hu, every natural grade N and every ground "
                + "endomorphism A, define actualParity as TensorProduct.map of the public "
                + "oscillator sigmaLinear with the genuine ground identity. The operator is "
                + "on ActualTensor, so it does not replace the separate charge-reflection theta.")),
            Describe.Lean(
                DescribeId.Create("actual-oscillator-parity"),
                DeclarationHandle.Create(Prefix + "actualParity"),
                H("The literal oscillator parity operator"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The operator is the actual oscillator involution tensored "
                    + "with identity on ActualGround. Existing sigma_monomial supplies the "
                    + "occurrence-length sign."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-parity-on-grade"),
                DeclarationHandle.Create(Prefix + "actualParity_on_actualGrade"),
                H("Parity is scalar on every actual grade vector"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("Every vector in actualGrade D hu N is sent to "
                    + "(-1)^N times itself. The proof uses the accepted actualGradeBasis, "
                    + "the equality of odd oscillator-weight parity and occurrence-count "
                    + "parity, and basis linearity; no eigenvector-only premise is added."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-parity-ground-restriction"),
                DeclarationHandle.Create(Prefix + "actualParityGroundInsertRestrict_eq_smul"),
                H("Parity after genuine ground insertion is a restricted operator"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("Compose actualParity with the existing ground insertion, "
                    + "restrict the composite to the preserved finite grade, and prove the "
                    + "operator equality to (-1)^N times actualGroundInsertRestrict. The "
                    + "restriction is genuine and carries arbitrary A."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-parity-finite-trace"),
                DeclarationHandle.Create(Prefix + "actualParityTraceTerm_eq_bRank"),
                H("The parity-inserted finite trace"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The trace is taken on the existing finite actual grade. "
                    + "Linearity of LinearMap.trace and the accepted bRank trace identity "
                    + "give (-1)^N times the ordinary finite insertion trace, including "
                    + "rank zero, N zero, zero traces and arbitrary complex A."))),
                DescribeRole.Theorem),
            Paragraph(Text("The canonical Character supplier is caller-owned and is not imported "
                + "by this checkpoint. The trace-defined parity character, absolute convergence "
                + "transport and the paired forward/reverse T laws with phases "
                + "exp(2*pi*I*rank/48), together with T squared at exp(2*pi*I*rank/24), "
                + "remain the explicit continuation obligation once that API is canonically "
                + "available. No eta rewrite, scalar proxy, positivity or even-rank premise is "
                + "introduced here.")))));
}

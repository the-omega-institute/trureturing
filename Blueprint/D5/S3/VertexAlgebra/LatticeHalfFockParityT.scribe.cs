using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockParityTDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeHalfFockParityT.";
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal oscillator parity, convergent finite-grade trace characters, and paired T and T-squared action.",
        H("Actual half-Fock parity and paired T action"),
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
            Describe.Lean(
                DescribeId.Create("actual-parity-character"),
                DeclarationHandle.Create(Prefix + "actualParityInsertedCharacter"),
                H("The trace-defined parity character"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("Use exactly exp(2*pi*I*tau*rank/48) times the series "
                    + "of LinearMap.trace on actualGrade of actualParityGroundInsertRestrict, "
                    + "weighted by exp(pi*I*tau)^N. Thus the character retains the actual "
                    + "finite restriction and the same vacuum normalization as Character."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-parity-trace-series"),
                DeclarationHandle.Create(Prefix + "actual_parity_trace_series"),
                H("Absolute convergence through the negative oscillator parameter"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("For every complex q with norm less than one, identify "
                    + "each literal parity trace coefficient with Character.actualTraceTerm at "
                    + "-q. Character.actual_trace_series applies because norm(-q)=norm(q), "
                    + "yielding absolute summability and HasSum with trace(A) times "
                    + "oddCoefficientSeries(rank,-q). No Euler or eta proof is duplicated."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-normalized-parity-series"),
                DeclarationHandle.Create(Prefix + "actual_parity_character_series"),
                H("The normalized trace series sums to the parity character"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("For every tau in the upper half-plane, the oscillator "
                    + "parameter has norm less than one. Multiplication by the retained "
                    + "vacuum exponential gives absolute summability and HasSum to "
                    + "actualParityInsertedCharacter. This convergent series is consumed "
                    + "in the forward paired T proof."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-paired-t"),
                DeclarationHandle.Create(Prefix + "actual_paired_T"),
                H("Both forward paired T laws"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The identity exp(pi*I*(tau+1))=-exp(pi*I*tau) "
                    + "interchanges the ordinary and parity trace series. The vacuum shift "
                    + "contributes phase48=exp(2*pi*I*rank/48). The two conclusions are "
                    + "character(tau+1)=phase48*parityCharacter(tau) and "
                    + "parityCharacter(tau+1)=phase48*character(tau). They are forward "
                    + "laws, retain all complex phases, and are consumed by the T-squared proof."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-paired-t-squared"),
                DeclarationHandle.Create(Prefix + "actual_paired_T_sq"),
                H("Both T-squared laws"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("Apply the paired T laws at tau and tau+1, both in "
                    + "the upper half-plane, and combine the two vacuum phases by exp_add. "
                    + "Each character at tau+2 equals exp(2*pi*I*rank/24) times itself at "
                    + "tau. Every theorem retains arbitrary lattice data D, IsUnit determinant, "
                    + "arbitrary ground endomorphism A, rank zero, grade zero and zero or "
                    + "complex trace. No positivity, even-rank premise, trace division or "
                    + "charge-reflection theta is used."))),
                DescribeRole.Theorem),
            Paragraph(Text("These results establish the oscillator-parity paired T action "
                + "on the original half-Fock trace characters. Full SL2Z closure of a sector "
                + "system, fusion, sewing, charged residue identities, and the full "
                + "Moonshine/VOA/CFT/string/AdS-CFT programme remain separate obligations.")))));
}

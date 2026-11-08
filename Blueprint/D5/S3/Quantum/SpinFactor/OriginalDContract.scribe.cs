using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.SpinFactor;

internal sealed class OriginalDContractDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete H2 original-D contract",
        H("Original scalar/vector contract and phase balance"),
        Blocks(
            Paragraph(Text("The carrier is the exact real spin factor E = R x (Fin 3 -> R), with unit (1,0), Jordan product (s,x) o (t,y) = (st + x dot y, s y + t x), cone inequality s >= sqrt(x dot x), and original norm |s| + sqrt(x dot x). Evaluations retain every mass m >= sqrt(v dot v), including zero, unequal, and subnormalized masses.")),
            Paragraph(Text("P2 is the actual directed complex 2-label Gram positivity predicate. Both diagonal entries and both directed off-diagonal readouts are formed from the same total D. PB is the original plus/minus one phase-square equality, with all inputs and both outer pairs remaining in E.")),
            Paragraph(Text("The source keeps D arbitrary. The predicates skew, zeroRows, proportionalZero, finiteDifference, and classificationStatement are named contracts for downstream consumers; no regularity, unit row, translation, bilinearity, continuity, or source realization is assumed.")),
            Describe.Lean(
                DescribeId.Create("original-d-p2"),
                DeclarationHandle.Create("D5/S3/Quantum/SpinFactor/OriginalDContract.P2"),
                H("Directed two-label positivity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every original positive evaluation and every pair of original inputs, the actual complex two-label matrix is positive semidefinite. The two directed off-diagonal entries are retained separately."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("original-d-pb"),
                DeclarationHandle.Create("D5/S3/Quantum/SpinFactor/OriginalDContract.PB"),
                H("Original plus/minus phase-square balance"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two outer pairs obtained with t = +1 and t = -1 have equal square readout for every evaluation and every original triple."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("original-d-basic-cross"),
                DeclarationHandle.Create("D5/S3/Quantum/SpinFactor/OriginalDContract.crossD_basic"),
                H("Canonical cross orientations satisfy the elementary original-D relations"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Both signs of the canonical cross-product candidate are skew, vanish on zero and proportional inputs, and therefore satisfy the basic relation contract consumed by the rigidity stages."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-d-phase-difference"),
                DeclarationHandle.Create("D5/S3/Quantum/SpinFactor/OriginalDContract.phaseBalanceDifference_zero"),
                H("Phase balance gives the original finite-difference equation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Expanding the two square readouts and using the known Jordan square identity yields the finite-difference residual consumed by the unit-row and label-rotation arguments."))),
                DescribeRole.Theorem))));
}
}

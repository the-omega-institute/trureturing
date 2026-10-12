using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.TimeArrow;

internal sealed class CalibratedArithmeticSmallBallDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer lattice bands, moving centers, and hypergeometric arithmetic estimates share one calibrated small-ball framework. The combined bounds use classical Stirling, Poisson, Littlewood-Offord, and hypergeometric estimates recorded in the repository Library/Estimation notes; the stated theorems are repository-derived.",
        H("Calibrated arithmetic small-ball bounds"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("event-mass"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.eventMass"),
                H("Finite event mass"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The mass of an integer event is the finite sum of its point masses."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("lattice-band"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.latticeBand"),
                H("Lattice band"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A lattice band keeps the integer arguments whose calibrated value lies within a fixed real radius of an integer target."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("arithmetic-event"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.arithmeticEvent"),
                H("Arithmetic small-ball event"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The central event is the union of the lattice bands indexed by the supplied integer targets."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("arithmetic-central-mass-bound"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.arithmetic_central_mass_bound"),
                H("Central arithmetic mass bound"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A real-valued calibration on the integers and a pointwise mass cap bound the central event by the number of targets times the lattice width."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integer-targets"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.integerTargets"),
                H("Integer targets in a real interval"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The integer targets are the closed integer interval between the ceiling of the lower endpoint and the floor of the upper endpoint."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("moving-center-small-ball"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.moving_center_small_ball"),
                H("Moving-center small-ball estimate"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A monotone approximation to a moving center, with lower and upper slope bounds and a tail outside the central interval, yields the displayed finite small-ball mass bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hypergeometric-arithmetic-bound"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.NativeCalibratedArithmeticBridge.hypergeometric_arithmetic_bound"),
                H("Hypergeometric arithmetic bound"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The hypergeometric count kernel satisfies a moving-center arithmetic bound under balanced margins, scale, and slope hypotheses."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hypergeometric-predicate-bound"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.NativeCalibratedArithmeticBridge.hypergeometric_predicate_bound"),
                H("Hypergeometric predicate bound"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An arbitrary predicate contained in the central lattice window is bounded by the same hypergeometric central estimate plus the kernel tail."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hypergeometric-balanced-max-atom"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.RectangleHypergeometricMaxAtom.hypergeometric_balanced_max_atom"),
                H("Balanced hypergeometric atom bound"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a fixed balance parameter, one positive constant uniformly bounds every atom of every balanced hypergeometric table."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-anchored-central-feedback"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.NativeSharedRootFeedback.native_anchored_central_feedback"),
                H("Native anchored central feedback"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The native anchored experiment supplies a common calibrated central feedback bound for the original and conditioned environments."))),
                DescribeRole.Theorem)
        )));
}

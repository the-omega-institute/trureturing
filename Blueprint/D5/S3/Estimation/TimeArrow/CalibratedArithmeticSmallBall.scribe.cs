using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.TimeArrow;

internal sealed class CalibratedArithmeticSmallBallDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer lattice bands, moving centers, and hypergeometric arithmetic estimates share one calibrated small-ball framework. Classical Stirling, Poisson, Littlewood-Offord, and hypergeometric estimates are recorded in Library/Estimation; the balanced hypergeometric maximum-atom bound is literature-attested, while the arithmetic and native calibration contracts are repository-derived.",
        H("Calibrated arithmetic small-ball bounds"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("event-mass"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.eventMass"),
                H("Finite event mass"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The mass of an integer event is the finite sum of its point masses."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("lattice-band"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.latticeBand"),
                H("Lattice band"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A lattice band keeps the integer arguments whose calibrated value lies within a fixed real radius of an integer target."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("arithmetic-event"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.arithmeticEvent"),
                H("Arithmetic small-ball event"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The central event is the union of the lattice bands indexed by the supplied integer targets."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("arithmetic-central-mass-bound"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.arithmetic_central_mass_bound"),
                H("Central arithmetic mass bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A real-valued calibration on the integers and a pointwise mass cap bound the central event by the number of targets times the lattice width."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integer-targets"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.integerTargets"),
                H("Integer targets in a real interval"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The integer targets are the closed integer interval between the ceiling of the lower endpoint and the floor of the upper endpoint."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("moving-center-small-ball"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.moving_center_small_ball"),
                H("Moving-center small-ball estimate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A monotone approximation to a moving center, with lower and upper slope bounds and a tail outside the central interval, yields the displayed finite small-ball mass bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hypergeometric-arithmetic-bound"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.hypergeometric_arithmetic_bound"),
                H("Hypergeometric arithmetic bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The hypergeometric count kernel satisfies a moving-center arithmetic bound under balanced margins, scale, and slope hypotheses."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hypergeometric-predicate-bound"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.hypergeometric_predicate_bound"),
                H("Hypergeometric predicate bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An arbitrary predicate contained in the central lattice window is bounded by the same hypergeometric central estimate plus the kernel tail."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hypergeometric-balanced-max-atom"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.hypergeometric_balanced_max_atom"),
                H("Balanced hypergeometric atom bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Estimation/lahirichatterjeemaiti2007hypergeometric")),
                Blocks(Paragraph(Text("For a fixed balance parameter, one positive constant uniformly bounds every atom of every balanced hypergeometric table."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-anchored-central-feedback"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.native_anchored_central_feedback"),
                H("Native anchored central feedback"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The native anchored experiment supplies a common calibrated central feedback bound for the original and conditioned environments."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("signal-four-reference-ratios"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.signal_four_reference_ratios"),
                H("Signal four reference ratios"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For all natural M,q,L, support S : Support M q, real r,kappa with kappa>0, r>0, r<=1-kappa and compensation M q r<=1-kappa, L>=1, i : Fin M with i in S.val, and natural k,l, assume both L*(1+r)/(2*(k+1)) and L*(1-r)/(2*(l+1)) lie in [15/16,1]. For every j : Fin 4, rowReference S r L i at the j-th cell of [(k,l),(k+1,l),(k,l+1),(k+1,l+1)] lies between 7/8 and 9/8 times rowReference S r L i (k,l). Counts in the successor factors are cast to reals."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("floored-signal-four-reference-ratios"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.floored_signal_four_reference_ratios"),
                H("Floored signal four reference ratios"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original floor and its complementary count give the displayed four-cell reference-mass comparisons."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("background-reference-cell-ratio"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.background_reference_cell_ratio"),
                H("Background reference cell ratio"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At the same count cell, the background reference mass has its exact ratio to the signal reference mass."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-window"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.originalWindow"),
                H("Original window"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The selection window uses the original compensated score with its complete left-open and right-closed bounds."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("original-group-posterior-mean"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall.originalGroupPosteriorMean"),
                H("Original group posterior mean"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The group mean sums the complete support posterior over all rows in the same original score group."))),
                DescribeRole.Definition)
        )));
}

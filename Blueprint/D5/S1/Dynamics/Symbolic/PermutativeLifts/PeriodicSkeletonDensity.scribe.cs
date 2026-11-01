using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic.PermutativeLifts;

internal sealed class PeriodicSkeletonDensityDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/PermutativeLifts/PeriodicSkeletonDensity.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual periodic-skeleton density exhaustion.",
        H("Actual periodic-skeleton density exhaustion"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-phases"), DeclarationHandle.Create(Owner + "phases"),
                H("Actual periodic coordinate phases"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a two-sided binary point y and a positive natural period p, the finite set consists of exactly those residue classes j in Z/pZ for which y(j+kp)=y(j) for every signed integer k. The chosen representative is j.val in the complete interval from zero to p-1. This is the actual periodic coordinate condition; no finite sampling or word approximation substitutes for it."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("normalized-density"), DeclarationHandle.Create(Owner + "density"),
                H("Periodic-skeleton density"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The density is the real number of actual periodic residue classes divided by the positive period p. This is the source periodic-skeleton count on one complete period. It does not assert that p is an essential period, that the sequence supplied later is an essential period structure, or that the point is nonperiodic."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("density-upper-bound"), DeclarationHandle.Create(Owner + "density_le_one"),
                H("A density cannot exceed one"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Filtering the p-element residue space gives at most p periodic classes, so every actual periodic-skeleton density is at most one. This generic finite-count bound is consumed in the balanced limit proof."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("shared-columns"), DeclarationHandle.Create(Owner + "common_phases_subset_periodic_phases"),
                H("Shared columns are actual periodic phases"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fix the actual aligned compact-limit point and a balanced level n. The actual origin-aligned marked tiling identifies each residue j with its physical offset j. Outside the literal word-disagreement set both tile types read the same symbol at that offset; tiled_common_column_periodic therefore proves equality at j+k h(n) for all integers k. Thus the complement of the disagreement set is included in the actual periodic skeleton."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("integral-bound"), DeclarationHandle.Create(Owner + "aligned_periodic_phases_card_lower_bound"),
                H("An integral bound on actual skeleton holes"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The common-phase inclusion and the existing SparseDisagreement.wordDisagreements_card bridge imply h(n) is at most the number of actual periodic phases plus disagreementCount(n). The existing list mismatch recurrence is reused rather than reproved. Extra periodic phases are allowed; this theorem claims only a lower bound."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("geometric-bound"), DeclarationHandle.Create(Owner + "aligned_periodic_density_lower_bound"),
                H("An explicit geometric density bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual h(n)-periodic skeleton of the aligned point has density at least 1-(1/3)^n. Its proof divides the integral phase bound by the positive height and casts the previously proved exact rational word-disagreement fraction to the reals."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("density-limit"), DeclarationHandle.Create(Owner + "aligned_periodic_density_tendsto_one"),
                H("Actual periodic skeletons exhaust density one"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual skeleton densities along the balanced heights converge to one: 1-(1/3)^n is a lower bound, one is an upper bound and the geometric error converges to zero. This is a faithful intermediate periodic-skeleton result. It supplies no essential-period extraction theorem, and hence does not by itself complete the primary source period-structure definition of regular Toeplitzness."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-generator"), DeclarationHandle.Create(Owner + "exists_balanced_toeplitz_generator_with_density"),
                H("One generator has all proved properties"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("There is one binary point in the actual balanced subshift with periodic coordinates for all signed multiples, no positive global shift period, orbit closure exactly equal to that compact minimal subshift, and actual balanced-height periodic-skeleton densities converging to one. Every clause refers to the same actual aligned point. Essential-period structure, strict ergodicity and lift splitting are separate obligations. Public theorem escape registrations remain unfinished under https://github.com/the-omega-institute/trureturing/issues/24726; the mathematical build and scoped axiom report do not constitute declared_validated registration evidence."))), DescribeRole.Theorem)),
            [ DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMinimal")),
              DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Dynamics/Symbolic/PermutativeLifts/SparseDisagreement")) ]));
}

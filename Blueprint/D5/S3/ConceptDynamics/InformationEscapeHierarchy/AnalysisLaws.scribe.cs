using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscapeHierarchy;

internal sealed class AnalysisLawsDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscapeHierarchy/AnalysisLaws.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Shared-arena capture sets support certified overlap, refinement, multiplicity-spectrum, and role-histogram analysis.",
        H("Shared-Arena Analysis Laws"),
        Blocks(
            Definition("capture-pairs", "capturePairs", "Occurrence capture pairs",
                "The capture set removes the singleton-kernel escape set from all ordered off-diagonal state pairs."),
            Definition("exclusive-capture-vector", "exclusiveCaptureVector",
                "Exclusive capture vector",
                "Each catalog coordinate is its peer-relative unique-capture cardinality."),
            Definition("pairwise-capture-overlap-pairs", "pairwiseCaptureOverlapPairs",
                "Pairwise capture overlap",
                "An overlap cell is the intersection of two occurrence capture sets."),
            Definition("pairwise-capture-overlap-count", "pairwiseCaptureOverlapCount",
                "Pairwise overlap count", "The count is the exact cardinality of one overlap cell."),
            Definition("pairwise-capture-overlap-rate", "pairwiseCaptureOverlapRate",
                "Pairwise overlap rate", "The exact rational rate uses the common arena denominator."),
            Definition("role-signature-rate", "roleSignatureRate", "Role-signature rate",
                "The exact rational rate divides one role-signature count by the common arena denominator."),
            Definition("kernel-refines", "KernelRefines", "Occurrence kernel refinement",
                "The finer occurrence agreement relation is pointwise contained in the coarser relation."),
            Definition("kernel-equivalent", "KernelEquivalent", "Occurrence kernel equivalence",
                "Two occurrence kernels are equivalent when they refine one another."),
            Definition("kernel-comparison", "KernelComparison", "Kernel comparison cases",
                "The four cases distinguish equality, either strict direction, and incomparability."),
            Definition("classify-kernel-comparison", "kernelComparison",
                "Classified kernel comparison",
                "The two decidable inclusion cells determine the four-way kernel classification."),
            Definition("refinement-witness", "refinementWitness", "Refinement failure witness",
                "A deterministic finite search returns a state pair witnessing a false refinement cell."),
            Theorem("refinement-witness-none-iff-included", "refinementWitness_eq_none_iff",
                "No witness exactly means refinement", WitnessNone()),
            Theorem("refinement-witness-some-is-sound", "refinementWitness_eq_some_implies",
                "A returned refinement witness is sound", WitnessSome()),
            Theorem("refinement-witness-exists-iff-not-refines",
                "refinementWitness_exists_iff_not_kernelRefines",
                "A false cell has a deterministic witness", WitnessExistsIff()),
            Theorem("kernel-comparison-spec", "kernelComparison_spec",
                "Kernel comparison carries all inclusion and witness payloads", ComparisonSpec()),
            Definition("capture-multiplicity", "captureMultiplicity", "Capture multiplicity",
                "Multiplicity counts how many catalog occurrences capture one ordered state pair."),
            Definition("capture-spectrum", "captureSpectrum", "Capture-multiplicity spectrum",
                "Each bucket counts off-diagonal pairs having exactly its indexed multiplicity."),
            Definition("capture-multiplicity-one", "captureMultiplicityOne",
                "Multiplicity-one index", "A nonempty catalog has a genuine spectrum coordinate for multiplicity one."),
            Definition("ordered-distinct-overlap-total", "orderedDistinctOverlapTotal",
                "Ordered distinct overlap total",
                "The total sums all overlap counts over ordered distinct occurrence pairs."),
            Definition("capture-spectrum-second-factorial-moment",
                "captureSpectrumSecondFactorialMoment", "Second factorial spectrum moment",
                "The second factorial moment weights each bucket by k times k minus one."),
            Definition("role-histogram-total", "roleHistogramTotal", "Role column total",
                "A role-signature column is summed across the entire catalog."),
            Definition("role-profile-equality", "roleProfileEq", "Role profile equality",
                "Two occurrences have equal role profiles when every role-signature count agrees."),
            Definition("role-histogram-difference", "roleHistogramDifference",
                "Role histogram difference", "A signed column difference compares two catalog occurrences."),
            Theorem("role-histogram-difference-zero-iff-equal",
                "roleHistogramDifference_eq_zero_iff",
                "Zero role difference exactly means equal counts", DifferenceZero()),
            Theorem("role-profile-equality-iff-difference-zero",
                "roleProfileEq_iff_difference_zero",
                "Role profiles agree exactly when every difference vanishes", ProfileDifferenceZero()),
            Definition("redundant-indices", "redundantIndices", "Redundant occurrence indices",
                "The redundant-index set contains exactly occurrences with zero unique capture."),
            Definition("catalog-redundant", "CatalogRedundant", "Catalog redundancy",
                "A catalog is redundant when at least one occurrence has zero unique capture."),
            Theorem("unique-capture-as-set-difference",
                "uniqueCapturePairs_eq_capture_sdiff_iUnion",
                "Unique capture is capture minus peer capture", UniqueAsDifference()),
            Theorem("unique-capture-pairwise-disjoint",
                "uniqueCapturePairs_pairwise_disjoint",
                "Unique-capture sets are pairwise disjoint", UniqueDisjoint()),
            Theorem("sum-unique-capture-bounded-by-captured-count",
                "sum_uniqueCaptureCount_le_capturedCount",
                "Exclusive capture is bounded by full capture", UniqueBound()),
            Theorem("pairwise-capture-overlap-commutes", "pairwiseCaptureOverlap_comm",
                "Pairwise overlap is symmetric", OverlapComm()),
            Theorem("pairwise-capture-overlap-diagonal", "pairwiseCaptureOverlap_diag",
                "Diagonal overlap is capture", OverlapDiag()),
            Theorem("pairwise-capture-overlap-subset", "pairwiseCaptureOverlap_subset",
                "Overlap lies in both capture cells", OverlapSubset()),
            Theorem("pairwise-capture-overlap-count-bounds", "pairwiseCaptureOverlapCount_le",
                "Overlap count is bounded by both capture counts", OverlapCountBounds()),
            Theorem("kernel-refines-preorder", "kernelRefines_preorder",
                "Kernel refinement is a preorder", RefinesPreorder()),
            Theorem("kernel-refines-iff-capture-subset",
                "kernelRefines_iff_capturePairs_subset",
                "Refinement reverses capture inclusion", RefinesCapture()),
            Theorem("kernel-refines-implies-zero-unique-capture",
                "kernelRefines_implies_zero_uniqueCapture",
                "A distinct finer peer zeros coarser unique capture", RefinesZeroSet()),
            Theorem("kernel-refines-implies-zero-unique-capture-count",
                "kernelRefines_implies_zero_uniqueCaptureCount",
                "A distinct finer peer zeros coarser unique count", RefinesZeroCount()),
            Theorem("catalog-redundant-iff-exists-zero", "catalogRedundant_iff_exists_zero",
                "Redundancy is existence of a zero coordinate", RedundantExists()),
            Theorem("catalog-redundant-iff-not-irredundant",
                "catalogRedundant_iff_not_catalogIrredundant",
                "Redundancy negates catalog irredundancy", RedundantNegation()),
            Theorem("catalog-irredundant-iff-redundant-indices-empty",
                "catalogIrredundant_iff_redundantIndices_eq_empty",
                "Irredundancy empties the redundant-index set", IrredundantEmpty()),
            Theorem("catalog-redundant-iff-not-irredundant-spec-name",
                "catalogRedundant_iff_not_irredundant",
                "Spec-name redundancy equivalence", RedundantNegation()),
            Theorem("capture-spectrum-sum-is-denominator",
                "captureSpectrum_sum_eq_denominator",
                "Spectrum buckets partition the arena denominator", SpectrumTotal()),
            Theorem("capture-spectrum-zero-is-full-escape",
                "captureSpectrum_zero_eq_fullEscape",
                "Zero multiplicity is full escape", SpectrumZero()),
            Theorem("capture-spectrum-one-is-sum-unique",
                "captureSpectrum_one_eq_sum_unique",
                "Multiplicity one is total exclusive capture", SpectrumUnique()),
            Theorem("capture-spectrum-incidence-double-count",
                "captureSpectrum_incidence_double_count",
                "The first moment double-counts capture incidence", SpectrumFirst()),
            Theorem("pairwise-overlap-spectrum-double-count",
                "pairwiseOverlap_spectrum_doubleCount",
                "Overlap is the second factorial moment", SpectrumSecond()),
            Theorem("catalog-role-histogram-sum", "catalogRoleHistogram_sum",
                "Role columns sum to exclusive capture", RoleHistogramSum()),
            Theorem("spectrum-total", "spectrum_total",
                "Hierarchy spectrum total", SpectrumTotal()),
            Theorem("spectrum-zero", "spectrum_zero",
                "Hierarchy zero-multiplicity bucket", SpectrumZero()),
            Theorem("spectrum-unique", "spectrum_unique",
                "Hierarchy multiplicity-one bucket", SpectrumUnique()),
            Theorem("spectrum-first-moment", "spectrum_first_moment",
                "Hierarchy first spectrum moment", SpectrumFirst()),
            Theorem("spectrum-second-moment", "spectrum_second_moment",
                "Hierarchy second spectrum moment", SpectrumSecondReversed()),
            Theorem("overlap-symmetric-diagonal", "overlap_symmetric_diagonal",
                "Overlap symmetry and diagonal law", OverlapSymmetricDiagonal()),
            Theorem("refinement-overlap", "refinement_overlap",
                "Refinement determines overlap", RefinementOverlap()))));

    private static DocumentBlock.Describe Definition(
        string id, string declaration, string title, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))), DescribeRole.Definition);

    private static DocumentBlock.Describe Theorem(
        string id, string declaration, string title, Formula formula) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(Seq(formula, Dot))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The certificate follows from finite capture-set algebra and the landed escape and role-histogram laws."))),
            DescribeRole.Theorem);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Catalog() => F.Id("C");
    private static Formula Index() => F.Id("i");
    private static Formula OtherIndex() => F.Id("j");
    private static Formula Finer() => F.Id("i");
    private static Formula Coarser() => F.Id("j");
    private static Formula Pair() => F.Id("p");
    private static Formula Multiplicity() => F.Id("k");
    private static Formula Signature() => F.Id("s");
    private static Formula Capture(Formula index) => Call("capturePairs", Catalog(), index);
    private static Formula Unique(Formula index) => Call("uniqueCapturePairs", Catalog(), index);
    private static Formula UniqueCount(Formula index) => Call("uniqueCaptureCount", Catalog(), index);
    private static Formula Overlap(Formula left, Formula right) =>
        Call("pairwiseCaptureOverlapPairs", Catalog(), left, right);
    private static Formula Refines(Formula finer, Formula coarser) =>
        Call("KernelRefines", Catalog(), finer, coarser);
    private static Formula Witness(Formula finer, Formula coarser) =>
        Call("refinementWitness", Catalog(), finer, coarser);
    private static Formula WitnessExists(Formula finer, Formula coarser) => Seq(
        Exists, Sp, Pair(), Comma, Sp, Witness(finer, coarser), Sp, Eq, Sp,
        Call("some", Pair()));
    private static Formula Comparison(Formula value) => Seq(
        Call("kernelComparison", Catalog(), Index(), OtherIndex()), Sp, Eq, Sp, value);
    private static Formula Histogram(Formula index, Formula signature) =>
        Call("roleHistogram", Catalog(), index, signature);
    private static Formula Difference() =>
        Call("roleHistogramDifference", Catalog(), Index(), OtherIndex(), Signature());
    private static Formula Spectrum(Formula multiplicity) =>
        Call("captureSpectrum", Catalog(), multiplicity);
    private static Formula Sum(Formula term) => Call("sum", term);
    private static Formula Card(Formula set) => Call("card", set);
    private static Formula FullEscape() =>
        Call("escapePairs", Catalog(), Call("fullIndexSet", Catalog()));

    private static Formula UniqueAsDifference() => Seq(
        Unique(Index()), Sp, Eq, Sp,
        Call("sdiff", Capture(Index()),
            Call("biUnion", Call("erase", Call("univ"), Index()), Capture(OtherIndex()))));

    private static Formula UniqueDisjoint() => Implies(
        Seq(Index(), Sp, Neq, Sp, OtherIndex()),
        Call("Disjoint", Unique(Index()), Unique(OtherIndex())));

    private static Formula UniqueBound() => new Formula.Relation(
        Sum(UniqueCount(Index())), FormulaRelationOperator.LessThanOrEqual,
        Card(Call("sdiff", Call("offDiagonalPairs", Catalog()), FullEscape())));

    private static Formula OverlapComm() => Seq(
        Overlap(Index(), OtherIndex()), Sp, Eq, Sp, Overlap(OtherIndex(), Index()));

    private static Formula OverlapDiag() => Seq(
        Overlap(Index(), Index()), Sp, Eq, Sp, Capture(Index()));

    private static Formula OverlapSubset() => And(
        Seq(Overlap(Index(), OtherIndex()), Sp, Subseteq, Sp, Capture(Index())),
        Seq(Overlap(Index(), OtherIndex()), Sp, Subseteq, Sp, Capture(OtherIndex())));

    private static Formula OverlapCountBounds() => And(
        Seq(Call("pairwiseCaptureOverlapCount", Catalog(), Index(), OtherIndex()),
            Sp, Leq, Sp, Card(Capture(Index()))),
        Seq(Call("pairwiseCaptureOverlapCount", Catalog(), Index(), OtherIndex()),
            Sp, Leq, Sp, Card(Capture(OtherIndex()))));

    private static Formula RefinesPreorder() => And(
        Call("Reflexive", Call("KernelRefines", Catalog())),
        Call("Transitive", Call("KernelRefines", Catalog())));

    private static Formula RefinesCapture() => Seq(
        Refines(Finer(), Coarser()), Sp, Leftrightarrow, Sp,
        Capture(Coarser()), Sp, Subseteq, Sp, Capture(Finer()));

    private static Formula RefinementPremises() => And(
        Seq(Finer(), Sp, Neq, Sp, Coarser()), Refines(Finer(), Coarser()));

    private static Formula WitnessNone() => Seq(
        Witness(Finer(), Coarser()), Sp, Eq, Sp, Call("none"),
        Sp, Leftrightarrow, Sp, Refines(Finer(), Coarser()));

    private static Formula WitnessSome()
    {
        Formula fineAgrees = Call("agrees", Catalog(), Finer(),
            Call("fst", Pair()), Call("snd", Pair()));
        Formula coarseAgrees = Call("agrees", Catalog(), Coarser(),
            Call("fst", Pair()), Call("snd", Pair()));
        return Implies(
            Seq(Witness(Finer(), Coarser()), Sp, Eq, Sp, Call("some", Pair())),
            And(fineAgrees, Seq(Neg, coarseAgrees)));
    }

    private static Formula WitnessExistsIff() => Seq(
        WitnessExists(Finer(), Coarser()), Sp, Leftrightarrow, Sp,
        Neg, Refines(Finer(), Coarser()));

    private static Formula ComparisonSpec()
    {
        Formula equal = Seq(Comparison(F.Id("equal")), Sp, Leftrightarrow, Sp,
            And(Refines(Index(), OtherIndex()), Refines(OtherIndex(), Index())));
        Formula finer = Seq(Comparison(F.Id("strictlyFiner")), Sp, Leftrightarrow, Sp,
            And(Refines(Index(), OtherIndex()), WitnessExists(OtherIndex(), Index())));
        Formula coarser = Seq(Comparison(F.Id("strictlyCoarser")), Sp, Leftrightarrow, Sp,
            And(WitnessExists(Index(), OtherIndex()), Refines(OtherIndex(), Index())));
        Formula incomparable = Seq(Comparison(F.Id("incomparable")), Sp, Leftrightarrow, Sp,
            And(WitnessExists(Index(), OtherIndex()), WitnessExists(OtherIndex(), Index())));
        return And(equal, And(finer, And(coarser, incomparable)));
    }

    private static Formula RefinesZeroSet() => Implies(
        RefinementPremises(), Seq(Unique(Coarser()), Sp, Eq, Sp, Emptyset));

    private static Formula RefinesZeroCount() => Implies(
        RefinementPremises(), Seq(UniqueCount(Coarser()), Sp, Eq, Sp, D(0)));

    private static Formula RedundantExists() => Seq(
        Call("CatalogRedundant", Catalog()), Sp, Leftrightarrow, Sp,
        Exists, Sp, Index(), Comma, Sp, UniqueCount(Index()), Sp, Eq, Sp, D(0));

    private static Formula RedundantNegation() => Seq(
        Call("CatalogRedundant", Catalog()), Sp, Leftrightarrow, Sp,
        Neg, Call("CatalogIrredundant", Catalog()));

    private static Formula IrredundantEmpty() => Seq(
        Call("CatalogIrredundant", Catalog()), Sp, Leftrightarrow, Sp,
        Call("redundantIndices", Catalog()), Sp, Eq, Sp, Emptyset);

    private static Formula DifferenceZero() => Seq(
        Difference(), Sp, Eq, Sp, D(0), Sp, Leftrightarrow, Sp,
        Histogram(Index(), Signature()), Sp, Eq, Sp, Histogram(OtherIndex(), Signature()));

    private static Formula ProfileDifferenceZero() => Seq(
        Call("roleProfileEq", Catalog(), Index(), OtherIndex()), Sp, Leftrightarrow, Sp,
        Forall, Sp, Signature(), Comma, Sp, Difference(), Sp, Eq, Sp, D(0));

    private static Formula SpectrumTotal() => Seq(
        Sum(Spectrum(Multiplicity())), Sp, Eq, Sp,
        Card(Call("offDiagonalPairs", Catalog())));

    private static Formula SpectrumZero() => Seq(
        Spectrum(D(0)), Sp, Eq, Sp, Card(FullEscape()));

    private static Formula SpectrumUnique() => Seq(
        Spectrum(Call("captureMultiplicityOne", Catalog())), Sp, Eq, Sp,
        Sum(UniqueCount(Index())));

    private static Formula SpectrumFirst() => Seq(
        Sum(Seq(Multiplicity(), Sp, Times, Sp, Spectrum(Multiplicity()))),
        Sp, Eq, Sp, Sum(Card(Capture(Index()))));

    private static Formula SpectrumSecond() => Seq(
        Call("orderedDistinctOverlapTotal", Catalog()), Sp, Eq, Sp,
        Call("captureSpectrumSecondFactorialMoment", Catalog()));

    private static Formula SpectrumSecondReversed() => Seq(
        Call("captureSpectrumSecondFactorialMoment", Catalog()), Sp, Eq, Sp,
        Call("orderedDistinctOverlapTotal", Catalog()));

    private static Formula RoleHistogramSum()
    {
        Formula roleTotal = Call("sumNonzeroSignatures",
            Call("roleHistogramTotal", Catalog(), Signature()));
        Formula uniqueTotal = Sum(UniqueCount(Index()));
        Formula firstBucket = Spectrum(Call("captureMultiplicityOne", Catalog()));
        return And(Seq(roleTotal, Sp, Eq, Sp, uniqueTotal),
            Seq(uniqueTotal, Sp, Eq, Sp, firstBucket));
    }

    private static Formula OverlapSymmetricDiagonal() => And(
        Seq(Overlap(Index(), OtherIndex()), Sp, Eq, Sp,
            Overlap(OtherIndex(), Index())),
        Seq(Overlap(Index(), Index()), Sp, Eq, Sp, Capture(Index())));

    private static Formula RefinementOverlap() => Implies(
        Refines(Finer(), Coarser()),
        And(Seq(Capture(Coarser()), Sp, Subseteq, Sp, Capture(Finer())),
            Seq(Overlap(Finer(), Coarser()), Sp, Eq, Sp, Capture(Coarser()))));
}

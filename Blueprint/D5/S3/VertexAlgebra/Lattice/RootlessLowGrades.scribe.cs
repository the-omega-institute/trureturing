// Apache-2.0.
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class RootlessLowGradesDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Constructive low-energy bijections on the actual rootless lattice carrier.",
        H("Rootless Lattice Low Grades and Canonical Sugawara Spectrum"),
        Blocks(
            Paragraph(Text("D is ordinary even integral LatticeData of any natural rank, including zero. "
                + "Only real positive definiteness of the Gram matrix and absence of norm-two integral charges "
                + "are required for the spectral conclusion. No unimodularity, dimension premise, fixed shell count "
                + "or finite classification is used.")),
            Paragraph(Text("The new mathematical content is the exhaustive constructive oscillator and all-charge "
                + "energy-two classification and its injective/surjective occupation maps. Auxiliary rewrites, "
                + "stars-and-bars cardinality and basis/eigenspace transport are consumed on the live derivation "
                + "of the general spectral theorem. The resulting bijections give a symbolic construction for "
                + "every natural rank, including rank zero.")),
            Paragraph(Text("The proof reuses chargeSublevel_finite, gradeBasis, grade_finiteDimensional, "
                + "complex_inverse_exists and actualL0_eigenspace_eq_grade. Both inverse equations identify "
                + "the literal canonical Sugawara L0 eigenspaces with the existing grades on the same carrier. "
                + "Finite dimensionality includes every signed integer grade. Rank 24 specializes the neutral "
                + "term to 324; the charged contribution remains Nat.card of the actual norm-four shell. "
                + "No Leech count or Monster/moonshine identification follows from this slice.")),
            Describe.Lean(
                DescribeId.Create("latticerootlesslowgrades-oscillatorfiber"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/RootlessLowGrades.OscillatorFiber"),
                H("Exact oscillator energy fibre"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Exponent vectors with oscillatorEnergy exactly n."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticerootlesslowgrades-normfour"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/RootlessLowGrades.NormFour"),
                H("Actual integral norm-four shell"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The subtype of actual charges a with bilinear(D,a,a)=4; no finite classification or cardinality is assumed."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticerootlesslowgrades-oscillator-one-iff"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/RootlessLowGrades.oscillator_one_iff"),
                H("Exhaustive energy-one oscillator classification"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Removing one occupied occurrence proves that energy one is exactly one mode-one colour, including rank zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticerootlesslowgrades-oscillatoroneequiv"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/RootlessLowGrades.oscillatorOneEquiv"),
                H("Energy-one oscillator bijection"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The proved classification yields a bijection of the actual energy-one exponent fibre with Fin(rank)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticerootlesslowgrades-oscillator-two-classification"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/RootlessLowGrades.oscillator_two_classification"),
                H("Exhaustive energy-two oscillator classification"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Removing an occupied occurrence leaves weight zero or one. Every energy-two exponent is a mode-two singleton or the sum of two mode-one singletons."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticerootlesslowgrades-pairoccupation"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/RootlessLowGrades.pairOccupation"),
                H("Unordered pair occupation vector"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("A literal two-multiset of colours is mapped to its natural-valued finite-support occupation vector. Repeated colours are included."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticerootlesslowgrades-oscillatortwodecode"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/RootlessLowGrades.oscillatorTwoDecode"),
                H("Constructed energy-two oscillator labels"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The two summands construct actual exponent vectors: a mode-two singleton or an unordered pair of mode-one colours."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticerootlesslowgrades-oscillatortwoequiv"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/RootlessLowGrades.oscillatorTwoEquiv"),
                H("Constructive oscillator energy-two equivalence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The decoder is injective and surjective, giving OscillatorFiber(D,2) equivalent to Fin(rank) + Sym(Fin(rank),2)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticerootlesslowgrades-neutral-energy-two-card"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/RootlessLowGrades.neutral_energy_two_card"),
                H("General neutral oscillator cardinality"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The constructive equivalence and Mathlib stars-and-bars give rank + choose(rank+1,2)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticerootlesslowgrades-chargeenergy-gap"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/RootlessLowGrades.chargeEnergy_gap"),
                H("Rootless nonzero charge energy gap"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Positivity and evenness give nonnegative integral half-norm; zero characterizes the zero charge and rootlessness excludes energy one. Every nonzero charge costs at least two."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticerootlesslowgrades-normfour-finite"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/RootlessLowGrades.normFour_finite"),
                H("Derived finiteness of the actual norm-four shell"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The actual shell embeds in the existing charge-energy sublevel at two, whose finiteness follows from positive definiteness."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticerootlesslowgrades-energy-one-iff"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/RootlessLowGrades.energy_one_iff"),
                H("All-charge energy-one exclusion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Total energy one forces zero charge and oscillator energy one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticerootlesslowgrades-energy-two-iff"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/RootlessLowGrades.energy_two_iff"),
                H("All-charge energy-two classification"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Total energy two is exactly a neutral weight-two oscillator or a norm-four charge with zero oscillator exponent."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticerootlesslowgrades-energyzeroequiv"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/RootlessLowGrades.energyZeroEquiv"),
                H("Vacuum energy label"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The exact energy-zero label fibre is equivalent to Unit by the existing positive energy-zero characterization."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticerootlesslowgrades-energyoneequiv"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/RootlessLowGrades.energyOneEquiv"),
                H("Actual energy-one label bijection"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The all-charge energy-one label fibre is equivalent to Fin(rank), via proved charge exclusion."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticerootlesslowgrades-energytwodecode"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/RootlessLowGrades.energyTwoDecode"),
                H("All-charge energy-two label construction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Neutral oscillator labels and norm-four charged ground states construct actual energy-two labels."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticerootlesslowgrades-energytwoequiv"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/RootlessLowGrades.energyTwoEquiv"),
                H("All-charge energy-two sum decomposition"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The decoder bijection identifies the actual energy-two fibre with OscillatorFiber(D,2) + NormFour(D)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticerootlesslowgrades-energytwoconfigurations"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/RootlessLowGrades.energyTwoConfigurations"),
                H("Complete energy-two configurations"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The actual label fibre is equivalent to (Fin(rank) + Sym(Fin(rank),2)) + NormFour(D), without duplication."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticerootlesslowgrades-gradetwobasis"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/RootlessLowGrades.gradeTwoBasis"),
                H("Reindexed existing actual-carrier basis"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Reindex LatticeEnergyGrading.gradeBasis by the proved complete energy-two configurations; the carrier remains the actual lattice Fock carrier."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticerootlesslowgrades-grade-two-finrank"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/RootlessLowGrades.grade_two_finrank"),
                H("Actual-carrier grade-two dimension"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The derived finite shell and reindexed basis yield rank + choose(rank+1,2) + Nat.card(NormFour(D))."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticerootlesslowgrades-actual-rootless-low-spectrum"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/RootlessLowGrades.actual_rootless_low_spectrum"),
                H("Canonical inverse-Gram Sugawara low spectrum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every signed integer n the literal sugawaraMode(D,gramComplex(D) inverse,0) eigenspace at n is finite dimensional. Its dimensions at zero, one and two are 1, rank, and rank + choose(rank+1,2) + Nat.card(NormFour(D))."))),
                DescribeRole.Theorem))));
}

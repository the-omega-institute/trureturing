using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography.MUB;

internal sealed class MUBHadamardCompatibilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact Hadamard atlases retain relative gauges when testing four-MUB compatibility.",
        H("MUB Hadamard Compatibility"),
        Blocks(
            Describe.Lean(
                DescribeId.Create(
                    "mub-compat-complex-square"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility."
                    + "ComplexSquare"),
                H("Complex square matrices"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A square matrix over the complex numbers on a coordinate type n."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create(
                    "mub-compat-entrywise-unit"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility."
                    + "EntrywiseUnit"),
                H("Unit squared entry norms"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every entry of a rectangular complex matrix has squared norm one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create(
                    "mub-compat-is-complex-hadamard"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility."
                    + "IsComplexHadamard"),
                H("Unnormalized complex Hadamard matrices"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On a finite coordinate type with decidable equality, every entry "
                    + "has squared norm one and H times its adjoint equals the cardinality "
                    + "times the identity."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create(
                    "mub-compat-hadamard-equivalent"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility."
                    + "HadamardEquivalent"),
                H("Row and column monomial equivalence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Two complex square matrices are related by row and column "
                    + "permutations and multiplication by row and column phases of squared "
                    + "norm one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create(
                    "mub-compat-hadamard-equivalent-refl"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility."
                    + "hadamardEquivalent_refl"),
                H("Reflexivity of Hadamard equivalence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every complex square matrix is Hadamard equivalent to itself."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "mub-compat-hadamard-equivalent-trans"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility."
                    + "hadamardEquivalent_trans"),
                H("Transitivity of Hadamard equivalence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Equivalence of H to K and of K to L implies equivalence of H to L."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "mub-compat-hadamard-equivalent-symm"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility."
                    + "hadamardEquivalent_symm"),
                H("Symmetry of Hadamard equivalence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If H is Hadamard equivalent to K, then K is Hadamard equivalent to "
                    + "H."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "mub-compat-hadamard-unbiased"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility."
                    + "HadamardUnbiased"),
                H("Flat transitions between matrices"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every entry of the adjoint of H times K has squared norm equal to "
                    + "the finite coordinate cardinality."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create(
                    "mub-compat-hadamard-unbiased-symm"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility."
                    + "hadamardUnbiased_symm"),
                H("Symmetry of flat transitions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If H and K have a flat transition in this sense, then K and H do as "
                    + "well."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "mub-compat-i6"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility."
                    + "I6"),
                H("Six-coordinate carrier"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The coordinate type is the disjoint sum of two copies of Fin 3."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create(
                    "mub-compat-mat6"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility."
                    + "Mat6"),
                H("Order-six complex matrices"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A complex square matrix on the six-coordinate carrier I6."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create(
                    "mub-compat-four-mubhadamard-witness"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility."
                    + "FourMUBHadamardWitness"),
                H("Three pairwise unbiased Hadamard matrices"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A witness supplies three order-six complex Hadamard matrices, with "
                    + "a flat transition for every distinct pair."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create(
                    "mub-compat-is-exact-hadamard-atlas"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility."
                    + "IsExactHadamardAtlas"),
                H("Exact atlas contract"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every order-six matrix H, H is complex Hadamard exactly when "
                    + "some atlas entry is Hadamard equivalent to H."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create(
                    "mub-compat-has-lifted-four-mubwitness"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility."
                    + "HasLiftedFourMUBWitness"),
                H("Compatibility of lifted atlas entries"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Three matrices each have a Hadamard-equivalent representative in "
                    + "the atlas and have flat transitions for every distinct pair. "
                    + "Compatibility is tested on the lifted matrices."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create(
                    "mub-compat-nonempty-four-mubhadamard-witness-iff-lifted-atlas"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility."
                    + "nonempty_fourMUBHadamardWitness_iff_lifted_atlas"),
                H("Exact atlas reduction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For an exact atlas, a FourMUBHadamardWitness exists if and only if "
                    + "a lifted four-MUB witness exists over that atlas."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "mub-compat-no-four-mubhadamard-witness-of-no-lifted-atlas"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility."
                    + "no_fourMUBHadamardWitness_of_no_lifted_atlas"),
                H("Exclusion through an exact atlas"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If an exact atlas has no lifted four-MUB witness, then no "
                    + "FourMUBHadamardWitness exists."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "mub-compat-independent-hadamard-equivalence-does-not-preserve-unbiasedness"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility."
                    + "independent_hadamard_equivalence_does_not_preserve_unbiasedness"),
                H("Independent equivalence can change compatibility"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "There exist order-two complex Hadamard matrices H, K and L such "
                    + "that K and L are Hadamard equivalent, H and L are unbiased, and H "
                    + "and K are not unbiased. The witnesses are the order-two Fourier "
                    + "matrix and its row-phased partner."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "mub-compat-is-four-mubcontext-family"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility."
                    + "IsFourMUBContextFamily"),
                H("Four mutually unbiased projector contexts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Four rank-one contexts in dimension six have projector overlap "
                    + "one-sixth for every pair of outcomes from distinct contexts."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create(
                    "mub-compat-four-mubcontexts-have-maximal-incompatibility"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility."
                    + "fourMUBContexts_have_maximal_incompatibility"),
                H("Maximal context incompatibility"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every distinct pair in a four-MUB context family has normalized "
                    + "incompatibility equal to one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "mub-compat-four-mubcontexts-have-pairwise-orthogonal-planes"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility."
                    + "fourMUBContexts_have_pairwise_orthogonal_planes"),
                H("Orthogonal centered context planes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If every context in a four-MUB family is a record measurement, then "
                    + "distinct contexts have orthogonal centered projector planes."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "mub-compat-four-mubcontexts-have-commutator-sum-ten"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility."
                    + "fourMUBContexts_have_commutator_sum_ten"),
                H("Aggregate commutator square"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For distinct contexts in a dimension-six four-MUB family, the sum "
                    + "over all pairs of outcomes of the Hilbert-Schmidt square of their "
                    + "projector commutator equals ten."))),
                DescribeRole.Theorem))));
}

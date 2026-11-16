using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.Bloch;

internal sealed class AxisContractionCommutatorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/Bloch/AxisContractionCommutator.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Parameterized commutators of qubit Bloch axis contractions.",
        H("Bloch axis contraction commutator"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("bloch-axis-contraction"),
                DeclarationHandle.Create(Prefix + "axisContraction"),
                H("Bloch axis contraction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a real three-coordinate axis n and real factor c, axisContraction n c is the matrix c I + (1 - c) n nᵀ, with entries expanded over Fin 3."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("bloch-axis-dot"),
                DeclarationHandle.Create(Prefix + "axisDot"),
                H("Bloch axis dot product"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The finite coordinate dot product of two real Bloch vectors n and m is the sum over Fin 3 of n k times m k."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("bloch-axis-outer"),
                DeclarationHandle.Create(Prefix + "axisOuter"),
                H("Bloch axis outer product"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The outer product axisOuter n m is the matrix with entry (i,j) equal to n i times m j."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("bloch-axis-outer-symmetry"),
                DeclarationHandle.Create(Prefix + "axisOuter_eq_implies_parallel"),
                H("Symmetric nonzero outer products force parallel axes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If the first three-coordinate vector is nonzero and its outer product with a second vector is symmetric under swapping the two vectors, then the second vector is a real scalar multiple of the first."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bloch-axis-contraction-commutator"),
                DeclarationHandle.Create(Prefix + "axisContraction_commutator"),
                H("Bloch axis contraction commutator factorization"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For arbitrary real three-coordinate axes n and m and real factors c and d, the commutator of axisContraction n c and axisContraction m d equals the scalar (1 - c)(1 - d)(n · m) times the antisymmetric outer-product difference n mᵀ - m nᵀ."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bloch-axis-contraction-noncommutation"),
                DeclarationHandle.Create(Prefix + "axisContraction_commutator_ne_zero_of_nonparallel_nonorthogonal"),
                H("Nonparallel nonorthogonal axes do not commute"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a nonzero first axis, a second axis that is not a scalar multiple of it, a nonzero dot product, and factors different from one, the two Bloch contractions have a nonzero commutator."))),
                DescribeRole.Theorem))));
}

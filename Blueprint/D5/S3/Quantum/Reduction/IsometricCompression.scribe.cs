using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Reduction;

internal sealed class IsometricCompressionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact rectangular-matrix compression, positive leakage, and finite operator-word transport. Analytic norm estimates are outside these declarations.",
        H("IsometricCompression"),
        Blocks(new[]
        {
                "multiplication_defect",
                "normal_gram",
                "hermitian_multiplication_defect",
                "commutator_defect",
                "compressed_gram_add_leakage",
                "instrument_mass_balance",
                "sum_gram_eq_zero_iff",
                "compressed_instrument_iff",
                "zero_leakage_iff_intertwines",
                "word_intertwines",
                "branch_intertwines"
        }.Select(name => Describe.Lean(
            DescribeId.Create(name.Replace('_', '-')),
            DeclarationHandle.Create("D5/S3/Quantum/Reduction/IsometricCompression." + name),
            H(name.Replace('_', ' ')),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Exact rectangular-matrix compression, positive leakage, and finite operator-word transport. Analytic norm estimates are outside these declarations."))),
            DescribeRole.Theorem)).ToArray())));
}

using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Transport;

internal sealed class MatrixUnitGeneratorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The computed averaged derivative generates every moving logical matrix unit. A real differentiable-path adapter derives the tangent hypotheses. Dyson convergence, global ODE existence, and physical implementability are not assumed or certified by these declarations.",
        H("MatrixUnitGenerator"),
        Blocks(new[]
        {
            "matrix_unit_transport_generator",
            "generator_from_real_path"
        }.Select(name => Describe.Lean(
            DescribeId.Create(name.Replace('_', '-')),
            DeclarationHandle.Create("D5/S3/Quantum/Transport/MatrixUnitGenerator." + name),
            H(name.Replace('_', ' ')),
            StatementSource.FromLean(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/kato1950adiabatic")),
            Blocks(Paragraph(Text("The computed averaged derivative generates every moving logical matrix unit. A real differentiable-path adapter derives the tangent hypotheses. Dyson convergence, global ODE existence, and physical implementability are not assumed or certified by these declarations."))),
            DescribeRole.Theorem)).ToArray())));
}

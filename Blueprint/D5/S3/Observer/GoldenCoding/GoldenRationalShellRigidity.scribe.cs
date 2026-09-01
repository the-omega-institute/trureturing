using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenCoding;

internal sealed class GoldenRationalShellRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonzero rational scale cannot traverse a nontrivial positive golden shell and remain rational.",
        H("Golden Rational Shell Rigidity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rational-shell-collision-rigidity"),
                DeclarationHandle.Create("D5/S3/Observer/GoldenCoding/GoldenRationalShellRigidity.rational_shell_collision_rigidity"),
                H("Rational golden-shell collisions are trivial"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "If two nonzero rational scales differ by a natural power of the orientation-preserving golden unit, then the shell depth is zero and the scales are equal.")),
                    Paragraph(Text(
                        "The proof reduces positive powers of the golden unit to a nonzero rational coefficient of the irrational golden ratio. It gives exact rigidity without a quantitative near-collision bound."))),
                DescribeRole.Theorem))));
}

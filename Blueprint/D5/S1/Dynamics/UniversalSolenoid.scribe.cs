using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics;

internal sealed class UniversalSolenoidDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S1/Dynamics/UniversalSolenoid",
                "The universal one-dimensional solenoid carries its visible projection and dense real flow."),
            H("Universal One-Dimensional Solenoid"),
            Blocks(
                Paragraph(Text(
                    "The carrier is the compatible family of circle phases indexed by positive "
                    + "integers under divisibility. Coordinate one defines a continuous, "
                    + "surjective additive projection to the visible circle.")),
                Paragraph(Text(
                    "A real parameter maps to the family represented in coordinate m by t/m. "
                    + "This is a continuous additive flow, its visible projection is t modulo "
                    + "one, and its image is dense. The density proof exactly matches every "
                    + "finite coordinate window by passing through a common multiple.")),
                new DocumentBlock.Describe(
                    DescribeId.Create("universal-solenoid-projection-flow"),
                    DescribeKind.Theorem,
                    H("The real flow projects visibly and has dense range"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Dynamics/UniversalSolenoid.projection_realFlow")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "The projection formula is machine-checked directly. The same module "
                        + "proves dense range and derives connectedness from it."))),
                    LatexStatement.Create(
                        @"$$\pi(\operatorname{realFlow}(t))=t\pmod 1.$$")))));
}

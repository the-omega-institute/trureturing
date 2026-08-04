using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

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
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("universal-solenoid-projection-flow"),
                    H("The real flow projects visibly and has dense range"),
                    LeanTheorem(
                        "D5/S1/Dynamics/UniversalSolenoid.projection_realFlow"),
                    Disp(Seq(Pi, Open, Operatorname, Grp(F.Id("realFlow")), Open, F.Id("t"), Close, Close, Eq, F.Id("t"), Operatorname, Grp(F.Id("mod")), D(1), Dot)),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "The projection formula is machine-checked directly. The same module "
                        + "proves dense range and derives connectedness from it.")))
                ))));
}

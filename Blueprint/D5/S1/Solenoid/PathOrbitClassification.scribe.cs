using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Solenoid;

internal sealed class PathOrbitClassificationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Path-connected universal-solenoid points are exactly points on one real-flow orbit.",
        H("Solenoid Path-Orbit Classification"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("path-connected-points-are-exactly-one-real-flow-orbit"),
                DeclarationHandle.Create(
                    "D5/S1/Solenoid/PathOrbitClassification."
                        + "path_joined_iff_real_flow_orbit"),
                H("Path-connected points are exactly one real-flow orbit"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Sp,
                    InMacro, Sp, Mathcal, Grp(F.Id("S")), Comma, Esc,
                    Operatorname, Grp(F.Id("Joined")), Open, F.Id("x"), Comma, Sp,
                    F.Id("y"), Close, Sp, Iff, Sp,
                    Exists, Sp, F.Id("t"), Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("R")), Comma, Esc,
                    F.Id("y"), Sp, Eq, Sp,
                    F.Id("realFlow"), Open, F.Id("t"), Close,
                    Sp, Plus, Sp, F.Id("x"), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Two universal-solenoid points are joined by a continuous path exactly "
                            + "when the second is the sum of the first and a real-flow element. "
                            + "For the forward implication, extend the unit-interval path "
                            + "continuously to the real line and apply the existing unique "
                            + "streamline decomposition; subtracting its endpoint lift values "
                            + "gives the required flow parameter. The reverse implication uses "
                            + "the explicit real-flow segment.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies Path, Joined, and the canonical continuous "
                            + "interval extension. No library theorem classifies path components "
                            + "of the universal solenoid, so the forward direction reuses the "
                            + "repository's established streamline decomposition.")),
                    Paragraph(Text(
                        "This is a partial closure of the source corollary's path-orbit clause. "
                            + "The quotient parametrization, uncountability, classification of "
                            + "hidden jumps, transverse two-leaf structure, and cocycle law remain "
                            + "outside this deposit."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S1/Solenoid/StreamlineDecomposition")),
        ]));
}

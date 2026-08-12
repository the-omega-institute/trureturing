using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds;

internal sealed class CollisionEntropyUncertaintyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Collision conservation across a complete finite measurement family gives a summed entropy uncertainty bound.",
        H("Collision-Entropy Uncertainty"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("collision-conservation-implies-the-summed-entropy-bound"),
                DeclarationHandle.Create(
                    "D5/S3/QuantumBounds/CollisionEntropyUncertainty.collision_entropy_uncertainty"),
                H("Collision conservation implies the summed entropy bound"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, F.Id("d"), Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("N")), Comma, Sp,
                    D(0), Lt, F.Id("d"), Comma, RowBreak,
                    Forall, Sp, F.Id("p"), Colon, Sp,
                    Operatorname, Grp(F.Id("Fin")), Open,
                    F.Id("d"), Plus, D(1), Close, To,
                    Operatorname, Grp(F.Id("Fin")), Open, F.Id("d"), Close,
                    To, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Forall, Sp, F.Id("purity"), Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Open,
                    Forall, Sp, F.Id("b"), Comma, Sp,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Le, Sp, F.Id("p"), Open, F.Id("b"), Comma, F.Id("i"), Close,
                    Close, Sp, Land, Sp,
                    Sum, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("p"), Open, F.Id("b"), Comma, F.Id("i"), Close,
                    Eq, D(1), Close, Comma, RowBreak,
                    Sum, Underscore, Grp(F.Id("b")), Sp,
                    Sum, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("p"), Open, F.Id("b"), Comma, F.Id("i"), Close,
                    Caret, Grp(D(2)), Eq, D(1), Plus, F.Id("purity"),
                    Sp, Rightarrow, RowBreak,
                    Open, F.Id("d"), Plus, D(1), Close, Cdot, Sp,
                    Log, Open,
                    Frac, Grp(F.Id("d"), Plus, D(1)),
                    Grp(D(1), Plus, F.Id("purity")), Close,
                    Sp, Le, Sp,
                    Sum, Underscore, Grp(F.Id("b")), Sp,
                    Operatorname, Grp(F.Id("shannonEntropy")), Open,
                    F.Id("p"), Open, F.Id("b"), Close, Close, Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let d be positive. For d+1 finite measurement laws on d outcomes, "
                        + "assume every law is nonnegative and normalized and that the sum of "
                        + "their squared-probability collision values is one plus the supplied "
                        + "state purity. The conclusion bounds their summed Shannon entropy "
                        + "below by (d+1) times the natural logarithm of (d+1)/(1+purity).")),
                    Paragraph(Text(
                        "The first finite Jensen application uses each measurement law as its "
                        + "own weights and proves that its Shannon entropy is at least minus "
                        + "the logarithm of its collision value. Zero-probability outcomes have "
                        + "zero weight, so they are assigned the harmless positive logarithm "
                        + "argument one inside that calculation.")),
                    Paragraph(Text(
                        "A second finite Jensen application uses uniform weights over the d+1 "
                        + "measurements. Collision conservation then replaces their average by "
                        + "(1+purity)/(d+1), giving the displayed bound. The module reuses the "
                        + "repository finite Shannon entropy and mathlib's weighted Jensen "
                        + "theorem; it assumes no unrecorded spectral or numerical certificate."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Entropy/MaxEntropy"))]));
}

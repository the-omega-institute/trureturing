using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Deficit;

internal sealed class PullbackReflectionCoordinateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Deficit/PullbackReflectionCoordinate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden-square scaling conjugates the pulled-back affine reflection to the classical "
            + "reflection, with an invariant structural line and a single pointwise fixed point.",
        H("Pullback Reflection Coordinate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("qc-reflection"),
                DeclarationHandle.Create(Prefix + "qcReflection"),
                H("Pulled-back reflection"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("J"), Underscore, Grp(F.Id("qc")), Open, F.Id("s"), Close,
                    Eq, Frac, Grp(D(1)), Grp(Varphi, Caret, Grp(D(2))),
                    Minus, F.Id("s")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This is the affine reflection obtained by pulling z maps to one minus z "
                        + "back through multiplication by phi squared."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("pullback-reflection-coordinate"),
                DeclarationHandle.Create(Prefix + "pullback_reflection_coordinate"),
                H("Conjugacy, invariant line, and fixed point"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every complex s, golden-square scaling carries the pulled-back "
                            + "reflection to one minus the scaled coordinate. The real-part "
                            + "equivalence proves that the structural vertical line is invariant.")),
                    Paragraph(Text(
                        "The source calls this vertical line a fixed line. For the displayed "
                            + "holomorphic affine map that wording is false pointwise: solving "
                            + "J_qc(s) = s leaves only the real structuralZero. The theorem records "
                            + "both the valid setwise statement and the corrected fixed locus.")),
                    Paragraph(Text(
                        "Repository searches found the scaling owner but no conjugacy or fixed-locus "
                            + "theorem. Pinned Mathlib contributes field normalization and complex "
                            + "linear arithmetic only."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula() => Disp(Seq(
        Forall, Sp, F.Id("s"), InMacro, Mathbb, Grp(F.Id("C")), Comma, Quad,
        F.Id("phi"), Caret, Grp(D(2)), F.Id("J"), Underscore, Grp(F.Id("qc")),
        Open, F.Id("s"), Close, Eq, D(1), Minus, F.Id("phi"), Caret, Grp(D(2)), F.Id("s"),
        Quad, Land, Quad,
        Open, Re, Open, F.Id("J"), Underscore, Grp(F.Id("qc")), Open, F.Id("s"), Close,
        Close, Eq, F.Id("s"), Underscore, Grp(F.Id("star")), Iff,
        Re, Open, F.Id("s"), Close, Eq, F.Id("s"), Underscore, Grp(F.Id("star")), Close,
        Quad, Land, Quad,
        Open, F.Id("J"), Underscore, Grp(F.Id("qc")), Open, F.Id("s"), Close,
        Eq, F.Id("s"), Iff, F.Id("s"), Eq, F.Id("s"), Underscore, Grp(F.Id("star")), Close));
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.FixedPoints;

internal sealed class LimitUniversalPropertiesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Colimit cocones are initial and limit cones are terminal.",
        H("Universal Properties of Limits and Colimits"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("colimit-initial-and-limit-terminal"),
                DeclarationHandle.Create(
                    "D5/S1/FixedPoints/LimitUniversalProperties."
                        + "colimit_initial_and_limit_terminal"),
                H("Colimits are initial and limits are terminal"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open,
                    Operatorname, Grp(F.Id("Nonempty")), Open,
                    Operatorname, Grp(F.Id("IsColimit")), Open, F.Id("c"), Close, Close,
                    Sp, Leftrightarrow, Sp,
                    Operatorname, Grp(F.Id("Nonempty")), Open,
                    Operatorname, Grp(F.Id("IsInitial")), Open, F.Id("c"), Close, Close, Close,
                    Sp, Land, Sp,
                    Open,
                    Operatorname, Grp(F.Id("Nonempty")), Open,
                    Operatorname, Grp(F.Id("IsLimit")), Open, F.Id("l"), Close, Close,
                    Sp, Leftrightarrow, Sp,
                    Operatorname, Grp(F.Id("Nonempty")), Open,
                    Operatorname, Grp(F.Id("IsTerminal")), Open, F.Id("l"), Close, Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For any diagram F, a cocone c satisfies the colimit universal property "
                            + "exactly when it is an initial object in the category of cocones. "
                            + "Dually, a cone l satisfies the limit universal property exactly "
                            + "when it is terminal in the category of cones. Nonempty makes the "
                            + "existence of each universal-property structure propositional.")),
                    Paragraph(Text(
                        "The pinned Mathlib source was searched before proving. Its equivalences "
                            + "Cocone.isColimitEquivIsInitial and "
                            + "Cone.isLimitEquivIsTerminal are exact matches, so the Lean proof "
                            + "only applies their forward and inverse maps.")),
                    Paragraph(Text(
                        "The formal scope is Proposition 2 in source remark 27.559: the direct "
                            + "limit has the initial-cocone universal property and the inverse "
                            + "limit has the terminal-cone universal property. No claim is made "
                            + "here about state-space duality, Busch uniqueness, contextuality, "
                            + "Kolmogorov extension, or entropy and sharpness."))),
                DescribeRole.Theorem))));
}

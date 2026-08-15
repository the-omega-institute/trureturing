using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics.EscapeProbability;

internal sealed class ProbabilityBoundsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform escape probability lies in the closed unit interval for all finite address and output types.",
        H("Uniform Escape Probability Bounds"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("uniform-escape-probability-bounds"),
                DeclarationHandle.Create(
                    "D5/S0/Asymptotics/EscapeProbability/ProbabilityBounds."
                        + "escape_probability_bounds"),
                H("Uniform escape probability is between zero and one"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("A"), Comma, Sp,
                    OpenBracket, Operatorname, Grp(F.Id("Fintype")), Sp, F.Id("A"),
                    CloseBracket, Comma, Sp,
                    Forall, Sp, F.Id("Y"), Comma, Sp,
                    OpenBracket, Operatorname, Grp(F.Id("Fintype")), Sp, F.Id("Y"),
                    CloseBracket, Comma, Sp,
                    Forall, Sp, F.Id("f"), Colon, Sp, F.Id("Y"), Sp, To, Sp, F.Id("Y"),
                    Comma, Sp,
                    D(0), Sp, Leq, Sp,
                    Call("escapeProbability", F.Id("A"), F.Id("f")),
                    Sp, Land, Sp,
                    Call("escapeProbability", F.Id("A"), F.Id("f")),
                    Sp, Leq, Sp, D(1), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The escaped listings form a subtype of the finite space of all listings. "
                            + "Their cardinality is therefore at most the total cardinality, while "
                            + "both cardinalities are nonnegative. Dividing these cardinalities in "
                            + "the frozen definition gives the two bounds, including when the "
                            + "listing space is empty.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies Finite.card_subtype_le and the nonnegative "
                            + "division lemmas used to compare the uniform escape ratio with zero "
                            + "and one."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S0/Asymptotics/FixedPointFreeEscapeProbability"))]));
}

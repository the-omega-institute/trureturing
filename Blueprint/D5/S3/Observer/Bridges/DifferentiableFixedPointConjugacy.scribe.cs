using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Bridges;

internal sealed class DifferentiableFixedPointConjugacyDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Bridges/DifferentiableFixedPointConjugacy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nondegenerate differentiable observer bridge preserves the local multiplier.",
        H("Differentiable Fixed-Point Bridge"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nondegenerate-bridge-preserves-multiplier"),
                DeclarationHandle.Create(Prefix + "multiplier_eq_of_nondegenerate_bridge"),
                H("The local multiplier is invariant under a nondegenerate bridge"),
                StatementSource.FromAuthor(MultiplierFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At a fixed source state, differentiating h composed with F equals G "
                            + "composed with h. The chain rule intertwines the two multipliers.")),
                    Paragraph(Text(
                        "When the bridge derivative is nonzero, it can be cancelled in one real "
                            + "dimension, giving equality of source and target multipliers.")),
                    Paragraph(Text(
                        "Attracting, neutral, and repelling classifications are therefore "
                            + "preserved. Singular observer bridges are intentionally excluded."))),
                DescribeRole.Theorem))));

    private static Formula MultiplierFormula()
    {
        Formula h = F.Id("h");
        Formula source = F.Id("F");
        Formula target = F.Id("G");
        Formula x = F.Id("x");
        Formula dh = Sub(F.Id("d"), F.Id("h"));
        Formula dSource = Sub(F.Id("d"), F.Id("F"));
        Formula dTarget = Sub(F.Id("d"), F.Id("G"));
        return Disp(Seq(
            Call("Semiconj", h, source, target), Sp, Land, Sp,
            Call("IsFixedPt", source, x), Sp, Land, Sp,
            dh, Sp, Neq, Sp, D(0), Sp, Rightarrow, Sp,
            dSource, Sp, Eq, Sp, dTarget));
    }
}

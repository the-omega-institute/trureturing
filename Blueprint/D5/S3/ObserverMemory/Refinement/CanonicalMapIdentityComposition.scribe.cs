using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Refinement;

internal sealed class CanonicalMapIdentityCompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical predictive-completion maps satisfy identity and composition.",
        H("Canonical Map Identity and Composition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("canonical-map-identity-and-composition"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Refinement/CanonicalMapIdentityComposition."
                        + "canonical_map_identity_and_composition"),
                H("Canonical maps compose and have identities"),
                StatementSource.FromAuthor(CanonicalMapFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a fixed finite nonempty state carrier and a deterministic update, "
                            + "each readout defines a predictive completion as the quotient by "
                            + "equality of all future readout values.")),
                    Paragraph(Text(
                        "When one readout factors through another, the existing quotient factor "
                            + "construction supplies the canonical map between their completed "
                            + "state spaces and its equation on every source projection.")),
                    Paragraph(Text(
                        "Applying that projection equation first to the identity factorization "
                            + "and then to a chain of two factorizations proves the displayed "
                            + "identity and composition laws by quotient induction.")),
                    Paragraph(Text(
                        "Repository search found and directly applied the exact declarations "
                            + "completionFactor and completion_factor_projection. No imported "
                            + "theorem packaged both displayed map laws."))),
                DescribeRole.Theorem))));

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula Kappa(Formula left, Formula right) =>
        Subscript(F.Id("kappa"), Seq(left, Comma, Sp, right));

    private static Formula CanonicalMapFormula()
    {
        Formula q = F.Id("q");
        Formula r = F.Id("r");
        Formula s = F.Id("s");
        Formula identity = F.Id("id");

        return Disp(Seq(
            Open,
            Forall, Sp, q, Comma, Sp,
            Kappa(q, q), Sp, Eq, Sp, identity,
            Close, Sp, Land, Esc, Open,
            Forall, Sp, q, Comma, Sp, r, Comma, Sp, s, Comma, Esc,
            Call("Refines", q, r), Sp, Land, Sp, Call("Refines", r, s),
            Sp, Rightarrow, Sp,
            Kappa(q, s), Sp, Eq, Sp,
            Kappa(r, s), Sp, Circ, Sp, Kappa(q, r),
            Close, Dot));
    }
}

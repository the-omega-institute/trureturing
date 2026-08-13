using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics;

internal sealed class MetallicFamilyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The explicit quadratic-family value has reciprocal equal to its shift by the integer parameter.",
        H("Metallic Family"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("metallic-family-reciprocal-identity"),
                DeclarationHandle.Create(
                    "D5/S0/Asymptotics/MetallicFamily.metallic_family_value"),
                H("A quadratic-family value and its reciprocal"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    F.Id("metallicValue"), Open, F.Id("n"), Close, Eq, Frac, Grp(F.Id("n"), Plus, Sqrt, Open,
                    F.Id("n"), Caret, Grp(D(2)), Plus, D(4), Close), Grp(D(2)), Sp, Land, Sp,
                    Frac, Grp(D(1)), Grp(F.Id("metallicValue"), Open, F.Id("n"), Close), Eq,
                    F.Id("metallicValue"), Open, F.Id("n"), Close, Minus, F.Id("n"), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The Lean proof expands the displayed radical definition, uses the standard "
                        + "square-root nonnegativity and square identities from Mathlib, and clears "
                        + "the positive denominator by elementary ring arithmetic.")),
                    Paragraph(Text(
                        "This is an honest partial closure of the metal-family clause in source theorem "
                        + "5.7. The reciprocity law for the cotangent series, convergence assertions, "
                        + "special-value reductions, and all numerical certificates remain unresolved "
                        + "subitems of the source atom."))),
                DescribeRole.Theorem))));
}

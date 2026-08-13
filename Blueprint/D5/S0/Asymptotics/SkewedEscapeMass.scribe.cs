using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics;

internal sealed class SkewedEscapeMassDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A one-slot skewed escape mass is one minus the fixed-output mass.",
        H("Skewed Escape Mass"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("skewed-one-slot-escape-complement"),
                DeclarationHandle.Create(
                    "D5/S0/Asymptotics/SkewedEscapeMass.escape_mass_eq_one_sub_fixed_mass"),
                H("One-slot escape mass complements fixed-output mass"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("q"), Comma, Sp, F.Id("f"), Comma, Sp,
                    F.Id("escapeMass"), Open, F.Id("q"), Comma, Sp, F.Id("f"), Close,
                    Sp, Eq, Sp, D(1), Sp, Minus, Sp,
                    F.Id("fixedMass"), Open, F.Id("q"), Comma, Sp, F.Id("f"), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a finite output type with a probability mass function q and an "
                        + "output transformation f, escapeMass sums q over outputs changed by f, "
                        + "while fixedMass sums q over outputs fixed by f.")),
                    Paragraph(Text(
                        "The proof uses the finite filter partition identity and PMF.tsum_coe, "
                        + "so the two output classes exhaust total mass one.")),
                    Paragraph(Text(
                        "This is an honest partial closure of clause (iv), the A = 1 edge case, "
                        + "of priced-interface theorem 7.1'. The general independent-slot product "
                        + "formula, pairwise intersection formula, uniform specialization, and "
                        + "engineering corollary remain unresolved."))),
                DescribeRole.Theorem)),
        []));
}

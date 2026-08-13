using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Deficit;

internal sealed class FixedModulusNoncongruenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "No fixed modulus at least two determines the golden-addition deficit.",
        H("Fixed-Modulus Noncongruence of the Golden-Addition Deficit"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fixed-modulus-noncongruence-of-the-deficit"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/FixedModulusNoncongruence.deficit_not_determined_by_fixed_modulus"),
                H("Congruent input pairs can have different deficits"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("m"), Sp, Geq, Sp, D(2), Comma, Quad, Sp,
                    Exists, Sp, F.Id("v"), Underscore, D(1), Comma, Sp,
                    F.Id("v"), Underscore, D(2), Comma, Sp,
                    F.Id("v"), Underscore, D(1), Apos, Comma, Sp,
                    F.Id("v"), Underscore, D(2), Apos, Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("N")), Comma, Quad, Sp,
                    F.Id("v"), Underscore, D(1), Equiv, Sp,
                    F.Id("v"), Underscore, D(1), Apos, Sp,
                    Open, Operatorname, Grp(F.Id("mod")), Sp, F.Id("m"), Close,
                    Sp, Land, Sp,
                    F.Id("v"), Underscore, D(2), Equiv, Sp,
                    F.Id("v"), Underscore, D(2), Apos, Sp,
                    Open, Operatorname, Grp(F.Id("mod")), Sp, F.Id("m"), Close,
                    Comma, Quad, Sp,
                    F.Id("c"), Open, F.Id("v"), Underscore, D(1), Comma, Sp,
                    F.Id("v"), Underscore, D(2), Close, Neq, Sp,
                    F.Id("c"), Open, F.Id("v"), Underscore, D(1), Apos, Comma, Sp,
                    F.Id("v"), Underscore, D(2), Apos, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural modulus m at least two, there are two pairs of natural "
                        + "inputs that agree coordinatewise modulo m but whose normalized golden-addition "
                        + "deficits differ. This strengthens the source's finite certificate for moduli "
                        + "2 through 60 to a structural theorem for every fixed modulus.")),
                    Paragraph(Text(
                        "The existing displacement theorem identifies each model-set reading with an "
                        + "integer golden Beatty shift plus a linear conjugate term. The linear terms "
                        + "cancel in the additive coboundary, so the analytic deficit equals the Beatty "
                        + "deficit. Pinned Mathlib then supplies density of irrational multiples on the "
                        + "additive circle. Applying that theorem to the golden rotation restricted to "
                        + "any arithmetic progression produces congruent inputs in a positive-deficit "
                        + "phase interval and in a zero-deficit interval.")),
                    Paragraph(Text(
                        "This is an honest partial closure of proposition 6.28(ii). It does not formalize "
                        + "the prime-classification blindness interpretation, the zero-slice frequency "
                        + "1/phi, or the positive-slice frequency 1/phi^2; those independently testable "
                        + "claims remain unresolved and the source atom remains partial and open."))),
                DescribeRole.Theorem)),
        []));
}

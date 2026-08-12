using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Phase;

internal sealed class PythagoreanInputValidatorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A decidable integer gate accepts a genuine pin input and rejects a one-coordinate perturbation.",
        H("Pythagorean Input Validator"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("boolean-acceptance-iff-eisenstein-equation"),
                DeclarationHandle.Create(
                    "D5/S1/Phase/PythagoreanInputValidator.accepts_iff"),
                H("Boolean acceptance is equivalent to the Eisenstein equation"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("x"), Colon, Sp, Operatorname, Grp(F.Id("PinInput")),
                    Comma, Esc, F.Id("x"), Dot, F.Id("accepts"), Sp, Eq, Sp,
                    F.Id("true"), Sp, Leftrightarrow, Sp,
                    F.Id("x"), Dot, F.Id("beta"), Caret, Grp(D(2)), Sp, Minus, Sp,
                    F.Id("x"), Dot, F.Id("beta"), Sp, Star, Sp, F.Id("x"), Dot,
                    GammaLower, Underscore, Grp(D(0)), Sp, Plus, Sp, F.Id("x"), Dot,
                    GammaLower, Underscore, Grp(D(0)), Caret, Grp(D(2)), Sp, Eq, Sp,
                    F.Id("x"), Dot, F.Id("m"), Sp,
                    Star, Sp, Open, F.Id("x"), Dot, F.Id("m"), Sp, Plus, Sp, D(1), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every PinInput record, the executable Boolean gate returns true exactly "
                            + "when the normalized Eisenstein equation holds for its three fields. The proof reduces "
                            + "Boolean decision to the proposition and then reuses the existing "
                            + "Pythagorean-gate normalization theorem.")),
                    Paragraph(Text(
                        "This validator checks only the displayed Diophantine equation. It makes no "
                            + "claim about primitivity, orbit provenance, or any stronger admissibility "
                            + "condition."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("genuine-and-perturbed-input-certificate"),
                DeclarationHandle.Create(
                    "D5/S1/Phase/PythagoreanInputValidator.genuine_and_perturbed_input_certificate"),
                H("A genuine input is accepted and its beta perturbation is rejected"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("PinInput"), Dot, F.Id("accepts"), Open, OpenBrace,
                    F.Id("beta"), Sp, Colon, Sp, Eq, Sp, Minus, D(3), D(8), D(4),
                    Comma, Sp, GammaLower, Underscore, Grp(D(0)), Sp, Colon, Sp, Eq,
                    Sp, D(1), D(3), D(8),
                    Comma, Sp, F.Id("m"), Sp, Colon, Sp, Eq, Sp, D(4), D(6), D(8),
                    CloseBrace, Close,
                    Sp, Eq, Sp, F.Id("true"), Sp, Land, Sp,
                    F.Id("PinInput"), Dot, F.Id("accepts"), Open, OpenBrace,
                    F.Id("beta"), Sp, Colon, Sp, Eq, Sp, Minus, D(3), D(8), D(3),
                    Comma, Sp, GammaLower, Underscore, Grp(D(0)), Sp, Colon, Sp, Eq,
                    Sp, D(1), D(3), D(8),
                    Comma, Sp, F.Id("m"), Sp, Colon, Sp, Eq, Sp, D(4), D(6), D(8),
                    CloseBrace, Close,
                    Sp, Eq, Sp, F.Id("false")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The source-attested PinInput record with beta minus 384, gamma-zero 138, and m 468 "
                        + "passes the gate. Changing only its beta field to minus 383 fails it. These opposite "
                        + "Boolean outcomes ensure that acceptance depends on the supplied input and "
                        + "is not a constant or vacuous predicate."))),
                DescribeRole.Theorem))));
}

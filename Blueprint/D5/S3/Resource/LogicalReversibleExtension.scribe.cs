using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Resource;

internal sealed class LogicalReversibleExtensionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every function into an additive group has a reversible work-register extension.",
        H("Logical Reversibility by Retaining the Input"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("function-has-reversible-work-register-extension"),
                DeclarationHandle.Create(
                    "D5/S3/Resource/LogicalReversibleExtension.logical_reversible_extension"),
                H("A retained input makes the computation reversible"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("X"), Comma, F.Id("A"), Comma, Esc,
                    OpenBracket, Operatorname, Grp(F.Id("AddGroup")), Open, F.Id("A"), Close,
                    CloseBracket, Comma, Esc,
                    Forall, Sp, F.Id("f"), Colon, F.Id("X"), To, Sp, F.Id("A"), Comma, Esc,
                    Exists, Sp, F.Id("e"), Colon,
                    Operatorname, Grp(F.Id("Equiv")), Open,
                    F.Id("X"), Times, Sp, F.Id("A"), Comma,
                    F.Id("X"), Times, Sp, F.Id("A"), Close, Comma, Esc,
                    Forall, Sp, F.Id("x"), Comma, F.Id("a"), Comma, Esc,
                    F.Id("e"), Open, F.Id("x"), Comma, F.Id("a"), Close, Eq,
                    Open, F.Id("x"), Comma, F.Id("f"), Open, F.Id("x"), Close,
                    Plus, F.Id("a"), Close, Sp, Land, Sp, Esc,
                    Forall, Sp, F.Id("x"), Comma, Esc,
                    F.Id("e"), Open, F.Id("x"), Comma, D(0), Close, Eq,
                    Open, F.Id("x"), Comma, F.Id("f"), Open, F.Id("x"), Close,
                    Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The selected source clause says that logically reversible computation "
                        + "exists. For a function f into an additive group, retain the input x "
                        + "and add f(x) to an auxiliary register. Mathlib's Equiv.prodShear and "
                        + "Equiv.addLeft make this transformation an equivalence, while a zero "
                        + "auxiliary register produces the pair (x,f(x)).")),
                    Paragraph(Text(
                        "The additive register models the reversible accumulator used by finite "
                        + "bit computations, with exclusive-or as its group operation. The theorem "
                        + "is more general than that intended specialization and uses no physical "
                        + "cost model.")),
                    Paragraph(Text(
                        "This is a partial closure of proposition 3.9. The claim that the heat "
                        + "column can vanish, the reversible-simulation time-space upper-bound "
                        + "family, optimality within reversible pebble games, lower bounds outside "
                        + "that model, and the five-column synthesis remain unresolved."))),
                DescribeRole.Theorem)),
        []));
}

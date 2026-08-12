using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Carrier;

internal sealed class GoldenDiscriminantDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The golden polynomial has discriminant five and the golden ratio satisfies it.",
        H("Golden Discriminant"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-polynomial-discriminant-and-fixed-point"),
                DeclarationHandle.Create(
                    "D5/S0/Carrier/GoldenDiscriminant.golden_discriminant_spec"),
                H("Discriminant and fixed-point identity"),
                StatementSource.FromAuthor(Disp(Seq(
                    Grp(Minus, D(1)), Caret, D(2), Sp, Minus, Sp,
                    D(4), Sp, Times, Sp, D(1), Sp, Times, Sp, Grp(Minus, D(1)),
                    Sp, Eq, Sp, D(5), Sp, Land, Sp,
                    Varphi, Caret, D(2), Sp, Eq, Sp, Varphi, Sp, Plus, Sp, D(1)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The first conjunct computes the discriminant of x squared minus x minus one from its integer coefficients. The second conjunct reuses the frozen golden-ratio specification."))),
                DescribeRole.Theorem))));
}

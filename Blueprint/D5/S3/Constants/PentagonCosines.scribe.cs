using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants;

internal sealed class PentagonCosinesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeNode.Create(
            "The doubled pentagon cosines read the golden ratio, its inverse, and root five.",
            H("Pentagon Cosines"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("pentagon-golden-cosines"),
                    DeclarationHandle.Create("D5/S3/Constants/PentagonCosines.pentagon_golden_cosines"),
                    H("The pentagon angles read the golden ratio exactly"),
                    StatementSource.FromAuthor(Disp(Seq(
                                            D(2), Operatorname, Grp(F.Id("cos")), Open, Pi, Slash, D(5), Close,
                                            Eq, Varphi, Comma, Qquad, Sp,
                                            D(2), Operatorname, Grp(F.Id("cos")), Open, D(2), Pi, Slash, D(5), Close,
                                            Eq, Varphi, Caret, Grp(Minus, D(1)), Comma, Qquad, Sp,
                                            D(2), Operatorname, Grp(F.Id("cos")), Open, Pi, Slash, D(5), Close,
                                            Plus,
                                            D(2), Operatorname, Grp(F.Id("cos")), Open, D(2), Pi, Slash, D(5), Close,
                                            Eq, Sqrt, Grp(D(5)), Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                                            Paragraph(Text(
                                                "Doubling the cosine at the acute pentagon angle pi over five "
                                                + "yields the golden ratio itself, and doubling it at the obtuse "
                                                + "angle two pi over five yields the inverse golden ratio. The two "
                                                + "doubles sum to sqrt(5), the square root of the discriminant five "
                                                + "shared by both readings, and the obtuse double is additionally "
                                                + "proved irrational, so no rational register accommodates the "
                                                + "five-fold turn. These are classical pentagon identities, proved "
                                                + "here natively over the pinned library.")),
                                            Paragraph(Text(
                                                "The proof starts from the library's closed form for the cosine of "
                                                + "pi over five, namely (1 + sqrt(5)) / 4, derives the obtuse value "
                                                + "(sqrt(5) - 1) / 4 by the double-angle formula, and identifies the "
                                                + "two doubles with the golden ratio and its inverse through the "
                                                + "library's golden-ratio and golden-conjugate identities. The sum "
                                                + "clause is the difference identity between the golden ratio and "
                                                + "its conjugate, and the irrationality clause transports the "
                                                + "irrationality of the golden ratio through inversion."))),
                    DescribeRole.Theorem
                ))));
}

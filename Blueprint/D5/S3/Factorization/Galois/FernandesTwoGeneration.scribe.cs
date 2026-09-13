using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Galois;

internal sealed class FernandesTwoGenerationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Factorization/Galois/FernandesTwoGeneration.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two generators for the equal-sign subgroup whenever the second degree is two.",
        H("Two generators for equal-sign permutation pairs"),
        Blocks(
            Paragraph(Text(
                "Let Gamma(m,n) be the subgroup of S_m times S_n consisting of pairs "
                    + "whose permutation signs agree. Equivalently, it is the kernel "
                    + "of the ratio of the two signs.")),
            Describe.Lean(
                DescribeId.Create("fernandes-second-degree-two"),
                DeclarationHandle.Create(Prefix + "fernandes_two_generation_n_two"),
                H("Second degree two"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("m"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    F.Id("m"), Sp, Geq, Sp, D(2), Sp, Rightarrow, Sp,
                    Generated(F.Id("m"), D(2))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Sign is injective on S_2, so projection onto S_m is injective on Gamma(m,2). "
                        + "Lift a full cycle and an adjacent transposition to equal-sign pairs. "
                        + "Their projections generate S_m, hence the pairs generate Gamma(m,2)."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The two-generator assertion for degree pairs with second degree at least three "
                    + "is not established by this statement.")))));

    private static Formula Group(Formula m, Formula n) =>
        Seq(Gamma, Open, m, Comma, n, Close);

    private static Formula Generated(Formula m, Formula n) => Seq(
        Exists, Sp, F.Id("g"), Underscore, Grp(D(1)), Comma,
        F.Id("g"), Underscore, Grp(D(2)), Sp,
        InMacro, Sp, Group(m, n), Comma, Sp,
        Langle, Sp, F.Id("g"), Underscore, Grp(D(1)), Comma,
        F.Id("g"), Underscore, Grp(D(2)), Rangle,
        Sp, Eq, Sp, Group(m, n));
}

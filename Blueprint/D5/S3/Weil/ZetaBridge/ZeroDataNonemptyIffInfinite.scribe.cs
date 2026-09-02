using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class ZeroDataNonemptyIffInfiniteDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Weil/ZetaBridge/ZeroDataNonemptyIffInfinite."
            + "nonempty_zeroData_iff_infinite";

    public DocumentDefinition Create()
    {
        Formula rho = Rho;
        Formula zeroSet = Seq(
            OpenBrace, rho, Sp, Mid, Sp, Call("IsNontrivialZero", rho), CloseBrace);

        return DocumentDefinition.Create(ScribeNode.Create(
            "ZeroData is inhabited exactly when the set of nontrivial zeta zeros is infinite.",
            H("ZeroData Nonemptiness and Infinitely Many Nontrivial Zeros"),
            Blocks(Describe.Lean(
                DescribeId.Create("zero-data-nonempty-iff-infinitely-many-nontrivial-zeros"),
                DeclarationHandle.Create(Declaration),
                H("Exact nonvacuity characterization"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("Nonempty", F.Id("ZeroData")), Sp, Iff, Sp,
                    Call("Infinite", zeroSet)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Forward, the injective ZeroData enumeration embeds the natural numbers "
                            + "in the nontrivial-zero set. Backward, Mathlib's closed and discrete "
                            + "zeta-zero set is countable and compact-finite; an infinite countable "
                            + "subtype can therefore be enumerated without duplicates. Analytic "
                            + "order supplies its unique positive multiplicities, while the zeta "
                            + "functional equation and conjugation identity preserve those "
                            + "multiplicities and induce the required permutations.")),
                    Paragraph(Text(
                        "This theorem neither proves infinitude nor exhibits a zero. It does not "
                            + "establish O-6 nonvacuity; it reduces ZeroData nonvacuity exactly to "
                            + "the open infinitude of the nontrivial-zero set."))),
                DescribeRole.Theorem))));
    }
}

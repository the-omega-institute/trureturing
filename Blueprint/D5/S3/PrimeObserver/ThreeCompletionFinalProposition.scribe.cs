using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeObserver;

internal sealed class ThreeCompletionFinalPropositionDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/PrimeObserver/ThreeCompletionFinalProposition."
            + "prime_observer_three_completion_final_proposition";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime exponents, realizability mass, and operator phase are distinct completions.",
        H("Three Prime-Observer Completions"),
        Blocks(Describe.Lean(
            DescribeId.Create("prime-observer-three-completion-final-proposition"),
            DeclarationHandle.Create(Declaration),
            H("Deterministic, probabilistic, and operator completion"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Positive integers are reconstructed bijectively from finitely supported "
                        + "prime-exponent profiles.")),
                Paragraph(Text(
                    "The independent geometric profile is globally realizable precisely when "
                        + "the zeta parameter is greater than one.")),
                Paragraph(Text(
                    "A named pair of qubit density states has one prime-diagonal image but "
                        + "distinct operators, so commuting diagonal observations do not give "
                        + "operator tomography."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula() => Disp(Seq(
        F.Id("PrimeExponentBijection"),
        Sp, Land, Sp,
        Grp(Exists, Sp, F.Id("globalLaw"), Sp, Iff, Sp, F.Id("s"), Sp, Gt, Sp, Num(1)),
        Sp, Land, Sp,
        Grp(F.Id("samePrimeDiagonal"), Sp, Land, Sp, F.Id("differentOperator")),
        Sp, Land, Sp,
        F.Id("PrimeDiagonalLanguage"), Sp, Subset, Sp, F.Id("OperatorLanguage"), Dot));
}

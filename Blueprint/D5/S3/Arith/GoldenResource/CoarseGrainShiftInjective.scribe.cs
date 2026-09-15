using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.GoldenResource;

internal sealed class CoarseGrainShiftInjectiveDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Arith/GoldenResource/CoarseGrainShiftInjective.b_shift_injective";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Agreement at every forward shift determines the index seen by the golden observation.",
        H("Forward-Shift Injectivity of the Golden Observation"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-observation-forward-shift-injectivity"),
            DeclarationHandle.Create(Declaration),
            H("Forward-shift agreement determines the index"),
            StatementSource.FromAuthor(StatementFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The function b is the reused frozen golden exponent observation from "
                        + "GoldenDivisorLanguage. It is defined there by b(a) equal to fib of "
                        + "greatestFib(a plus one), minus one. The observation is monotone, "
                        + "but it is not asserted to be strictly monotone.")),
                Paragraph(Text(
                    "For natural indices a and c, equality of b(a plus t) and b(c plus t) "
                        + "for every natural offset t forces a and c to be equal. For unequal "
                        + "indices, a later Fibonacci endpoint is fixed by the larger shifted "
                        + "index while the smaller shifted index remains strictly below it.")),
                Paragraph(Text(
                    "This is the additive equality stated as Theorem 2.1 in the source text. "
                        + "It does not state the multiplicative Corollary 2.2 or reconstruct "
                        + "an integer from a family of prime exponents."))),
            DescribeRole.Theorem))));

    private static Formula StatementFormula()
    {
        Formula a = F.Id("a");
        Formula c = F.Id("c");
        Formula t = F.Id("t");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula shiftedA = Seq(F.Id("b"), Open, a, Plus, t, Close);
        Formula shiftedC = Seq(F.Id("b"), Open, c, Plus, t, Close);

        return Disp(Seq(
            Forall, Sp, a, Comma, Sp, c, Sp, InMacro, Sp, naturals, Comma, Sp,
            Open, Forall, Sp, t, Sp, InMacro, Sp, naturals, Comma, Sp,
            shiftedA, Sp, Eq, Sp, shiftedC, Close, Sp, Implies, Sp,
            a, Sp, Eq, Sp, c));
    }
}

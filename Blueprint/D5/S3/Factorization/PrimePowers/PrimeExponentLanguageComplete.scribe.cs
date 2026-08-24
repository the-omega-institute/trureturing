using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.PrimePowers;

internal sealed class PrimeExponentLanguageCompleteDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete prime-exponent readout separates positive natural numbers and has singleton fibers.",
        H("Completeness of the Prime-Exponent Language"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-exponent-language-complete"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/PrimePowers/PrimeExponentLanguageComplete."
                    + "prime_exponent_language_complete"),
                H("The full prime-exponent language is complete on positive naturals"),
                StatementSource.FromAuthor(CompleteFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The readout assigns to each positive natural number its full finitely "
                            + "supported family of prime exponents. Distinct positive naturals "
                            + "have distinct readouts, so the map loses no arithmetic information.")),
                    Paragraph(Text(
                        "Equivalently, fixing any positive natural n leaves exactly one input with "
                            + "the same exponent data: n itself. The positivity restriction is "
                            + "essential because the unrestricted natural-number factorizations of "
                            + "zero and one are both the empty exponent family.")),
                    Paragraph(Text(
                        "The proof invokes the injectivity of Mathlib's factorization equivalence "
                            + "and then applies that injectivity pointwise to identify each readout "
                            + "fiber with its singleton."))),
                DescribeRole.Theorem))));

    private static Formula CompleteFormula()
    {
        Formula positiveNaturals = Seq(
            Mathbb, Grp(F.Id("N")), Underscore, Grp(Gt, D(0)));
        Formula language = F.Id("primeExponentLanguage");
        Formula n = F.Id("n");
        Formula m = F.Id("m");

        return Disp(Seq(
            Operatorname, Grp(F.Id("Injective")), Open, language, Close,
            Sp, Land, Sp,
            Forall, Sp, n, Sp, InMacro, Sp, positiveNaturals, Comma, Sp,
            OpenBrace, m, Sp, InMacro, Sp, positiveNaturals, Sp, Mid, Sp,
            Call("primeExponentLanguage", m), Sp, Eq, Sp,
            Call("primeExponentLanguage", n), CloseBrace,
            Sp, Eq, Sp, OpenBrace, n, CloseBrace, Dot));
    }
}

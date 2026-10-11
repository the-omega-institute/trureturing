using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.NumberTheory.ModularForms;

internal sealed class EisensteinPrimeCoefficientDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The prime q-coefficient of a level-one Eisenstein series is the Bernoulli normalization times 1 plus p to the k minus one.",
        H("Eisenstein Prime Coefficient"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("eisenstein-prime-q-coefficient"),
                DeclarationHandle.Create(
                    "D5/S1/NumberTheory/ModularForms/EisensteinPrimeCoefficient."
                        + "eisenstein_qExpansion_coeff_prime"),
                H("Prime q-coefficient"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("k"), Comma, Sp, F.Id("p"), Comma, Sp,
                    F.Id("primeQCoefficient"), Eq, Sp,
                    F.Id("bernoulliMultiplier"), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The q-expansion coefficient theorem reduces the claim to the divisor sum at a prime. "
                            + "The prime divisor description then gives the two terms 1 and p^(k-1).")),
                    Paragraph(Text(
                        "This is the arithmetic input for a later formalization of the Hecke operator T_p on q-expansions."))),
                DescribeRole.Theorem))));
}

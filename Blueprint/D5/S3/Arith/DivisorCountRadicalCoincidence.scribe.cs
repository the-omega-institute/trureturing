using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class DivisorCountRadicalCoincidenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive integer whose divisor count divides its squarefree kernel has those two quantities equal.",
        H("Divisor Count and Radical Rigidity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("divisor-count-equals-radical-under-divisibility"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/DivisorCountRadicalCoincidence.radical_eq_card_divisors_of_dvd"),
                H("Divisibility forces equality"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The radical is squarefree, so every divisor of it is squarefree. "
                            + "The prime-exponent product for the divisor count contributes "
                            + "at least one prime factor for every distinct prime factor of k. "
                            + "Divisibility gives the reverse bound on distinct prime factors. "
                            + "The two prime-factor sets therefore coincide, and their products "
                            + "give the stated equality."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula k = F.Id("k");
        Formula divisorCount = Call("card", Call("divisors", k));
        Formula radical = Call("radical", k);

        return Disp(Seq(
            Forall, Sp, k, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
            D(1), Sp, Le, Sp, k, Sp, Rightarrow, Sp,
            divisorCount, Sp, Mid, Sp, radical, Sp, Rightarrow, Sp,
            radical, Sp, Eq, Sp, divisorCount));
    }
}

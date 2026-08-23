using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Ledger;

internal sealed class GenerationArrowOfTimeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime-exponent length is additive, equals the logarithm of the encoded number, and strictly grows under every nonzero generation.",
        H("Generation Gives an Arrow of Time"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-exponent-length-is-additive"),
                DeclarationHandle.Create("D5/S1/Ledger/GenerationArrowOfTime.length_add"),
                H("Prime-exponent length is additive"),
                StatementSource.FromAuthor(LengthAddFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Adding two prime-exponent states adds their exponent on every prime. "
                        + "The logarithmic weights are fixed, so the weighted finite sum of "
                        + "the combined state splits into the sum of the two lengths."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("length-is-the-logarithm-of-the-generated-number"),
                DeclarationHandle.Create(
                    "D5/S1/Ledger/GenerationArrowOfTime.length_eq_log_generatedNumber"),
                H("Length is the logarithm of the generated number"),
                StatementSource.FromAuthor(LengthEqualsLogFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A prime-exponent state encodes the product of each prime raised to its "
                        + "recorded exponent. Taking the logarithm turns that finite product "
                        + "into exactly the exponent-weighted sum that defines its length."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("every-nonzero-update-has-positive-length"),
                DeclarationHandle.Create("D5/S1/Ledger/GenerationArrowOfTime.length_pos"),
                H("Every nonzero update has positive length"),
                StatementSource.FromAuthor(PositiveLengthFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A nonzero state has a positive exponent on at least one prime. Every "
                        + "prime has positive logarithm, so that coordinate contributes "
                        + "strictly positively while all remaining coordinates contribute "
                        + "nonnegatively."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("nonzero-generation-strictly-increases-length"),
                DeclarationHandle.Create(
                    "D5/S1/Ledger/GenerationArrowOfTime.length_strictly_increases_under_generation"),
                H("Nonzero generation strictly increases length"),
                StatementSource.FromAuthor(StrictGrowthFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Generation adds an update vector to the current ledger state. Additivity "
                        + "says that the new length is the old length plus the update length, "
                        + "and a nonzero update has positive length. Thus every nonzero "
                        + "generation moves strictly forward in this logarithmic coordinate."))),
                DescribeRole.Theorem))));

    private static Formula LengthAddFormula()
    {
        Formula a = F.Id("a");
        Formula u = F.Id("u");

        return Disp(Seq(
            Forall, Sp, a, InMacro, Sp, PrimeExponent(), Comma, Esc,
            u, InMacro, Sp, PrimeExponent(), Comma, Esc,
            LengthOf(Seq(a, Sp, Plus, Sp, u)), Sp, Eq, Sp,
            LengthOf(a), Sp, Plus, Sp, LengthOf(u)));
    }

    private static Formula LengthEqualsLogFormula()
    {
        Formula a = F.Id("a");

        return Disp(Seq(
            Forall, Sp, a, InMacro, Sp, PrimeExponent(), Comma, Esc,
            LengthOf(a), Sp, Eq, Sp, LogOf(GeneratedNumberOf(a))));
    }

    private static Formula PositiveLengthFormula()
    {
        Formula u = F.Id("u");

        return Disp(Seq(
            Forall, Sp, u, InMacro, Sp, PrimeExponent(), Comma, Esc,
            u, Sp, Neq, Sp, D(0), Sp, Rightarrow, Sp,
            D(0), Sp, Lt, Sp, LengthOf(u)));
    }

    private static Formula StrictGrowthFormula()
    {
        Formula a = F.Id("a");
        Formula u = F.Id("u");

        return Disp(Seq(
            Forall, Sp, a, InMacro, Sp, PrimeExponent(), Comma, Esc,
            u, InMacro, Sp, PrimeExponent(), Comma, Esc,
            u, Sp, Neq, Sp, D(0), Sp, Rightarrow, Sp,
            LengthOf(Seq(a, Sp, Plus, Sp, u)), Sp, Gt, Sp, LengthOf(a)));
    }

    private static Formula PrimeExponent() =>
        Seq(Operatorname, Grp(F.Id("PrimeExponent")));

    private static Formula LengthOf(Formula value) =>
        Seq(Operatorname, Grp(F.Id("length")), Open, value, Close);

    private static Formula GeneratedNumberOf(Formula value) =>
        Seq(Operatorname, Grp(F.Id("generatedNumber")), Open, value, Close);

    private static Formula LogOf(Formula value) =>
        Seq(Log, Sp, Open, value, Close);
}

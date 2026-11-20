using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SubsetSpectrum;

internal sealed class MixedDigitDenominatorsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SubsetSpectrum/MixedDigitDenominators.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A restriction on mixing reduced denominators in dense integer coverage by four digits.",
        H("Mixed denominators in four-digit integer coverage"),
        Blocks(Describe.Lean(
            DescribeId.Create("no-mixed-denominators"),
            DeclarationHandle.Create(Prefix + "no_mixed_denominators_of_capacity_gap"),
            H("Two and three cannot both occur as reduced denominators"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let J be a finite index set, w a real weight family on J, and L a natural number. "
                    + "FourDigitIntegerCoverage means every integer level from zero through L minus one "
                    + "is represented by a sum with weights w and digits in zero through three. "
                    + "NoMixedHalfAndThirdWeights means that no two distinct coordinates of w have weights "
                    + "a divided by two and b divided by three with odd integer a and integer b indivisible "
                    + "by three. The threshold for this exclusion is L greater than four to the power card J minus one.")),
                Paragraph(Text(
                    "For two representations that agree off those coordinates, subtract the level equations "
                    + "and clear denominators. Reduction modulo two recovers equality of the first digits' "
                    + "remainders modulo two. Reduction modulo three gives the corresponding equality for "
                    + "the second digits. Both quotients have at most two values. Thus the outside digits and "
                    + "the two quotients together encode each level injectively, using at most four to the power "
                    + "card J minus one codes."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula j = F.Id("J");
        Formula levels = F.Id("L");
        Formula w = F.Id("w");
        return Disp(Seq(Forall, Sp, j, Sp, w, Sp, levels, Comma, Sp,
            new Formula.FunctionCall(FormulaIdentifier.Create("FourDigitIntegerCoverage"), [j, w, levels]),
            Sp, Land, Sp, D(4), Caret,
            Grp(new Formula.FunctionCall(FormulaIdentifier.Create("card"), [j]), Sp, Minus, Sp, D(1)),
            Sp, Lt, Sp, levels, Sp, Rightarrow, Sp,
            new Formula.FunctionCall(FormulaIdentifier.Create("NoMixedHalfAndThirdWeights"), [j, w])));
    }
}

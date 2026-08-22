using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Deficit.Cocycles;

internal sealed class AdditiveCarryCocycleIdentityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The kernel-valued carry of an additive section satisfies the cocycle identity.",
        H("Additive Section Carry Identity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("additive-section-carry-satisfies-the-cocycle-identity"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/Cocycles/AdditiveCarryCocycleIdentity."
                        + "additive_section_carry_cocycle_identity"),
                H("An additive section carry satisfies the cocycle identity"),
                StatementSource.FromAuthor(CocycleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let q be an additive homomorphism between commutative additive groups "
                            + "and let s be a right-inverse section of q. The named carry is the "
                            + "existing kernel-valued construction s(a)+s(b)-s(a+b).")),
                    Paragraph(Text(
                        "For every a, b, and c in the quotient carrier, the two bracketings "
                            + "accumulate equal kernel-valued carries."))),
                DescribeRole.Theorem))));

    private static Formula Carry(Formula quotient, Formula section, Formula left, Formula right) =>
        Seq(
            Kappa, Underscore, Grp(quotient, Comma, section),
            Open, left, Comma, Sp, right, Close);

    private static Formula CocycleFormula()
    {
        Formula x = F.Id("X");
        Formula bCarrier = F.Id("B");
        Formula quotient = F.Id("q");
        Formula section = F.Id("s");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula c = F.Id("c");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, x, Comma, Sp, bCarrier, Comma, Sp,
            OpenBracket, Call("AddCommGroup", x), CloseBracket, Comma, Sp,
            OpenBracket, Call("AddCommGroup", bCarrier), CloseBracket, Comma,
            RowBreak, Grp(),
            quotient, Colon, Sp, Call("AddMonoidHom", x, bCarrier), Comma, Sp,
            section, Colon, Sp, bCarrier, Sp, To, Sp, x, Comma,
            RowBreak, Grp(),
            Call("RightInverse", section, quotient), Sp, Rightarrow, Sp,
            Forall, Sp, a, Comma, Sp, b, Comma, Sp, c, InMacro, Sp, bCarrier, Comma,
            RowBreak, Grp(),
            Carry(quotient, section, a, b), Sp, Plus, Sp,
            Carry(quotient, section, Seq(a, Plus, b), c), Sp, Eq,
            RowBreak, Grp(),
            Carry(quotient, section, b, c), Sp, Plus, Sp,
            Carry(quotient, section, a, Seq(b, Plus, c)), Dot,
            End, Grp(F.Id("gathered"))));
    }
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Deficit.Cocycles;

internal sealed class AdditiveCarryCocycleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A section of an additive quotient produces an associative carry defect.",
        H("Additive Section Carry"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("an-additive-section-carry-satisfies-the-cocycle-identity"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/Cocycles/AdditiveCarryCocycle.section_carry_cocycle"),
                H("An additive section carry satisfies the cocycle identity"),
                StatementSource.FromAuthor(Disp(Seq(
                    Kappa, Underscore, Grp(F.Id("s")), Open,
                    F.Id("a"), Comma, F.Id("b"), Close, Sp, Plus, Sp,
                    Kappa, Underscore, Grp(F.Id("s")), Open,
                    F.Id("a"), Plus, F.Id("b"), Comma, F.Id("c"), Close, Sp, Eq, RowBreak,
                    Kappa, Underscore, Grp(F.Id("s")), Open,
                    F.Id("b"), Comma, F.Id("c"), Close, Sp, Plus, Sp,
                    Kappa, Underscore, Grp(F.Id("s")), Open,
                    F.Id("a"), Comma, F.Id("b"), Plus, F.Id("c"), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let q be an additive quotient map and let s be a set-theoretic "
                            + "right-inverse section. The carry is constructed as "
                            + "s(a)+s(b)-s(a+b), and the section law places it in the kernel of q.")),
                    Paragraph(Text(
                        "For all quotient values a, b, and c, the sum of the carries for "
                            + "(a,b) and (a+b,c) equals the sum for (b,c) and (a,b+c). "
                            + "The proof expands the four carries, rewrites by associativity, "
                            + "and cancels the section values."))),
                DescribeRole.Theorem))));
}

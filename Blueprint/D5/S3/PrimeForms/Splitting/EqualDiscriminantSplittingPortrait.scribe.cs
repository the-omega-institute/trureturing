using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms.Splitting;

internal sealed class EqualDiscriminantSplittingPortraitDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/PrimeForms/Splitting/EqualDiscriminantSplittingPortrait."
            + "equal_discriminant_splitting_portrait";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary quadratic forms with equal discriminants have identical splitting symbols "
            + "at every index.",
        H("Equal-Discriminant Splitting Portraits"),
        Blocks(Describe.Lean(
            DescribeId.Create("equal-discriminants-have-equal-splitting-portraits"),
            DeclarationHandle.Create(Declaration),
            H("Equal discriminants have equal splitting portraits"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The form carrier and discriminant are the canonical integer binary "
                        + "quadratic-form objects from the PrimeForms family. No parallel form "
                        + "or discriminant representation is introduced.")),
                Paragraph(Text(
                    "At index p, the splitting readout is constructed by applying the Jacobi "
                        + "symbol to the form's discriminant. At prime p this is the Legendre "
                        + "symbol used by the source splitting observer.")),
                Paragraph(Text(
                    "Equal discriminants remain equal after applying this same readout at every "
                        + "natural index, so the entire splitting portrait is unable to "
                        + "distinguish the two forms."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula first = F.Id("Q");
        Formula second = F.Id("Qprime");
        Formula index = F.Id("p");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula firstDiscriminant = Call("discriminant", first);
        Formula secondDiscriminant = Call("discriminant", second);
        Formula firstSplit = Call("jacobiSym", firstDiscriminant, index);
        Formula secondSplit = Call("jacobiSym", secondDiscriminant, index);

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, first, Comma, Sp, second, Colon, Sp,
                F.Id("BinaryQuadraticForm"), Comma),
            Seq(firstDiscriminant, Sp, Eq, Sp, secondDiscriminant, Sp, Rightarrow),
            Seq(Forall, Sp, index, Sp, InMacro, Sp, naturals, Comma),
            Seq(firstSplit, Sp, Eq, Sp, secondSplit, Dot),
        ]));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var content = new List<Formula>
        {
            Operatorname, Grp(F.Id(name)), Open
        };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[index]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }
}

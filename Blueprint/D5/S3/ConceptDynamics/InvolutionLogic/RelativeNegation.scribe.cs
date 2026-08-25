using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InvolutionLogic;

internal sealed class RelativeNegationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InvolutionLogic/RelativeNegation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a proposition inside the old ambient, negation grows by the admitted region.",
        H("Relative Negation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("relative-complement-expands-by-the-new-region"),
                DeclarationHandle.Create(Prefix + "relative_complement_expansion"),
                H("An enlarged relative complement splits into old and new parts"),
                StatementSource.FromAuthor(ExpansionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume the proposition lies in the old universe and the old "
                            + "universe lies in the new one.")),
                    Paragraph(Text(
                        "Removing the proposition from the enlarged universe leaves the old "
                            + "relative complement together with the points newly admitted by "
                            + "the universe expansion.")),
                    Paragraph(Text(
                        "The equality is conditional on both displayed inclusions; without "
                            + "them the decomposition is not asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("new-relative-complement-part-is-universe-difference"),
                DeclarationHandle.Create(Prefix + "relative_complement_new_region"),
                H("The newly available negative region is exactly the universe difference"),
                StatementSource.FromAuthor(NewRegionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Under the same two inclusions, subtracting the old relative "
                            + "complement from the new one removes every previously available "
                            + "negative point.")),
                    Paragraph(Text(
                        "What remains is precisely the set difference between the new and old "
                            + "universes, with no additional proposition-dependent region."))),
                DescribeRole.Theorem))));

    private static Formula Bindings(
        Formula carrier,
        Formula proposition,
        Formula oldUniverse,
        Formula newUniverse) =>
        Seq(
            Forall, Sp, proposition, Comma, Sp, oldUniverse, Comma, Sp, newUniverse,
            Colon, Sp, Call("Set", carrier), Comma, Sp);

    private static Formula Hypotheses(
        Formula proposition,
        Formula oldUniverse,
        Formula newUniverse) =>
        Seq(
            proposition, Sp, Subseteq, Sp, oldUniverse, Sp, Land, Sp,
            oldUniverse, Sp, Subseteq, Sp, newUniverse);

    private static Formula ExpansionFormula()
    {
        Formula carrier = F.Id("X");
        Formula proposition = F.Id("P");
        Formula oldUniverse = F.Id("U0");
        Formula newUniverse = F.Id("U1");

        return Disp(Seq(
            Bindings(carrier, proposition, oldUniverse, newUniverse),
            Open, Hypotheses(proposition, oldUniverse, newUniverse), Close,
            Sp, Rightarrow, Sp,
            Call("relativeNegation", newUniverse, proposition), Sp, Eq, Sp,
            Call("union",
                Call("relativeNegation", oldUniverse, proposition),
                Seq(newUniverse, Sp, Setminus, Sp, oldUniverse)),
            Dot));
    }

    private static Formula NewRegionFormula()
    {
        Formula carrier = F.Id("X");
        Formula proposition = F.Id("P");
        Formula oldUniverse = F.Id("U0");
        Formula newUniverse = F.Id("U1");

        return Disp(Seq(
            Bindings(carrier, proposition, oldUniverse, newUniverse),
            Open, Hypotheses(proposition, oldUniverse, newUniverse), Close,
            Sp, Rightarrow, Sp,
            Call("relativeNegation", newUniverse, proposition),
            Sp, Setminus, Sp,
            Call("relativeNegation", oldUniverse, proposition),
            Sp, Eq, Sp, newUniverse, Sp, Setminus, Sp, oldUniverse, Dot));
    }
}

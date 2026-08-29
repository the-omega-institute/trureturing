using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Postprocessing;

internal sealed class PostprocessingStrictLossWitnessDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/Postprocessing/PostprocessingStrictLossWitness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A collapsed distinction witnesses strict information loss under postprocessing.",
        H("Postprocessing Strict Loss Witness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a-collapsed-distinction-witnesses-strict-loss"),
                DeclarationHandle.Create(
                    Prefix + "collapsed_distinction_witnesses_strict_loss"),
                H("A collapsed distinction witnesses strict loss"),
                StatementSource.FromAuthor(WitnessStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume q separates x and y while p identifies their q-values.")),
                    Paragraph(Text(
                        "The pair is therefore in the processed kernel and is not in the "
                            + "original kernel, recording both sides of the witness."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("strict-loss-refutes-postprocessing-injectivity"),
                DeclarationHandle.Create(Prefix + "strict_loss_refutes_image_injectivity"),
                H("Strict loss refutes postprocessing injectivity"),
                StatementSource.FromAuthor(InjectivityStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The same separated-and-collapsed pair contradicts injectivity of the "
                            + "postprocessing map p.")),
                    Paragraph(Text(
                        "The conclusion is failure of global injectivity of p; it follows from "
                            + "the displayed pair in the image of q."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula PrefixFormula(Formula conclusion)
    {
        Formula q = F.Id("q");
        Formula p = F.Id("p");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula antecedent = Seq(
            Call("q", x), Sp, Neq, Sp, Call("q", y), Sp, Land, Sp,
            Call("p", Call("q", x)), Sp, Eq, Sp, Call("p", Call("q", y)));
        return Disp(Seq(
            Forall, Sp, q, Colon, Sp, Arrow(F.Id("X"), F.Id("Y")), Comma, Sp,
            p, Colon, Sp, Arrow(F.Id("Y"), F.Id("Z")), Comma, Sp,
            x, Comma, Sp, y, Colon, Sp, F.Id("X"), Comma, RowBreak, Grp(),
            Open, antecedent, Close, Sp, Rightarrow, Sp, conclusion, Dot));
    }

    private static Formula WitnessStatement()
    {
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula consequence = Seq(
            Call("Kernel", Seq(F.Id("p"), Sp, Circ, Sp, F.Id("q")), x, y),
            Sp, Land, Sp, Neg, Call("Kernel", F.Id("q"), x, y));
        return PrefixFormula(Seq(Open, consequence, Close));
    }

    private static Formula InjectivityStatement() =>
        PrefixFormula(Seq(Neg, Call("Injective", F.Id("p"))));
}

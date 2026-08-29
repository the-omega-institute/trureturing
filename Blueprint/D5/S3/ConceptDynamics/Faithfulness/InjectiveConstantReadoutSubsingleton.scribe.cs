using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Faithfulness;

internal sealed class InjectiveConstantReadoutSubsingletonDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/Faithfulness/InjectiveConstantReadoutSubsingleton.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An injective constant readout has a subsingleton source.",
        H("Injective Constant Readout Subsingleton"),
        Blocks(Describe.Lean(
            DescribeId.Create("injective-constant-readout-forces-subsingleton-source"),
            DeclarationHandle.Create(Prefix + "injective_constant_readout_subsingleton"),
            H("An injective constant readout forces a subsingleton source"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let q be a readout from X to Y that is both injective and constant on "
                        + "every pair of source states.")),
                Paragraph(Text(
                    "Constancy equates the readouts of any two states, and injectivity "
                        + "reflects that equality back to the states themselves.")),
                Paragraph(Text(
                    "Thus X has at most one element. No inhabitedness or finiteness of X "
                        + "is assumed."))),
            DescribeRole.Theorem))));

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula Statement()
    {
        Formula q = F.Id("q");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula antecedent = Seq(
            Call("Injective", q), Sp, Land, Sp,
            Open, Forall, Sp, x, Comma, Sp, y, Colon, Sp, F.Id("X"), Comma, Sp,
            Call("q", x), Sp, Eq, Sp, Call("q", y), Close);
        return Disp(Seq(
            Forall, Sp, q, Colon, Sp, Arrow(F.Id("X"), F.Id("Y")), Comma, Sp,
            Open, antecedent, Close, Sp, Rightarrow, Sp,
            Call("Subsingleton", F.Id("X")), Dot));
    }
}

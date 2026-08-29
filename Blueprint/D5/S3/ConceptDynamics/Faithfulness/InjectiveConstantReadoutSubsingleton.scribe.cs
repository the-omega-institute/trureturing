using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Faithfulness;

internal sealed class InjectiveConstantReadoutSubsingletonDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Faithfulness/InjectiveConstantReadoutSubsingleton."
            + "injective_constant_readout_subsingleton";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An injective constant readout has a subsingleton source.",
        H("Injective Constant Readout Subsingleton"),
        Blocks(Describe.Lean(
            DescribeId.Create("injective-constant-readout-forces-subsingleton-source"),
            DeclarationHandle.Create(Declaration),
            H("An injective constant readout forces a subsingleton source"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The source statement assumes one ordinary readout that identifies no "
                        + "distinct states and nevertheless returns the same value on every "
                        + "pair of source states.")),
                Paragraph(Text(
                    "Constancy gives equal readout values for arbitrary source states. "
                        + "Injectivity reflects that equality back to equality of the states, "
                        + "which is exactly the Subsingleton conclusion.")),
                Paragraph(Text(
                    "The theorem permits an empty source and is witnessed by the identity "
                        + "readout on the one-point type. It makes no claim about jointly "
                        + "faithful families or relational observers."))),
            DescribeRole.Theorem))));

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula TheoremFormula()
    {
        Formula source = F.Id("X");
        Formula output = F.Id("Y");
        Formula readout = F.Id("q");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula constant = Seq(
            Forall, Sp, Typed(Seq(left, Comma, Sp, right), source), Comma, Sp,
            Call("q", left), Sp, Eq, Sp, Call("q", right));
        Formula conclusion = Seq(
            Call("Injective", readout), Sp, Land, Sp,
            Open, constant, Close, Sp, Rightarrow, Sp,
            Call("Subsingleton", source));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(Seq(source, Comma, Sp, output), TypeUniverse()),
            Comma, RowBreak, Grp(),
            Typed(readout, Seq(source, Sp, To, Sp, output)),
            Comma, RowBreak, Grp(),
            Open, conclusion, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class RarePriorReferenceScalarDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorReferenceScalar.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "RarePriorReferenceScalar", H("RarePriorReferenceScalar"), Blocks(
            Paragraph(Text("The PH14 rational expressions e and f use the supplied exact constants. The PH17 polynomial isolates their unique nonnegative common root between 0.2333613 and 0.2333615. The scalar is e at that root. The statement proves the needed strict bound and makes no minimax or irrationality claim.")),
            Node("exact-reference-scalar", "exact_reference_scalar", "exact reference scalar"))));

    private static DocumentBlock.Describe Node(string id, string name, string title) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(Statement(name))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The statement retains the complete original telescope and conditions."))), DescribeRole.Theorem);

    private static Formula Statement(string name) => name switch
    {
        "exact_reference_scalar" => Seq(Name("lower"), Sp, Lt, Sp, Name("aStar"), Sp, Land, Sp, Name("aStar"), Sp, Lt, Sp, Name("upper"), Sp, Land, Sp, Name("rootPolynomial"), Sp, Name("aStar"), Sp, Eq, Sp, D(0), Sp, Land, Sp, Open, Sp, Forall, Sp, Name("a"), Sp, Colon, Sp, Name("Real"), Sp, Comma, Sp, D(0), Sp, Leq, Sp, Name("a"), Sp, Rightarrow, Sp, Name("rootPolynomial"), Sp, Name("a"), Sp, Eq, Sp, D(0), Sp, Rightarrow, Sp, Name("a"), Sp, Eq, Sp, Name("aStar"), Sp, Close, Sp, Land, Sp, Name("e"), Sp, Name("aStar"), Sp, Eq, Sp, Name("f"), Sp, Name("aStar"), Sp, Land, Sp, D(0), Sp, Lt, Sp, Name("tStar"), Sp, Land, Sp, Name("tStar"), Sp, Lt, Sp, D(1), Sp, Slash, Sp, D(1,0,0,0,0)),
        _ => Name("Unknown")
    };
    private static Formula Name(string value) => Seq(Operatorname, Grp(F.Id(value)));
    private static Formula Seq(params Formula[] items) => F.Seq(items);
}

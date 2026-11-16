using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;

internal sealed class ZverykIdealRigidityRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/VertexAlgebra/Sectors/ZverykIdealRigidityRefutation";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/VertexAlgebra/zveryk2026virasoroextensions");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Virasoro and Borcherds presentation, action, and ideal structure.",
        H("ZverykIdealRigidityRefutation"), Blocks(
        Describe.Lean(DescribeId.Create("zv-result"),
            DeclarationHandle.Create(Module + ".result"), H("result"),
            StatementSource.FromAuthor(Disp(Seq(Neg, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(F.Id("I"), Sp, F.Id("J"), Sp, F.Id("H"), Sp, F.Id("V"), Sp, Colon, Sp, Q("Type"))), Sp, Seq(OpenBracket, Seq(Q("AddCommGroup"), Sp, F.Id("H")), CloseBracket), Sp, Seq(OpenBracket, Seq(Q("Module"), Sp, Complex, Sp, F.Id("H")), CloseBracket), Sp, Seq(OpenBracket, Seq(Q("AddCommGroup"), Sp, F.Id("V")), CloseBracket), Sp, Seq(OpenBracket, Seq(Q("Module"), Sp, Complex, Sp, F.Id("V")), CloseBracket), Sp, Parenthesized(Seq(F.Id("F"), Sp, Colon, Sp, Q("EnhancedCartanData"), Sp, F.Id("I"), Sp, F.Id("J"), Sp, F.Id("H"), Sp, F.Id("V"))), Comma, Sp, Q("F","IsEnhanced"), Sp, To, Sp, Q("F","Symmetrizable"), Sp, To, Sp, Forall, Sp, F.Id("s"), Sp, F.Id("t"), Sp, Colon, Sp, Complex, Sp, Comma, Sp, Parenthesized(Seq(F.Id("s"), Sp, Neq, Sp, D(0), Sp, Lor, Sp, F.Id("t"), Sp, Neq, Sp, D(0))), Sp, To, Sp, Parenthesized(Seq(Q("if"), Sp, F.Id("s"), Sp, Eq, Sp, D(0), Sp, Q("then"), Sp, Parenthesized(Q("F","heisenberg")), Dot, Q("IdealRigidity"), Sp, Q("else"), Sp, Parenthesized(Seq(Q("F","deform"), Sp, F.Id("s"), Sp, F.Id("t"))), Dot, Q("Condition43"), Sp, To, Sp, Parenthesized(Seq(Q("F","deform"), Sp, F.Id("s"), Sp, F.Id("t"))), Dot, Q("IdealRigidity")))))))),
            AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text("The rational rank-two datum satisfies (4.3). Its level-four Virasoro singular vector survives the presentation and generates a nonzero ideal disjoint from Cartan. The local relations vanish for this datum."))), DescribeRole.Theorem,
            new OpenProblemResolutionClaim(ProblemSlugRef.Create("op-zveryk2609c48"),
                ResolutionKind.Refuted)))));

    private static Formula Q(params string[] names) => Seq([.. names.SelectMany(
        (name, index) => index == 0
            ? new Formula[] { Operatorname, Grp(F.Id(name)) }
            : [Dot, Operatorname, Grp(F.Id(name))])]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Complex => Seq(Mathbb, Grp(F.Id("C")));
}

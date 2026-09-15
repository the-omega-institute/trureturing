using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class IterateProductFourFiveFifthModEightDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/hanna2026a396798");
    private static readonly DeclarationHandle SourceSeries = DeclarationHandle.Create(
        "D5/S1/Recurrence/Residue/IterateProductFourFiveEighthModEight.generatingSeries");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The fifth compositional iterate of A396798 has coefficient period 5,1,1,5 modulo eight from degree two.",
        H("The Fifth Compositional Iterate Modulo Eight"),
        Blocks(
            Paragraph(Text("Let A denote "), Ref(SourceSeries.Value),
                Text(", the unique integer ordinary formal power series with zero constant "
                    + "coefficient satisfying A=X+I4(A)*I5(A). Write I0(F)=X and "
                    + "I(k+1)(F)=Ik(F) composed with F. The product is ordinary "
                    + "series multiplication, with no factorial scaling.")),
            Describe.Lean(DescribeId.Create("a396798-fifth-iterate-result"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/Residue/IterateProductFourFiveFifthModEight.result"),
                H("Hanna's fifth conjecture"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Reduce A modulo eight to F, and write P=I4(F) "
                    + "and J=I5(F). The fourth and eighth iterate identities give "
                    + "P=X+4X^2 and I8(F)=X. Substituting P into F=X+PJ gives "
                    + "J=P+XF. Elimination yields "
                    + "(J-X)(1-X^4)=5X^2+X^3+X^4+5X^5. The geometric inverse "
                    + "of 1-X^4 has coefficient one at multiples of four and zero "
                    + "elsewhere, so the stated period starts at degree two."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a396798-fifth-iterate-mod-eight"),
                    ResolutionKind.Proved)))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Statement()
    {
        Formula n = F.Id("n");
        Formula residue = Call("mod", Parenthesized(Seq(n, Sp, Minus, Sp, D(2))), D(4));
        Formula condition = Seq(residue, Sp, Eq, Sp, D(0), Sp, Lor, Sp,
            residue, Sp, Eq, Sp, D(3));
        Formula expected = Seq(Named("if"), Sp, Parenthesized(condition), Sp,
            Named("then"), Sp, D(5), Sp, Named("else"), Sp, D(1));
        return Disp(Seq(Forall, Sp, n, Colon, Mathbb, Grp(F.Id("N")), Comma, Sp,
            D(1), Lt, n, Implies, Sp, D(8), Sp, Mid, Sp,
            Parenthesized(Seq(Call("coeff", n, Call("iterate", F.Id("A"), D(5))),
                Sp, Minus, Sp, Parenthesized(expected)))));
    }
}

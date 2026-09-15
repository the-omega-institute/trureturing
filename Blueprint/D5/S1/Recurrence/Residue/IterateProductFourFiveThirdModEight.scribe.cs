using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class IterateProductFourFiveThirdModEightDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/hanna2026a396798");
    private static readonly DeclarationHandle SourceSeries = DeclarationHandle.Create(
        "D5/S1/Recurrence/Residue/IterateProductFourFiveEighthModEight.generatingSeries");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The third compositional iterate of A396798 has coefficient period 3,1,7,5 modulo eight from degree two.",
        H("The Third Compositional Iterate Modulo Eight"),
        Blocks(
            Paragraph(Text("Let A denote "), Ref(SourceSeries.Value),
                Text(", the unique integer ordinary formal power series with zero constant "
                    + "coefficient satisfying A=X+I4(A)*I5(A). Write I0(F)=X and "
                    + "I(k+1)(F)=Ik(F) composed with F. The product is ordinary "
                    + "series multiplication, with no factorial scaling.")),
            Describe.Lean(DescribeId.Create("a396798-third-iterate-result"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/Residue/IterateProductFourFiveThirdModEight.result"),
                H("Hanna's third conjecture"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Reduce A modulo eight to F, and let J=I5(F). "
                    + "The fifth coefficient identity gives the rational form of J. "
                    + "Clearing unit denominators identifies its compositional "
                    + "inverse K=X+X^2*(3+X+7*X^2+5*X^3)/(1-X^4). "
                    + "The eighth identity I8(F)=X identifies I3(F) with K. "
                    + "The geometric inverse of 1-X^4 then gives the period "
                    + "3,1,7,5 from degree two."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a396798-third-iterate-mod-eight"),
                    ResolutionKind.Proved)))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Statement()
    {
        Formula n = F.Id("n");
        Formula residue = Call("mod", Parenthesized(Seq(n, Sp, Minus, Sp, D(2))), D(4));
        Formula expected = Seq(Named("if"), Sp, residue, Sp, Eq, Sp, D(0), Sp,
            Named("then"), Sp, D(3), Sp, Named("else"), Sp,
            Named("if"), Sp, residue, Sp, Eq, Sp, D(1), Sp,
            Named("then"), Sp, D(1), Sp, Named("else"), Sp,
            Named("if"), Sp, residue, Sp, Eq, Sp, D(2), Sp,
            Named("then"), Sp, D(7), Sp, Named("else"), Sp, D(5));
        return Disp(Seq(Forall, Sp, n, Colon, Mathbb, Grp(F.Id("N")), Comma, Sp,
            D(1), Lt, n, Implies, Sp, D(8), Sp, Mid, Sp,
            Parenthesized(Seq(Call("coeff", n, Call("iterate", F.Id("A"), D(3))),
                Sp, Minus, Sp, Parenthesized(expected)))));
    }
}

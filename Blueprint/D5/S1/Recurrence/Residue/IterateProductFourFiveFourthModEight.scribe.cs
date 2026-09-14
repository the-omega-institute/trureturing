using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class IterateProductFourFiveFourthModEightDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/hanna2026a396798");
    private static readonly DeclarationHandle SourceSeries = DeclarationHandle.Create(
        "D5/S1/Recurrence/Residue/IterateProductFourFiveEighthModEight.generatingSeries");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every coefficient above degree two in the fourth compositional iterate of A396798 is divisible by eight.",
        H("The Fourth Compositional Iterate Modulo Eight"),
        Blocks(
            Paragraph(Text("Let A denote "), Ref(SourceSeries.Value),
                Text(", the unique integer ordinary formal power series with zero constant "
                    + "coefficient satisfying A=X+I4(A)*I5(A). Write I0(F)=X and "
                    + "I(k+1)(F)=Ik(F) composed with F. The product is ordinary "
                    + "series multiplication, and the coefficients have no factorial scaling.")),
            Describe.Lean(DescribeId.Create("a396798-fourth-iterate-result"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/Residue/IterateProductFourFiveFourthModEight.result"),
                H("Hanna's fourth conjecture"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), Colon, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    D(2), Lt, F.Id("n"), Implies, Sp, D(8), Sp, Mid, Sp,
                    new Formula.Apply(Seq(Operatorname, Grp(F.Id("coeff"))),
                    [
                        F.Id("n"),
                        new Formula.Apply(Seq(Operatorname, Grp(F.Id("iterate"))),
                            [F.Id("A"), D(4)])
                    ])))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Modulo four, source uniqueness identifies A "
                    + "with X/(1-X), so its second iterate equals X+2X^2. An exact "
                    + "integer quotient gives G=X+2X^2+4B for the second iterate "
                    + "modulo eight. Its zero constant coefficient makes "
                    + "substitution legitimate. The relations 4(G-X)=0 and "
                    + "4((B composed with G)-B)=0, together with 2G^2=2X^2, yield "
                    + "G composed with G=X+4X^2. Thus every coefficient of the "
                    + "fourth iterate above degree two vanishes modulo eight."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a396798-fourth-iterate-mod-eight"),
                    ResolutionKind.Proved)))));
}

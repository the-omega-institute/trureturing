using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class IterateProductFourFiveSeventhModEightDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/hanna2026a396798");
    private static readonly DeclarationHandle SourceSeries = DeclarationHandle.Create(
        "D5/S1/Recurrence/Residue/IterateProductFourFiveEighthModEight.generatingSeries");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The seventh compositional iterate of A396798 has coefficient period 7,1,3,5 modulo eight from degree two.",
        H("The Seventh Compositional Iterate Modulo Eight"),
        Blocks(
            Paragraph(Text("Let A denote "), Ref(SourceSeries.Value),
                Text(", the unique integer ordinary formal power series with zero constant "
                    + "coefficient satisfying A=X+I4(A)*I5(A). Write I0(F)=X and "
                    + "I(k+1)(F)=Ik(F) composed with F. The product is ordinary "
                    + "series multiplication, with no factorial scaling.")),
            Describe.Lean(DescribeId.Create("a396798-seventh-iterate-result"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/Residue/IterateProductFourFiveSeventhModEight.result"),
                H("Hanna's seventh conjecture"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Reduce A modulo eight to F, and set U=I3(F). "
                    + "The source definition gives coeff0(F)=0 and coeff1(F)=1. "
                    + "The existing iterate_top theorem, comparing F with X "
                    + "at degree two, gives coeff2(Ij(F))=j*coeff2(F). "
                    + "The public third result at n=2 gives 3*coeff2(F)=3; "
                    + "since 3*3=1 modulo eight, coeff2(F)=1. "
                    + "These low coefficients and the public fourth tail give "
                    + "I4(F)=X+4X^2. Iteration addition and substitution into "
                    + "U give I7(F)=U+4U^2. The zero constant and unit linear "
                    + "coefficients of U, together with the third period, give "
                    + "4*coeff m(U)=4 for every m>0. The convolution endpoints "
                    + "vanish, and its n-1 positive-index pairs each contribute "
                    + "four, so 4*coeff n(U^2)=4*(n-1) for n>1. "
                    + "The four cases of (n-2)%4 give 7,1,3,5; compatibility "
                    + "of coefficient reduction with iteration transfers this "
                    + "identity to integer divisibility."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a396798-seventh-iterate-mod-eight"),
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
            Named("then"), Sp, D(7), Sp, Named("else"), Sp,
            Named("if"), Sp, residue, Sp, Eq, Sp, D(1), Sp,
            Named("then"), Sp, D(1), Sp, Named("else"), Sp,
            Named("if"), Sp, residue, Sp, Eq, Sp, D(2), Sp,
            Named("then"), Sp, D(3), Sp, Named("else"), Sp, D(5));
        return Disp(Seq(Forall, Sp, n, Colon, Mathbb, Grp(F.Id("N")), Comma, Sp,
            D(1), Lt, n, Implies, Sp, D(8), Sp, Mid, Sp,
            Parenthesized(Seq(Call("coeff", n, Call("iterate", F.Id("A"), D(7))),
                Sp, Minus, Sp, Parenthesized(expected)))));
    }
}

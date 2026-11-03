using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms.SternBrocot;

internal sealed class UnimodularGenerationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All natural determinant-one matrices are finite left-right words.",
        H("Natural unimodular matrix generation"),
        Blocks(
            Paragraph(Text("PositiveMatrix is the existing carrier of four natural entries a,b,c,d arranged as [[a,b],[c,d]]; zero entries are allowed. Unimodular(A) means a d=b c+1. The existing factors L=[[1,0],[1,1]] and U=[[1,1],[0,1]] act by left multiplication. For a Boolean word w, wordMatrix([])=I, wordMatrix(false::w)=L wordMatrix(w), and wordMatrix(true::w)=U wordMatrix(w). Thus this list records matrix factors with its head on the left; it is distinct from chronological action order.")),
            Describe.Lean(DescribeId.Create("natural-unimodular-generation"),
                DeclarationHandle.Create("D5/S3/PrimeForms/SternBrocot/UnimodularGeneration.unimodular_iff_wordMatrix"),
                H("Exact generation of determinant-one natural matrices"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/PrimeForms/axiom2026unimodulardescent")),
                Blocks(
                    Paragraph(Text("The quantifier ranges over every natural matrix, with no bound on entries or length and no strict positivity assumption. A word always has determinant one by the existing multiplication theorem.")),
                    Paragraph(Text("For the converse, orient the two rows as p=(c,d) and p'=(a,b). The unimodular-pair equation is p'₁p₂=p₁p'₂+1. Except at p=(0,1), p'=(1,0), the pair has an additive unimodular parent. If p=q+p', reversing the subtraction is multiplication by L; if p'=p+q, it is multiplication by U. The subtracted row is nonzero, so the sum a+b+c+d strictly decreases. Strong induction constructs the entire finite word, terminating at I. The additive-parent arithmetic is Kenny Lau's HJO descent; the finite matrix-word construction and its connection to the existing wordMatrix use that descent.")),
                    Paragraph(Text("Replacing L by chronological J,M and U by chronological M,J connects this determinant-one description to native forward histories. A row exchange accounts for determinant minus one. The cumulative continuation and prefix normal-form conclusions require their own additional arguments."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, Formula x) =>
        Seq(Operatorname, Grp(F.Id(name)), Open, x, Close);
    private static Formula Statement()
    {
        var a = F.Id("A");
        var w = F.Id("w");
        return Disp(Seq(Forall, Sp, a, InMacro, Sp, Operatorname, Grp(F.Id("PositiveMatrix")),
            Comma, Sp, Call("Unimodular", a), Iff, Sp,
            Exists, Sp, w, InMacro, Sp, OpenBrace, D(0), Comma, D(1), CloseBrace,
            Caret, Grp(Star), Comma, Sp, Call("wordMatrix", w), Eq, Sp, a));
    }
}

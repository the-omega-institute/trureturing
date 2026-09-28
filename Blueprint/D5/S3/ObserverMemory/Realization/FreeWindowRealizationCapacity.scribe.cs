using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Realization;

internal sealed class FreeWindowRealizationCapacityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The realized finite words determine the exact total state capacity.",
        H("Free Window Realization Capacity"),
        Blocks(
            Paragraph(Text("Let S be a finite set, A any output alphabet, D:S -> S a total update, q:S -> A a readout, and n a natural number. Define w_n(s)=(q(D^j(s))) for 0 <= j <= n, W_n=range(w_n), and I_n(s)=w_n(s), with codomain W_n. A word state w has readout g_n(w)=w(0). Empty S and n=0 are included.")),
            Paragraph(Text("For an arbitrary finite total carrier M, WindowCorrect(D,q,n,I,F,g) means g(F^j(I(s)))=q(D^j(s)) for every source s and 0 <= j <= n. The fixed update F and readout g act on all of M. The initial preparation I need not be surjective and need not commute with D and F; unused states count toward the capacity.")),
            Describe.Lean(
                DescribeId.Create("free-window-realization-capacity"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/Realization/FreeWindowRealizationCapacity.free_window_realization_capacity"),
                H("Exact capacity with arbitrary representative successors"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a representative map r:W_n -> S satisfying I_n(r(w))=w, define U_r(w)=I_n(D(r(w))). The theorem asserts the lower bound for every finite realization, finiteness of W_n, surjectivity of I_n, existence of a representative map, and correctness of U_r for every such choice. Its carrier is exactly W_n, so this realizes the minimum total number |W_n| of states.")),
                    Paragraph(Text("More precisely, for every word state w and every natural time t, the length n+1 output word from U_r^t(w) equals the label U_r^t(w). Thus every later output window remains in W_n. This does not require it to match the later window of the source originally used to prepare w.")),
                    Paragraph(Text("For the lower bound, choose one source for each realized word. Two equal prepared states would give equal outputs at every required time, hence the same word. The resulting injection from W_n into M gives |W_n| <= |M|.")),
                    Paragraph(Text("For attainment, adjacent labels satisfy (U_r(w))(k)=w(k+1) whenever k<n. Induction on j gives (U_r^j(w))(k)=w(k+j) whenever k+j<=n. Taking k=0 identifies the output window with the word label. Applying the same identity to every later state proves the assertion at all starting times."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var d = F.Id("D"); var q = F.Id("q"); var n = F.Id("n");
        var m = F.Id("M"); var i = F.Id("I"); var f = F.Id("F"); var g = F.Id("g");
        var r = F.Id("r"); var w = F.Id("w"); var t = F.Id("t");
        var wn = new Formula.Subscript(F.Id("W"), n); var ini = new Formula.Subscript(F.Id("I"), n);
        var gn = new Formula.Subscript(F.Id("g"), n); var ur = new Formula.Subscript(F.Id("U"), r);
        var after = Call(new Formula.Power(ur, t), w);
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, F.Id("S"), Sp, TextToken("finite"), Comma, Sp,
            F.Id("A"), Comma, Sp, d, Colon, F.Id("S"), To, Sp, F.Id("S"), Comma, Sp,
            q, Colon, F.Id("S"), To, Sp, F.Id("A"), Comma, Sp,
            n, InMacro, Seq(Mathbb, Grp(F.Id("N"))), Colon, RowBreak,
            Open, Forall, Sp, m, Sp, TextToken("finite"), Comma, Sp, i, Comma, f, Comma, g,
            Comma, Sp, Correct(d, q, n, i, f, g), Rightarrow,
            Card(wn), Leq, Card(m), Close, Land, RowBreak,
            Call(F.Id("Finite"), wn), Land, Sp, Call(F.Id("Surjective"), ini), Land,
            Open, Exists, Sp, r, Colon, wn, To, Sp, F.Id("S"), Comma, Sp,
            Call(F.Id("RightInverse"), r, ini), Close, Land, RowBreak,
            Forall, Sp, r, Colon, wn, To, Sp, F.Id("S"), Comma, Sp,
            Call(F.Id("RightInverse"), r, ini), Rightarrow,
            Open, Correct(d, q, n, ini, ur, gn), Land, RowBreak,
            Forall, Sp, w, InMacro, Sp, wn, Comma, Sp, t, InMacro, Seq(Mathbb, Grp(F.Id("N"))),
            Comma, Sp, Call(F.Id("futureReadoutWord"), ur, gn, n, after), Eq, after, Close,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Correct(params Formula[] args) => Call(F.Id("WindowCorrect"), args);
    private static Formula Card(Formula x) => Seq(Lvert, Sp, x, Sp, Rvert);
    private static Formula TextToken(string s) => Seq(F.Text, Grp(F.Id(s)));
    private static Formula Call(Formula name, params Formula[] args) => new Formula.Apply(name, [.. args]);
}

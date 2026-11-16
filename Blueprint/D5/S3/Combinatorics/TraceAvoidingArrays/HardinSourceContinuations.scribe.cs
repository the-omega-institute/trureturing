using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinSourceContinuationsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/HardinSourceContinuations.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Automata/hardin2013a233170");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The source four-class matrix counts actual literal continuations at every length.",
        H("Completed rows and first appearances"),
        Blocks(
            Paragraph(Text("The boundary p is a proper four-letter word on Fin 3. The scanner state s records whether colours 1 and 2 have appeared. A completed admissible row has seen 1; if 2 is unseen, every boundary label differs from 2. The same literal good and finish scanner as the existing strip definitions determines which actual next rows are allowed.")),
            Def("admissible", "admissible", "Actual admissible boundaries", "The predicate is s.first=true, horizontal properness of p, and exclusion of pair two when s.second=false. It includes all such boundaries, with no height bound."),
            Def("class", "sourceClass", "The four source classes", "Classes 0,1,2,3 are U,A,B,C. U means colour 2 is unseen. Otherwise A has p0=p2 and p1=p3, B has p0=p3, and C contains the remaining two proper equality patterns. In three labels these are exactly abab, abca, and abac or abcb."),
            Def("matrix", "M", "Literal next-row counts", "With row and column order U,A,B,C the matrix is ((16,16,8,32),(0,48,16,64),(0,16,16,32),(0,32,16,48)). Each entry counts actual Fin 6 next rows satisfying horizontal properness, both diagonals, and the current first-appearance scanner. The class count and preservation of admissibility are verified for every boundary and every actual next row."),
            Def("initial", "r", "The actual first rows", "The initial vector is (4,0,2,4). Its ten rows are U:0101,0104,0151,0154; B:0120,0125; C:0102,0121,0124,0152. There is no A first row."),
            Def("continuation", "sourceV", "The source vector recurrence", "For every class i, sourceV(0,i)=1 and sourceV(m+1,i)=sum over j of M(i,j)sourceV(m,j). The theorem identifies this recurrence with the existing literal row-continuation count for all admissible scanner states and boundaries."),
            Describe.Lean(DescribeId.Create("four-class-certificate"),
                DeclarationHandle.Create(Prefix + "four_class_certificate"),
                H("Exact admissible four-class transfer certificate"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The certificate proves admissible successors and initial states, every actual six-colour transition count M, and the normalized initial distribution r. At saturated Seen flags, scanner_fibres pushes the transition projection to sixteen times the proper three-colour successor count. The exact budget and class adapter followed by integer division supplies the proper diagonal sectors of the width-four defect strips. Their raw initial distributions are separate."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "four_class_result"),
                H("Universal literal interpretation of M and r"), StatementSource.FromAuthor(Disp(ResultFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The first equality holds for every continuation length m, scanner state s and admissible boundary p. Here widthV uses rowOK(c)=proper(beta composed with c), pairs(c)=beta composed with c, and nextOK(p,c)=the two diagonal inequalities at all three adjacent positions. The proof decomposes by the unique next literal row, uses the exact class counts, and inducts on m. The second equality reads the actual (m+1)-by-4 rectangular literal strip through the existing width_counting_bridge and the exact first-row vector. It asserts an interpretation of every source class and continuation, independently of the existing terminal generating-function theorem. The construction neither divides by a group order nor replaces actual arrays by a finite-height sample."))), DescribeRole.Theorem))));

    private static DocumentBlock Def(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(
        Seq(name.Split('.').SelectMany((part, k) => k == 0
            ? new[] { Seq(Operatorname, Grp(F.Id(part))) }
            : new[] { Dot, Seq(Operatorname, Grp(F.Id(part))) }).ToArray()), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula ResultFormula()
    {
        var m = F.Id("m"); var s = F.Id("s"); var p = F.Id("p"); var j = F.Id("j");
        var state = All("s", Call("Seen"), All("p", Seq(Call("Fin", D(4)), Sp, To, Sp, Call("Fin", D(3))),
            Seq(Call("admissible", s, p), Sp, Implies, Sp,
                Call("widthV", Call("rowOK"), Call("pairs"), Call("nextOK"), m, s, p), Sp, F.Eq, Sp,
                Call("sourceV", m, Call("sourceClass", s, p)))));
        var total = Seq(Call("Nat.card", Call("HardinThinGraphTransport.literalStrip", Call("true"), m, D(3))),
            Sp, F.Eq, Sp, F.Sum, Underscore, Grp(j, Colon, Sp, Call("Fin", D(4))), Sp,
            new Formula.Binary(Call("r", j), FormulaBinaryOperator.Multiply, Call("sourceV", m, j)));
        return All("m", Call("Nat"), Seq(Open, state, Close, Sp, Land, Sp, total));
    }
}

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
            Describe.Lean(DescribeId.Create("decidable-admissible"), DeclarationHandle.Create(Prefix + "instDecidableAdmissible"),
                H("Decision for all admissible boundaries"), StatementSource.FromAuthor(Disp(DecidableAdmissibleFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The instance uses inferInstanceAs to decide the conjunction s.first=true, proper p, and the implication from s.second=false to exclusion of pair two at every Fin 4 position."))), DescribeRole.Definition),
            Def("class", "sourceClass", "The four source classes", "Classes 0,1,2,3 are U,A,B,C. U means colour 2 is unseen. Otherwise A has p0=p2 and p1=p3, B has p0=p3, and C contains the remaining two proper equality patterns. In three labels these are exactly abab, abca, and abac or abcb."),
            Def("matrix", "M", "Literal next-row counts", "With row and column order U,A,B,C the matrix is ((16,16,8,32),(0,48,16,64),(0,16,16,32),(0,32,16,48)). Each entry counts actual Fin 6 next rows satisfying horizontal properness, both diagonals, and the current first-appearance scanner. The class count and preservation of admissibility are verified for every boundary and every actual next row."),
            Def("initial", "r", "The actual first rows", "The initial vector is (4,0,2,4). Its ten rows are U:0101,0104,0151,0154; B:0120,0125; C:0102,0121,0124,0152. There is no A first row."),
            Def("continuation", "sourceV", "The source vector recurrence", "For every class i, sourceV(0,i)=1 and sourceV(m+1,i)=sum over j of M(i,j)sourceV(m,j). The theorem identifies this recurrence with the existing literal row-continuation count for all admissible scanner states and boundaries."),
            Describe.Lean(DescribeId.Create("four-class-certificate"),
                DeclarationHandle.Create(Prefix + "four_class_certificate"),
                H("Exact admissible four-class transfer certificate"), StatementSource.FromAuthor(Disp(FourClassCertificateFormula())),
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
    private static Formula Name(string name) => Seq(name.Split('.').SelectMany((part, k) => k == 0
        ? new[] { Seq(Operatorname, Grp(F.Id(part))) }
        : new[] { Dot, Seq(Operatorname, Grp(F.Id(part))) }).ToArray());
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Name(name) : new Formula.Apply(Name(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, Parenthesized(body));
    private static Formula ResultFormula()
    {
        var m = V("m"); var s = V("s"); var p = V("p"); var j = V("j");
        var state = All("s", Seen(), All("p", Boundary(), Imp(Call("HardinSourceContinuations.admissible", s, p),
            Eq(Call("HardinA233251TriangleStrip.widthV", RowOKFunction(), PairsFunction(), NextOKFunction(), m, s, p),
                Call("HardinSourceContinuations.sourceV", m, Call("HardinSourceContinuations.sourceClass", s, p))))));
        var total = Eq(Typed(Call("Nat.card", Call("HardinThinGraphTransport.literalStrip", Call("true"), m, D(3))), Call("Int")),
            SumOver("j", Fin(4), new Formula.Binary(Call("HardinSourceContinuations.r", j), FormulaBinaryOperator.Multiply,
                Call("HardinSourceContinuations.sourceV", m, j))));
        return All("m", Call("Nat"), And(state, total));
    }
    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Fin(byte size) => Call("Fin", D(size));
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula Conditional(Formula test, Formula yes, Formula no) => Parenthesized(
        Seq(Call("if"), Sp, Parenthesized(test), Sp, Call("then"), Sp, Parenthesized(yes), Sp, Call("else"), Sp, Parenthesized(no)));
    private static Formula SumOver(string n, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(V(n), Colon, Sp, type), Sp, Parenthesized(body));
    private static Formula Seen() => Call("HardinA233175PairStrip.Seen");
    private static Formula Boundary() => new Formula.TypeArrow(Fin(4), Fin(3));
    private static Formula Row() => new Formula.TypeArrow(Fin(4), Fin(6));
    private static Formula Fn(string n, Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Typed(V(n), type), Sp, Mapsto, Sp, Parenthesized(body)));
    private static Formula Pairs(Formula c) => Fn("i", Fin(4), Call("D5.S3.Observer.Separation.BooleanRankThreeK4.beta", At(c, V("i"))));
    private static Formula RowOK(Formula c) => Call("HardinThinGraphTransport.proper", Pairs(c));
    private static Formula NextOK(Formula p, Formula c) => Call("HardinThinGraphTransport.compatible", Call("true"), p, Pairs(c));
    private static Formula PairsFunction() => Fn("c", Row(), Pairs(V("c")));
    private static Formula RowOKFunction() => Fn("c", Row(), RowOK(V("c")));
    private static Formula NextOKFunction() => Fn("p", Boundary(), Fn("c", Row(), NextOK(V("p"), V("c"))));
    private static Formula FourClassCertificateFormula()
    {
        var s = V("s"); var p = V("p"); var c = V("c"); var j = V("j");
        Formula Own(string name, params Formula[] args) => Call("HardinSourceContinuations." + name, args);
        Formula Scanner(string name, params Formula[] args) => Call("HardinA233175PairStrip." + name, args);
        var unseen = Parenthesized(Seq(Call("false"), Comma, Sp, Call("false")));
        Formula UnderValid(Formula body) => All("s", Seen(), All("p", Boundary(), Imp(Own("admissible", s, p), body)));
        Formula NextGuard(Formula seen) => And(RowOK(c), And(NextOK(p, c), Scanner("good", seen, c)));
        var firstGuard = And(Eq(At(c, D(0)), D(0)), And(RowOK(c), Scanner("good", unseen, c)));
        Formula NextClass(Formula seen) => Own("sourceClass", Scanner("finish", seen, c), Pairs(c));
        Formula Indicator(Formula condition) => Typed(Conditional(condition, D(1), D(0)), Call("Int"));
        var nextValid = UnderValid(All("c", Row(), Imp(NextGuard(s), Own("admissible", Scanner("finish", s, c), Pairs(c)))));
        var firstValid = All("c", Row(), Imp(firstGuard, Own("admissible", Scanner("finish", unseen, c), Pairs(c))));
        var transitions = UnderValid(All("j", Fin(4), Eq(SumOver("c", Row(),
            Indicator(And(NextGuard(s), Eq(NextClass(s), j)))), Own("M", Own("sourceClass", s, p), j))));
        var initial = All("j", Fin(4), Eq(SumOver("c", Row(), Indicator(And(firstGuard, Eq(NextClass(unseen), j)))), Own("r", j)));
        return And(nextValid, And(firstValid, And(transitions, initial)));
    }

    private static Formula DecidableAdmissibleFormula() => All("s", Seen(), All("p", Boundary(), Typed(
            Call("HardinSourceContinuations.instDecidableAdmissible", V("s"), V("p")),
            Call("Decidable", Call("HardinSourceContinuations.admissible", V("s"), V("p"))))));

}

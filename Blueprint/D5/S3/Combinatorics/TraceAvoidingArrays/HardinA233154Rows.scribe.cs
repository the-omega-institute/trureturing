using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;
internal sealed class HardinA233154RowsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233154Rows.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Automata/hardin2013a233154");
    private static DocumentBlock Node(string declaration, Formula formula, string prose, bool count = false, bool theorem = false) =>
        Describe.Lean(DescribeId.Create("hardina233154rows-" + declaration.ToLowerInvariant().Replace("_", "-")), DeclarationHandle.Create(Prefix + declaration), H(declaration), StatementSource.FromAuthor(Disp(formula)), count ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), theorem ? DescribeRole.Theorem : DescribeRole.Definition);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal 7-column count obeys a recurrence determined by its finite row quotient.",
        H("OEIS A233154"), Blocks(
            Node("T7",All("n",NatF(),Eq(C("T7",V("n")),FilterCard(N(7),V("n")))),"Every labelled function satisfying the two bond conditions is counted.",true),
            Node("classes",Cast(C("classes"),ClassTableType(7,16)),"The complete nested lookup table on the 7 row coordinates, including its zero entries."),
            Node("classify",All("r",RowF(N(7)),Eq(C("classify",V("r")),A(V("classes"),A(V("r"),N(0)), A(V("r"),N(1)), A(V("r"),N(2)), A(V("r"),N(3)), A(V("r"),N(4)), A(V("r"),N(5)), A(V("r"),N(6))))),"The finite decision tree assigns the successor class of a row."),
            Node("quotient",Eq(C("quotient"),Vec(Vec(N(5), N(5), N(3), N(3), N(4), N(4), N(2), N(2), N(3), N(3), N(3), N(3), N(1), N(1), N(0), N(0)), Vec(N(4), N(4), N(3), N(3), N(4), N(4), N(2), N(2), N(2), N(2), N(1), N(1), N(1), N(1), N(1), N(1)), Vec(N(3), N(3), N(3), N(3), N(3), N(3), N(2), N(2), N(3), N(3), N(3), N(3), N(2), N(2), N(0), N(0)), Vec(N(1), N(1), N(2), N(2), N(1), N(1), N(3), N(3), N(1), N(1), N(2), N(2), N(2), N(2), N(2), N(2)), Vec(N(4), N(4), N(2), N(2), N(4), N(4), N(2), N(2), N(3), N(3), N(1), N(1), N(1), N(1), N(0), N(0)), Vec(N(4), N(4), N(2), N(2), N(4), N(4), N(2), N(2), N(2), N(2), N(3), N(3), N(1), N(1), N(1), N(1)), Vec(N(2), N(2), N(2), N(2), N(2), N(2), N(2), N(2), N(2), N(2), N(2), N(2), N(3), N(3), N(1), N(1)), Vec(N(0), N(0), N(2), N(2), N(0), N(0), N(2), N(2), N(0), N(0), N(2), N(2), N(2), N(2), N(3), N(3)), Vec(N(3), N(3), N(3), N(3), N(3), N(3), N(1), N(1), N(3), N(3), N(3), N(3), N(1), N(1), N(0), N(0)), Vec(N(2), N(2), N(1), N(1), N(2), N(2), N(3), N(3), N(2), N(2), N(1), N(1), N(1), N(1), N(1), N(1)), Vec(N(4), N(4), N(3), N(3), N(2), N(2), N(1), N(1), N(3), N(3), N(3), N(3), N(2), N(2), N(0), N(0)), Vec(N(2), N(2), N(3), N(3), N(2), N(2), N(1), N(1), N(1), N(1), N(2), N(2), N(2), N(2), N(2), N(2)), Vec(N(2), N(2), N(1), N(1), N(2), N(2), N(1), N(1), N(3), N(3), N(2), N(2), N(2), N(2), N(0), N(0)), Vec(N(2), N(2), N(1), N(1), N(2), N(2), N(1), N(1), N(1), N(1), N(3), N(3), N(2), N(2), N(2), N(2)), Vec(N(0), N(0), N(1), N(1), N(0), N(0), N(1), N(1), N(0), N(0), N(1), N(1), N(1), N(1), N(3), N(3)), Vec(N(1), N(1), N(1), N(1), N(1), N(1), N(1), N(1), N(1), N(1), N(1), N(1), N(3), N(3), N(2), N(2)))),"The quotient entry counts legal compatible successors in each class."),
            Node("weights",Eq(C("weights"),Vec(N(12), N(12), N(12), N(12), N(12), N(12), N(12), N(12), N(12), N(12), N(12), N(12), N(12), N(12), N(12), N(12))),"The weights count legal rows in each class."),
            Node("codes",Eq(C("codes"),Seq(OpenBracket,Join(new Formula[]{N(0), N(1), N(3), N(5), N(9), N(10), N(16), N(17), N(27), N(28), N(30), N(32), N(48), N(50), N(52), N(53), N(81), N(82), N(84), N(86), N(90), N(91), N(97), N(98), N(144), N(145), N(151), N(152), N(156), N(158), N(160), N(161), N(243), N(244), N(246), N(248), N(252), N(253), N(259), N(260), N(270), N(271), N(273), N(275), N(291), N(293), N(295), N(296), N(432), N(433), N(435), N(437), N(453), N(455), N(457), N(458), N(468), N(469), N(475), N(476), N(480), N(482), N(484), N(485), N(729), N(730), N(732), N(734), N(738), N(739), N(745), N(746), N(756), N(757), N(759), N(761), N(777), N(779), N(781), N(782), N(810), N(811), N(813), N(815), N(819), N(820), N(826), N(827), N(873), N(874), N(880), N(881), N(885), N(887), N(889), N(890), N(1296), N(1297), N(1299), N(1301), N(1305), N(1306), N(1312), N(1313), N(1359), N(1360), N(1366), N(1367), N(1371), N(1373), N(1375), N(1376), N(1404), N(1405), N(1407), N(1409), N(1425), N(1427), N(1429), N(1430), N(1440), N(1441), N(1447), N(1448), N(1452), N(1454), N(1456), N(1457), N(1701), N(1702), N(1704), N(1706), N(1710), N(1711), N(1717), N(1718), N(1728), N(1729), N(1731), N(1733), N(1749), N(1751), N(1753), N(1754), N(1890), N(1891), N(1893), N(1895), N(1911), N(1913), N(1915), N(1916), N(1926), N(1927), N(1933), N(1934), N(1938), N(1940), N(1942), N(1943), N(2025), N(2026), N(2028), N(2030), N(2034), N(2035), N(2041), N(2042), N(2088), N(2089), N(2095), N(2096), N(2100), N(2102), N(2104), N(2105), N(2133), N(2134), N(2136), N(2138), N(2154), N(2156), N(2158), N(2159), N(2169), N(2170), N(2176), N(2177), N(2181), N(2183), N(2185), N(2186)}),CloseBracket)),"The list contains every legal row code once."),
            Node("classCount",ClassCountFormula(),"The sum counts compatible legal successors in one destination class.")), []));
    private static Formula ClassCountFormula() {
        var r=V("r"); var s=V("s"); var c=V("c");
        var value=Ite(And(C("compatible",r,C("decode",N(7),c)),
            Eq(C("classify",C("decode",N(7),c)),s)),Cast(N(1),IntF()),N(0));
        return All("r",RowF(N(7)),All("s",FinF(N(16)),Eq(C("classCount",r,s),
            C("List.sum",C("List.map",Lam("c",FinF(N(2187)),value),C("codes"))))));
    }
    private static Formula V(string name) => F.Id(name);
    private static Formula Op(string name) => Seq(Operatorname, Grp(Name(name)));
    private static Formula Name(string name) => Seq(name.Split('.').SelectMany((part,i) =>
        i == 0 ? new[]{Atom(part)} : new[]{Dot,Atom(part)}).ToArray());
    private static Formula Atom(string part) {
        var words=part.Split('_');
        return words.Length == 1 ? V(part) : new Formula.Subscript(V(words[0]),
            Seq(words.Skip(1).Select(V).ToArray()));
    }

    private static Formula C(string name, params Formula[] args) => args.Length == 0 ? Name(name) : new Formula.Apply(Name(name), [.. args]);
    private static Formula A(Formula fn, params Formula[] args) => new Formula.Apply(fn, [.. args]);
    private static Formula P(Formula f) => Parenthesized(f);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Lam(string name, Formula type, Formula body) => P(Seq(LambdaLower, Sp, V(name), Colon, Sp, type, Sp, Mapsto, Sp, P(body)));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(P(a), FormulaLogicOperator.And, P(b));
    private static Formula Arr(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula N(int n) => n < 0 ? Seq(Minus, N(-n)) : D(n.ToString(System.Globalization.CultureInfo.InvariantCulture).Select(c => (byte)(c - '0')).ToArray());
    private static Formula FinF(Formula n) => C("Fin", n);
    private static Formula ClassTableType(int width, int q) { Formula t = FinF(N(q)); for (int i = 0; i < width; ++i) t = Arr(FinF(N(3)), t); return t; }
    private static Formula NatF() => Op("Nat");
    private static Formula IntF() => Op("Int");
    private static Formula Cast(Formula x, Formula t) => P(Seq(x, Colon, Sp, t));
    private static Formula RowF(Formula k) => C("Row", k);
    private static Formula Grid(Formula k, Formula n) => Arr(Seq(FinF(n), Sp, Times, Sp, FinF(k)), FinF(N(3)));
    private static Formula Ite(Formula p, Formula a, Formula b) => Seq(Op("if"), Sp, p, Sp, Op("then"), Sp, a, Sp, Op("else"), Sp, b);
    private static Formula FilterCard(Formula k, Formula n) => C("Finset.card", C("Finset.filter", Lam("f", Grid(k,n), C("Legal",V("f"))), Op("Finset.univ")));
    private static Formula Vec(params Formula[] xs) => Seq(Bang, OpenBracket, Join(xs), CloseBracket);
    private static Formula Join(Formula[] xs) => Seq(xs.SelectMany((x,i) => i == 0 ? new[]{x} : new[]{Comma,Sp,x}).ToArray());
}

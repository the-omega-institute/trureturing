using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;
internal sealed class HardinA233159RowsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233159Rows.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Automata/hardin2013a233159");
    private static DocumentBlock Node(string declaration, Formula formula, string prose, bool count = false, bool theorem = false) =>
        Describe.Lean(DescribeId.Create("a233159-hardina233159rows-" + declaration.ToLowerInvariant().Replace("_", "-")), DeclarationHandle.Create(Prefix + declaration), H(declaration), StatementSource.FromAuthor(Disp(formula)), count ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), theorem ? DescribeRole.Theorem : DescribeRole.Definition);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equality patterns and their quotient determine labelled six-row strip counts.",
        H("OEIS A233159"), Blocks(
            Node("U6",All("n",NatF(),Eq(C("U6",V("n")),FilterCard(N(6),V("n")))),"Every labelled function satisfying horizontal and antidiagonal sum exclusion is counted.",true),
            Node("classes",All("a",FinF(N(3)),All("b",FinF(N(3)),All("c",FinF(N(3)),All("d",FinF(N(3)),All("e",FinF(N(3)),All("f",FinF(N(3)),Eq(C("classes",V("a"),V("b"),V("c"),V("d"),V("e"),V("f")),Ite(Eq(V("b"),V("a")),Ite(Eq(V("c"),V("a")),Ite(Eq(V("d"),V("a")),Ite(Eq(V("e"),V("a")),Ite(Eq(V("f"),V("a")),N(0),N(1)),Ite(Eq(V("f"),V("a")),N(2),Ite(Eq(V("f"),V("e")),N(3),N(4)))),Ite(Eq(V("e"),V("a")),Ite(Eq(V("f"),V("a")),N(5),Ite(Eq(V("f"),V("d")),N(6),N(7))),Ite(Eq(V("e"),V("d")),Ite(Eq(V("f"),V("a")),N(8),Ite(Eq(V("f"),V("d")),N(9),N(10))),Ite(Eq(V("f"),V("a")),N(11),Ite(Eq(V("f"),V("d")),N(12),N(13)))))),Ite(Eq(V("d"),V("a")),Ite(Eq(V("e"),V("a")),Ite(Eq(V("f"),V("a")),N(14),Ite(Eq(V("f"),V("c")),N(15),N(16))),Ite(Eq(V("e"),V("c")),Ite(Eq(V("f"),V("a")),N(17),Ite(Eq(V("f"),V("c")),N(18),N(19))),Ite(Eq(V("f"),V("a")),N(20),Ite(Eq(V("f"),V("c")),N(21),N(22))))),Ite(Eq(V("d"),V("c")),Ite(Eq(V("e"),V("a")),Ite(Eq(V("f"),V("a")),N(23),Ite(Eq(V("f"),V("c")),N(24),N(25))),Ite(Eq(V("e"),V("c")),Ite(Eq(V("f"),V("a")),N(26),Ite(Eq(V("f"),V("c")),N(27),N(28))),Ite(Eq(V("f"),V("a")),N(29),Ite(Eq(V("f"),V("c")),N(30),N(31))))),Ite(Eq(V("e"),V("a")),Ite(Eq(V("f"),V("a")),N(32),Ite(Eq(V("f"),V("c")),N(33),N(34))),Ite(Eq(V("e"),V("c")),Ite(Eq(V("f"),V("a")),N(35),Ite(Eq(V("f"),V("c")),N(36),N(37))),Ite(Eq(V("f"),V("a")),N(38),Ite(Eq(V("f"),V("c")),N(39),N(40)))))))),Ite(Eq(V("c"),V("a")),Ite(Eq(V("d"),V("a")),Ite(Eq(V("e"),V("a")),Ite(Eq(V("f"),V("a")),N(41),Ite(Eq(V("f"),V("b")),N(42),N(43))),Ite(Eq(V("e"),V("b")),Ite(Eq(V("f"),V("a")),N(44),Ite(Eq(V("f"),V("b")),N(45),N(46))),Ite(Eq(V("f"),V("a")),N(47),Ite(Eq(V("f"),V("b")),N(48),N(49))))),Ite(Eq(V("d"),V("b")),Ite(Eq(V("e"),V("a")),Ite(Eq(V("f"),V("a")),N(50),Ite(Eq(V("f"),V("b")),N(51),N(52))),Ite(Eq(V("e"),V("b")),Ite(Eq(V("f"),V("a")),N(53),Ite(Eq(V("f"),V("b")),N(54),N(55))),Ite(Eq(V("f"),V("a")),N(56),Ite(Eq(V("f"),V("b")),N(57),N(58))))),Ite(Eq(V("e"),V("a")),Ite(Eq(V("f"),V("a")),N(59),Ite(Eq(V("f"),V("b")),N(60),N(61))),Ite(Eq(V("e"),V("b")),Ite(Eq(V("f"),V("a")),N(62),Ite(Eq(V("f"),V("b")),N(63),N(64))),Ite(Eq(V("f"),V("a")),N(65),Ite(Eq(V("f"),V("b")),N(66),N(67))))))),Ite(Eq(V("c"),V("b")),Ite(Eq(V("d"),V("a")),Ite(Eq(V("e"),V("a")),Ite(Eq(V("f"),V("a")),N(68),Ite(Eq(V("f"),V("b")),N(69),N(70))),Ite(Eq(V("e"),V("b")),Ite(Eq(V("f"),V("a")),N(71),Ite(Eq(V("f"),V("b")),N(72),N(73))),Ite(Eq(V("f"),V("a")),N(74),Ite(Eq(V("f"),V("b")),N(75),N(76))))),Ite(Eq(V("d"),V("b")),Ite(Eq(V("e"),V("a")),Ite(Eq(V("f"),V("a")),N(77),Ite(Eq(V("f"),V("b")),N(78),N(79))),Ite(Eq(V("e"),V("b")),Ite(Eq(V("f"),V("a")),N(80),Ite(Eq(V("f"),V("b")),N(81),N(82))),Ite(Eq(V("f"),V("a")),N(83),Ite(Eq(V("f"),V("b")),N(84),N(85))))),Ite(Eq(V("e"),V("a")),Ite(Eq(V("f"),V("a")),N(86),Ite(Eq(V("f"),V("b")),N(87),N(88))),Ite(Eq(V("e"),V("b")),Ite(Eq(V("f"),V("a")),N(89),Ite(Eq(V("f"),V("b")),N(90),N(91))),Ite(Eq(V("f"),V("a")),N(92),Ite(Eq(V("f"),V("b")),N(93),N(94))))))),Ite(Eq(V("d"),V("a")),Ite(Eq(V("e"),V("a")),Ite(Eq(V("f"),V("a")),N(95),Ite(Eq(V("f"),V("b")),N(96),N(97))),Ite(Eq(V("e"),V("b")),Ite(Eq(V("f"),V("a")),N(98),Ite(Eq(V("f"),V("b")),N(99),N(100))),Ite(Eq(V("f"),V("a")),N(101),Ite(Eq(V("f"),V("b")),N(102),N(103))))),Ite(Eq(V("d"),V("b")),Ite(Eq(V("e"),V("a")),Ite(Eq(V("f"),V("a")),N(104),Ite(Eq(V("f"),V("b")),N(105),N(106))),Ite(Eq(V("e"),V("b")),Ite(Eq(V("f"),V("a")),N(107),Ite(Eq(V("f"),V("b")),N(108),N(109))),Ite(Eq(V("f"),V("a")),N(110),Ite(Eq(V("f"),V("b")),N(111),N(112))))),Ite(Eq(V("e"),V("a")),Ite(Eq(V("f"),V("a")),N(113),Ite(Eq(V("f"),V("b")),N(114),N(115))),Ite(Eq(V("e"),V("b")),Ite(Eq(V("f"),V("a")),N(116),Ite(Eq(V("f"),V("b")),N(117),N(118))),Ite(Eq(V("f"),V("a")),N(119),Ite(Eq(V("f"),V("b")),N(120),N(121))))))))))))))))),"The equality tests assign one class to each column pattern."),
            Node("classify",All("r",RowF(N(6)),Eq(C("classify",V("r")),A(C("classes"),A(V("r"),N(0)), A(V("r"),N(1)), A(V("r"),N(2)), A(V("r"),N(3)), A(V("r"),N(4)), A(V("r"),N(5))))),"The coordinates select one of the 122 equality classes."),
            Node("representatives", Cast(C("representatives"), Arr(FinF(N(122)), RowF(N(6)))), "The fixed table selects one canonical 6-entry column for each of the 122 equality classes."),
            Node("quotient",All("i",FinF(N(122)),All("s",FinF(N(122)),Eq(C("quotient",V("i"),V("s")),C("List.sum",C("List.map",Lam("j",FinF(N(122)),Ite(Eq(V("j"),V("s")),Cast(N(1),IntF()),N(0))),C("successors",V("i"))))))),"The quotient entry is the multiplicity of a class in the successor list."),
            Node("weights", Cast(C("weights"), Arr(FinF(N(122)), IntF())), "The fixed 122-entry integer vector records three labelled constant columns in the constant class and six labelled columns in every other equality class."),
            Node("successors", Cast(C("successors"), Arr(FinF(N(122)), C("List", FinF(N(122))))), "The fixed table assigns each of the 122 representatives its list of compatible successor classes in base-three code order, retaining multiplicities."),
            Node("equality_classes",EqualityFormula(),"Color permutations preserve the equality class and carry each column to its representative.",theorem:true)), []));
    private static Formula EqualityFormula() {
        var perm=C("Equiv.Perm",FinF(N(3)));
        var invariant=All("e",perm,All("r",RowF(N(6)),Eq(C("classify",C("relabel",V("e"),V("r"))),C("classify",V("r")))));
        var representative=All("r",RowF(N(6)),new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create("e"),perm,Eq(C("relabel",V("e"),V("r")),C("representatives",C("classify",V("r"))))));
        return And(invariant,representative);
    }
    private static Formula V(string name) => F.Id(name);
    private static Formula Op(string name) => Seq(Operatorname, Grp(Name(name)));
    private static Formula Name(string name) => Seq(name.Split('.').SelectMany((part,i) =>
        i == 0 ? new[]{Atom(part)} : new[]{Dot,Atom(part)}).ToArray());
    private static Formula Atom(string part) {
        var words=part.Split('_');
        if (part == "U3") return new Formula.Subscript(V("U"),N(3));
        if (part == "U4") return new Formula.Subscript(V("U"),N(4));
        if (part == "U5") return new Formula.Subscript(V("U"),N(5));
        if (part == "U6") return new Formula.Subscript(V("U"),N(6));
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
    private static Formula NatF() => Op("Nat");
    private static Formula IntF() => Op("Int");
    private static Formula Cast(Formula x, Formula t) => P(Seq(x, Colon, Sp, t));
    private static Formula RowF(Formula k) => C("Row", k);
    private static Formula Grid(Formula k, Formula n) => Arr(P(Seq(FinF(k), Sp, Times, Sp, FinF(n))), FinF(N(3)));
    private static Formula Ite(Formula p, Formula a, Formula b) => Seq(Op("if"), Sp, p, Sp, Op("then"), Sp, a, Sp, Op("else"), Sp, b);
    private static Formula FilterCard(Formula k, Formula n) => C("Finset.card", C("Finset.filter", Lam("f", Grid(k,n), C("Legal",V("f"))), Op("Finset.univ")));
}

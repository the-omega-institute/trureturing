using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class SingerQuadricQuditDistanceBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/SingerQuadricQuditDistanceBound.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumStates/kulhandjian2026singer");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every odd prime p and every primitive element of GaloisField p 3, the Singer-quadric stabilizer code has a non-stabilizer centralizer vector of Pauli weight at most p+1. A translated trace-plane indicator gives a centralizer vector. A right-kernel separator and two correlation moments ensure that at least one translated vector lies outside the stabilizer row space.",
        H("Kulhandjian-Hanzo Conjecture 25: the odd-prime distance bound"), Blocks(
            Node("tauh", "The trace-plane indicator", IndicatorFormula("tauH", false),
                "At q=p and d=2, the carrier is GaloisField p 3 and the positions are Fin(p^2+p+1). The entry is 0 when the trace is nonzero.",
                "tauH", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("tauq", "The quadric indicator", IndicatorFormula("tauQ", true),
                "For odd p the exponent is 2*val(i), with trace zero giving entry 1 and nonzero trace giving entry 0. Primitive powers have period p^3-1, so the source's exponent reduction modulo p^3-1 gives the same entry.",
                "tauQ", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("a", "The Singer circulant", MatrixFormula("A", QCall("Matrix", "circulant", Call("tauH", AlphaValue()))),
                "A=circ(tau_H), with entry tauH(alpha)(i-j) and cyclic subtraction in Fin(p^2+p+1).", "A", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("mq", "The quadric circulant", MatrixFormula("MQ", QCall("Matrix", "circulant", Call("tauQ", AlphaValue()))),
                "M_Q=circ(tau_Q), using the same first-column circulant convention as A.", "MQ", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("b", "The second check block", MatrixFormula("B", TimesOf(Call("MQ", AlphaValue()), Call("A", AlphaValue()))),
                "The X block is M_Q*A over ZMod p.", "B", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("h", "The stabilizer check matrix", CheckFormula(),
                "Page 11, Section V: H=(H_z | H_x):=(A | M_Q A). Sum.elim concatenates the two row functions, so H has columns indexed by Fin(p^2+p+1) summed with Fin(p^2+p+1).",
                "H", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("symp", "The symplectic pairing", SymplecticFormula(),
                "The first component is the Z part, and the second the X part. The signed form is z dot x' minus x dot z'; its vanishing expresses symplectic commutation.",
                "symp", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("stabilizers", "The stabilizer row space", StabilizersFormula(),
                "The pairs (c*A,c*B) for all row coefficient vectors c are exactly rowspan(H), with H=(A | B).", "stabilizers", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("centralizer", "The symplectic centralizer", CentralizerFormula(),
                "The vectors pairing to zero with every element of the stabilizer row space.", "centralizer", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("weight", "The Pauli weight", WeightFormula(),
                "Weight counts positions where either component is nonzero, counting a position only once when both are nonzero.", "wt", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 25", ClaimFormula(),
                "The encoding quantifies over every prime p>2 and every alpha of multiplicative order p^3-1. It asserts a vector in the symplectic centralizer, outside rowspan(H), of Pauli weight at most p+1.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The conjectured distance bound holds", Disp(F.Id("claim")),
                "Let D and Q be the trace-plane and trace-square supports. Both have size p+1, and D has nonzero difference multiplicities one. A translated reversed indicator s has A*s=1, while MQ*1=1, so (s,s) centralizes the row space. The vector (tauQ,-e_0) is in the ordinary right kernel of H. Its pairing with (s,s) is m_t-delta_t, where m_t counts (t-D) intersect Q and delta_t indicates membership in D. The moment identities sum(m_t)=(p+1)^2 and sum(m_t^2)=(p+1)^2+p^2+p contradict m_t congruent to delta_t modulo p for every t: their forced lower bound exceeds the second moment by p*(p-2)*(p+1)>0. A nonzero pairing excludes stabilizer membership. The support of (s,s) has p+1 positions.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("kulhandjian-hanzo-2026-flagship-distance-conjecture-25"),
                    ResolutionKind.Proved))), []));

    private static Formula IndicatorFormula(string name, bool doubled)
    {
        Formula i = F.Id("i");
        Formula exponent = doubled ? TimesOf(F.D(2), Value(i)) : Value(i);
        return Disp(AlphaBinder(All(i, Index(), Equal(Apply(Call(name, AlphaValue()), i),
            Call("ite", Equal(Trace(Power(AlphaValue(), exponent)), F.D(0)), F.D(1), F.D(0))))));
    }
    private static Formula MatrixFormula(string name, Formula value) =>
        Disp(AlphaBinder(Equal(Call(name, AlphaValue()), value)));
    private static Formula CheckFormula()
    {
        Formula i = F.Id("i"), j = F.Id("j");
        return Disp(AlphaBinder(All(i, Index(), All(j, Call("Sum", Index(), Index()),
            Equal(Apply(Call("H", AlphaValue()), i, j), QCall("Sum", "elim",
                Apply(Call("A", AlphaValue()), i), Apply(Call("B", AlphaValue()), i), j))))));
    }
    private static Formula SymplecticFormula()
    {
        Formula v = F.Id("v"), w = F.Id("w");
        return Disp(All(P(), Naturals(), All(v, Pairs(), All(w, Pairs(),
            Equal(Call("symp", v, w), MinusOf(Call("dotProduct", Component(v, 1), Component(w, 2)),
                Call("dotProduct", Component(v, 2), Component(w, 1))))))));
    }
    private static Formula StabilizersFormula()
    {
        Formula v = F.Id("v"), c = F.Id("c");
        return Disp(AlphaBinder(All(v, Pairs(), Equivalent(Member(v, Call("stabilizers", AlphaValue())),
            Some(c, Vectors(), Equal(v, Pair(QCall("Matrix", "vecMul", c, Call("A", AlphaValue())),
                QCall("Matrix", "vecMul", c, Call("B", AlphaValue())))))))));
    }
    private static Formula CentralizerFormula()
    {
        Formula v = F.Id("v"), w = F.Id("w");
        return Disp(AlphaBinder(All(v, Pairs(), Equivalent(Member(v, Call("centralizer", AlphaValue())),
            All(w, Pairs(), Implies(Member(w, Call("stabilizers", AlphaValue())), Equal(Call("symp", v, w), F.D(0))))))));
    }
    private static Formula WeightFormula()
    {
        Formula v = F.Id("v"), i = F.Id("i");
        return Disp(All(P(), Naturals(), All(v, Pairs(), Equal(Call("wt", v), Count(i,
            Or(NotEqual(Apply(Component(v, 1), i), F.D(0)), NotEqual(Apply(Component(v, 2), i), F.D(0))))))));
    }
    private static Formula ClaimFormula()
    {
        Formula v = F.Id("v");
        Formula logical = Some(v, Pairs(), And(Member(v, Call("centralizer", AlphaValue())),
            And(NotMember(v, Call("stabilizers", AlphaValue())), Leq(Call("wt", v), PlusOf(P(), F.D(1))))));
        return Disp(Equivalent(F.Id("claim"), All(P(), Naturals(), Implies(Prime(),
            Implies(Less(F.D(2), P()), All(AlphaValue(), Field(), Implies(Primitive(), logical)))))));
    }
    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("kh25-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance, Commentary(id, prose), role, resolution);
    private static BlockSequence Commentary(string id, string prose)
    {
        if (id == "claim")
        {
            Formula code = Apply(Seq(Mathcal, Grp(F.Id("Q"))), P(), F.D(2));
            Formula distance = new Formula.Subscript(F.Id("d"), Min);
            return Blocks(Paragraph(Text("Page 19, Section VII, Conjecture 25 (Flagship distance, original): “For prime "),
                Math(In(P())), Text(" odd, "),
                Math(In(Leq(Seq(distance, Parenthesized(code)), PlusOf(P(), F.D(1))))), Text(".”")),
                Paragraph(Text(prose)));
        }
        if (id == "tauh")
        {
            Formula tau = Seq(Mathbf, Grp(new Formula.Subscript(Tau, F.Id("H"))));
            Formula entry = new Formula.Subscript(Parenthesized(tau), F.Id("i"));
            Formula tr = new Formula.Subscript(Named("Tr"), Seq(F.Id("K"), Slash, F.Id("F")));
            return Blocks(Paragraph(Text("Page 7, Section III: “Its first column "), Math(In(tau)),
                Text(" has "), Math(In(Equal(entry, F.D(1)))), Text(" iff "),
                Math(In(Equal(Seq(tr, Parenthesized(Power(Alpha, F.Id("i")))), F.D(0)))), Text(".”")),
                Paragraph(Text(prose)));
        }
        if (id == "tauq")
        {
            Formula q = F.Id("q"), d = F.Id("d"), i = F.Id("i");
            Formula tau = Seq(Mathbf, Grp(new Formula.Subscript(Tau, F.Id("Q"))));
            Formula field = Seq(Mathbb, Grp(F.Id("F")));
            Formula space = new Formula.Power(new Formula.Subscript(field, q), F.Id("n"));
            Formula index = Seq(Parenthesized(TimesOf(Xi, i)), Sp, Named("mod"), Sp,
                Parenthesized(MinusOf(Power(q, PlusOf(d, F.D(1))), F.D(1))));
            Formula table = Seq(F.Id("T"), OpenBracket, index, CloseBracket);
            return Blocks(Paragraph(Text("Page 27, Appendix A, Step 3: “Set "),
                Math(In(Equal(Xi, PlusOf(F.Id("q"), F.D(1))))), Text(" if "), Math(In(F.Id("q"))),
                Text(" is even, "), Math(In(Equal(Xi, F.D(2)))), Text(" if "), Math(In(F.Id("q"))),
                Text(" is odd. Define "), Math(In(Member(tau, space))), Text(" by "),
                Math(In(Equal(new Formula.Subscript(Parenthesized(tau), i), F.D(1)))), Text(" if "),
                Math(In(Equal(table, F.D(0)))), Text(", else "), Math(In(F.D(0))), Text(".”")),
                Paragraph(Text(prose)));
        }
        return Blocks(Paragraph(Text(prose)));
    }

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula QCall(string owner, string name, params Formula[] args) => new Formula.Apply(Qualified(owner, name), [.. args]);
    private static Formula Apply(Formula value, params Formula[] args) => new Formula.Apply(value, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula NotEqual(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula NotMember(Formula a, Formula b) => new Formula.Not(Parenthesized(Member(a, b)));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Equivalent(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula All(Formula a, Formula type, Formula body) => Seq(Forall, Sp, a, Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(Formula a, Formula type, Formula body) => Seq(Exists, Sp, a, Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula PlusOf(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula MinusOf(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula TimesOf(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Power(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Prime() => QCall("Nat", "Prime", P());
    private static Formula P() => F.Id("p");
    private static Formula AlphaValue() => Alpha;
    private static Formula Field() => Call("GaloisField", P(), F.D(3));
    private static Formula Scalars() => Call("ZMod", P());
    private static Formula Index() => Call("Fin", PlusOf(PlusOf(Power(P(), F.D(2)), P()), F.D(1)));
    private static Formula Vectors() => Parenthesized(Seq(Index(), Sp, To, Sp, Scalars()));
    private static Formula Pairs() => Call("Prod", Vectors(), Vectors());
    private static Formula BaseBinder(Formula body) => All(P(), Naturals(),
        Seq(OpenBracket, Call("Fact", Prime()), CloseBracket, Comma, Sp, body));
    private static Formula AlphaBinder(Formula body) => BaseBinder(All(AlphaValue(), Field(), body));
    private static Formula Value(Formula i) => Call("val", i);
    private static Formula Trace(Formula x) => QCall("Algebra", "trace", Scalars(), Field(), x);
    private static Formula Pair(Formula x, Formula y) => Parenthesized(Seq(x, Comma, Sp, y));
    private static Formula Component(Formula v, byte j) => Seq(v, Dot, F.D(j));
    private static Formula Filter(Formula i, Formula condition) => QCall("Finset", "filter",
        Seq(Parenthesized(Seq(i, Colon, Sp, Index())), Sp, Mapsto, Sp, condition), QCall("Finset", "univ", Index()));
    private static Formula Count(Formula i, Formula condition) => QCall("Finset", "card", Filter(i, condition));
    private static Formula Primitive() => Equal(Call("orderOf", AlphaValue()), MinusOf(Power(P(), F.D(3)), F.D(1)));
}

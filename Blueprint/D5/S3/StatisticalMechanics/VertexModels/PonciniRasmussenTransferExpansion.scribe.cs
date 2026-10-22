using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.VertexModels;

internal sealed class PonciniRasmussenTransferExpansionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenTransferExpansion.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/StatisticalMechanics/poncini2023planar");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The eight-vertex transfer matrix equals the central factorial polynomial expansion of its principal Hamiltonian over every algebraically closed field of characteristic zero.", H("The Poncini\u2013Rasmussen transfer expansion"), Blocks(
        Node("Rcoef", "Eight-vertex coefficients", RBody(), "Page 42, (C.15): R^{km}_{jl}(u) is 1 if j = m, l = k; u if j = l, k = m, j \u2260 k; u if j = k, l = m, j \u2260 l; and 0 otherwise. All four indices belong to Fin 2.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
        Node("Kcoef", "Boundary coefficients", KBody(), "Page 42, (C.15): \u201cK^k_j(u) = K\u0304^k_j(u) = \u03b4_{jk}\u201d. The coefficients are independent of u.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
        Node("twoSite", "Two-site operators", TwoBody(), "Page 42, (C.9)\u2013(C.10): \u201cR_{i,n+1}(u) := \u03a3_{j,k,l,m} R^{km}_{jl}(u) 1_{i\u22121} \u2297 e^k_j \u2297 1_{n\u2212i} \u2297 e^m_l\u201d. Rows x and columns y are configurations; coordinates outside a and b agree, and the matrix-unit entry is (row, column) = (k, j).", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
        Node("oneSite", "Boundary operators", OneBody(), "Page 42, (C.11) defines K_1(u) and K\u0304_{n+1}(u). The matrix-unit coefficient Kcoef acts on coordinate a, with identity on every other coordinate.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
        Node("preTrace", "The ordered double row", PreBody(), "Page 42, (C.12): \u201cL_{n+1}(u) := R_{n,n+1}(u) \u22ef R_{1,n+1}(u) K_1(u) R_{n+1,1}(u) \u22ef R_{n+1,n}(u) K\u0304_{n+1}(u)\u201d. Lean coordinates start at zero and the auxiliary coordinate is Fin.last n.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
        Node("transfer", "The auxiliary partial trace", TransferBody(), "Page 42, (C.13): \u201c\u0164_n(u) = Tr_{n+1}(L_{n+1}(u))\u201d. Fin.snoc appends the same auxiliary bit to the row and column, and the sum ranges over its two values.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
        Node("hamiltonian", "The principal Hamiltonian", HamiltonianBody(), "Page 45, (C.40): \u201ch_n = \u03a3_{i=1}^{n\u22121} \u03c3^x_{n,i} \u03c3^x_{n,i+1}\u201d. Each term flips the adjacent pair and fixes every other coordinate. The proof h certifies that the next Fin index belongs to the chain.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
        Node("claim", "Conjecture C.12", ClaimDefinition(), "Page 47, Conjecture C.12: \u201cFor every n \u2208 \u2115 and all u \u2208 F, we have \u0164_n(u) = 2 \u03a3_{k=0}^{n\u22121} (1 + u\u00b2)^{n\u2212k} (2u)^k \u03a3_{j=0}^{\u230ak/2\u230b} [n \u2212 k \u2212 2 + 2j over 2j]!! (\u22121)^j m_{k\u22122j}(h_n)/(k \u2212 2j)!\u201d. Here n \u2265 1, F is an algebraically closed field of characteristic zero, and the basis of its n-fold tensor power is Fin n \u2192 Fin 2. Nat.div denotes natural-number division; natural subtraction is truncated.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
        Node("result", "The transfer expansion", ClaimBody(), "Conjecture C.12 holds. The ordered product reduces to commuting adjacent flips, whose Walsh eigenvectors have Hamiltonian eigenvalue n \u2212 1 \u2212 2l. The scalar central factorial identity then gives the matrix equality.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))
    ), []));
    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("poncinirasmussentransferexpansiondocument-"+name.Replace('_','-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix+name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula RBody() => Field(All("u",X("F"),All("j",Fin(D(2)),All("k",Fin(D(2)),All("l",Fin(D(2)),All("m",Fin(D(2)),
        Eq(Call("Rcoef",X("u"),X("j"),X("k"),X("l"),X("m")),
            Ite(And(Eq(X("j"),X("m")),Eq(X("l"),X("k"))),D(1),
            Ite(And(Eq(X("j"),X("l")),And(Eq(X("k"),X("m")),Ne(X("j"),X("k")))),X("u"),
            Ite(And(Eq(X("j"),X("k")),And(Eq(X("l"),X("m")),Ne(X("j"),X("l")))),X("u"),D(0)))))))))));
    private static Formula KBody() => Field(All("j",Fin(D(2)),All("k",Fin(D(2)),
        Eq(Call("Kcoef",X("j"),X("k")),Ite(Eq(X("j"),X("k")),D(1),D(0))))));
    private static Formula Rest(bool pair) => All("c",Fin(X("N")),Imp(Ne(X("c"),X("a")),pair ?
        Imp(Ne(X("c"),X("b")),Eq(At(X("x"),X("c")),At(X("y"),X("c")))) :
        Eq(At(X("x"),X("c")),At(X("y"),X("c")))));
    private static Formula TwoBody() => Field(All("N",N(),All("u",X("F"),All("a",Fin(X("N")),All("b",Fin(X("N")),
        Eq(Call("twoSite",X("N"),X("u"),X("a"),X("b")),Lam("x",States(X("N")),Lam("y",States(X("N")),
            Ite(Rest(true),Call("Rcoef",X("u"),At(X("y"),X("a")),At(X("x"),X("a")),At(X("y"),X("b")),At(X("x"),X("b"))),D(0))))))))));
    private static Formula OneBody() => Field(All("N",N(),All("a",Fin(X("N")),
        Eq(Call("oneSite",X("N"),X("a")),Lam("x",States(X("N")),Lam("y",States(X("N")),
            Ite(Rest(false),Call("Kcoef",At(X("y"),X("a")),At(X("x"),X("a"))),D(0))))))));
    private static Formula PreHalf(bool first) => Mul(
        Call("List.prod",Call("List.ofFn",Lam("i",Fin(X("n")),
            Call("twoSite",Add(X("n"),D(1)),X("u"),
                first ? Call("Fin.castSucc",Call("Fin.rev",X("i"))) : Call("Fin.last",X("n")),
                first ? Call("Fin.last",X("n")) : Call("Fin.castSucc",X("i")))))),
        Call("oneSite",Add(X("n"),D(1)),first ? D(0) : Call("Fin.last",X("n"))));
    private static Formula PreBody() => Field(All("n",N(),All("u",X("F"),
        Eq(Call("preTrace",X("n"),X("u")),
            Mul(Parenthesized(PreHalf(true)),Parenthesized(PreHalf(false)))))));
    private static Formula TransferBody() => Field(All("n",N(),All("u",X("F"),Eq(Call("transfer",X("n"),X("u")),
        Lam("x",States(X("n")),Lam("y",States(X("n")),
            Sum("s",Call("Finset.univ",Fin(D(2))),Call("preTrace",X("n"),X("u"),
                Call("Fin.snoc",X("x"),X("s")),Call("Fin.snoc",X("y"),X("s"))))))))));
    private static Formula Next() => Seq(Langle,Add(Call("Fin.val",X("i")),D(1)),Comma,X("h"),Rangle);
    private static Formula HamiltonianBody() => Field(All("n",N(),Eq(Call("hamiltonian",X("n")),
        Sum("i",Call("Finset.univ",Fin(X("n"))),Seq(Call("if"),X("h"),Colon,Lt(Add(Call("Fin.val",X("i")),D(1)),X("n")),Sp,Call("then"),Sp,
            Parenthesized(Lam("x",States(X("n")),Lam("y",States(X("n")),Ite(
                And(All("c",Fin(X("n")),Imp(Ne(X("c"),X("i")),Imp(Ne(X("c"),Next()),Eq(At(X("x"),X("c")),At(X("y"),X("c")))))),
                    And(Ne(At(X("x"),X("i")),At(X("y"),X("i"))),Ne(At(X("x"),Next()),At(X("y"),Next())))),D(1),D(0))))),
            Sp,Call("else"),Sp,D(0))))));
    private static Formula ClaimBody() => Field(All("n",N(),Imp(Le(D(1),X("n")),All("u",X("F"),
        Eq(Call("transfer",X("n"),X("u")),Smul(Cast(D(2),X("F")),
            Sum("k",Range(X("n")),Smul(Mul(Pow(Add(D(1),Pow(X("u"),D(2))),Sub(X("n"),X("k"))),Pow(Mul(D(2),X("u")),X("k"))),
                Sum("j",Range(Add(Half(X("k")),D(1))),Smul(CentralCoefficient(X("n"),X("k"),X("j")),
                    Call("Polynomial.aeval",Cast(Call("hamiltonian",X("n")),Matrix(X("n"))),
                        Call("mPoly",Sub(X("k"),Mul(D(2),X("j")))))))))))))),closed:true);
    private static Formula ClaimDefinition() => new Formula.Logic(Call("claim"),FormulaLogicOperator.Iff,Parenthesized(ClaimBody()));

    private static Formula X(string x) => F.Id(x);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Call(string name, params Formula[] args)
    {
        var parts = new List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (parts.Count > 0) parts.Add(Dot);
            parts.Add(F.Id(part));
        }
        return args.Length == 0 ? Seq(Operatorname, Grp([.. parts]))
            : new Formula.Apply(Seq(Operatorname, Grp([.. parts])), [.. args]);
    }
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, X(name), Colon, type, Comma, Sp, Parenthesized(body));
    private static Formula Instance(string name, Formula body) =>
        Seq(OpenBracket, Call(name, X("F")), CloseBracket, Sp, body);
    private static Formula Field(Formula body, bool zero = false, bool closed = false) =>
        All("F", Call("Type"), Instance("Field", closed ? Instance("IsAlgClosed",
            Instance("CharZero", body)) : zero ? Instance("CharZero", body) : body));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a,b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a,b);
    private static Formula Cast(Formula a, Formula type) => Parenthesized(Seq(a, Colon, type));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a,b);
    private static Formula Lam(string name, Formula type, Formula body) =>
        Seq(Call("fun"), Parenthesized(Seq(X(name), Colon, type)), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula N() => Seq(Mathbb, Grp(X("N")));
    private static Formula Z() => Seq(Mathbb, Grp(X("Z")));
    private static Formula Fin(Formula n) => Call("Fin",n);
    private static Formula States(Formula n) => Arrow(Fin(n),Fin(D(2)));
    private static Formula Matrix(Formula n) => Call("Matrix",States(n),States(n),X("F"));
    private static Formula Sum(string name, Formula domain, Formula body) =>
        Seq(F.Sum, Underscore, Grp(X(name), InMacro, Sp, domain), Sp, Parenthesized(body));
    private static Formula Ite(Formula p, Formula a, Formula b) =>
        Seq(Call("if"), Sp, Parenthesized(p), Sp, Call("then"), Sp, Parenthesized(a), Sp, Call("else"), Sp, Parenthesized(b));
    private static Formula Smul(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Cdot, Sp, Parenthesized(b));
    private static Formula Range(Formula n) => Call("Finset.range",n);
    private static Formula Fact(Formula n) => Call("Nat.factorial",n);
    private static Formula Half(Formula k) => Call("Nat.div",k,D(2));
    private static Formula CentralCoefficient(Formula n, Formula k, Formula j) =>
        Div(Mul(Call("dfBinom", Add(Sub(Sub(Cast(n,Z()),Cast(k,Z())),D(2)),Mul(D(2),Cast(j,Z()))),
            Mul(D(2),Cast(j,Z()))), Pow(Cast(Sub(D(0),D(1)),X("F")),j)),
            Cast(Fact(Sub(k,Mul(D(2),j))),X("F")));
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class FullySeparableExchangeObstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/FullySeparableExchangeObstruction.";
    private static readonly LibraryNoteRef Quinta = LibraryNoteRef.Create("D5/L/QuantumBounds/quinta2019resistant");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fully separable finite state has zero coherence whenever an exchanged product-basis diagonal vanishes.",
        H("Full separability and exchanged diagonals"),
        Blocks(
            Node("joinLocal", "Joining complementary configurations", JoinFormula(),
                "The finite loss set J denotes its membership subtype in a carrier position. The complementary subtype contains the retained sites. The dependent conditional has a membership proof in its first branch and a nonmembership proof in its second branch.", AssessedProvenance.FromRepo()),
            Node("partialTraceLocal", "Partial trace over any finite loss set", TraceFormula(),
                "The input matrix is reindexed by the join of the lost and retained configurations. The existing partialTraceFirst sums the same lost configuration in both indices, giving the usual finite partial trace.", AssessedProvenance.FromRepo()),
            Node("IsFullySeparableLocal", "Finite convex mixtures of local density states", SeparableFormula(),
                "Full separability is a convex combination of product states. Each DensityState L is a positive trace-one local matrix, val forgets its proof, and Complex.ofReal embeds each nonnegative real mixture weight into the complex scalars. The product and sum are over all sites and all mixture indices.", AssessedProvenance.FromLiterature(Quinta)),
            Describe.Lean(DescribeId.Create("exchange-density-psd"), DeclarationHandle.Create(Prefix + "density_psd"),
                H("Density states are positive semidefinite"), StatementSource.FromAuthor(DensityPsdFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite local carrier L, forgetting the CStarMatrix wrapper of a DensityState L gives a positive semidefinite complex matrix. Positivity is transported through CStarMatrix.ofMatrixStarAlgEquiv.symm."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("separable-exchange-zero"), DeclarationHandle.Create(Prefix + "separable_exchange_zero"),
                H("A zero exchanged diagonal annihilates coherence"), StatementSource.FromAuthor(ExchangeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Write rho as a convex sum of products of local density matrices. All terms on the exchanged diagonal are nonnegative. If their sum is zero, each weighted product has a zero factor. Positivity makes the corresponding local row or column zero, so every summand of rho(x,y) vanishes. The contrapositive detects entanglement from a nonzero coherence and a zero exchanged diagonal."))), DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("exchange-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Apply(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(F.Id(owner), Dot, F.Id(name)));
    private static Formula Qualified(string owner, string name, params Formula[] args) => Apply(Q(owner, name), args);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Arr(Formula a, Formula b) => Seq(Parenthesized(a), To, Sp, b);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Lam(string name, Formula type, Formula body) => Parenthesized(Seq(LambdaLower, Sp, Parenthesized(Seq(F.Id(name), Colon, type)), Sp, Mapsto, Sp, body));
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula IffTo(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Config(Formula v) => Arr(v, F.Id("L"));
    private static Formula Mat(Formula v) => Call("Matrix", Config(v), Config(v), Complex());
    private static Formula Member(Formula v, Formula j) => Seq(v, Sp, InMacro, Sp, j);
    private static Formula Retained() => Seq(OpenBrace, F.Id("v"), Colon, F.Id("V"), Mid, Sp, new Formula.Not(Member(F.Id("v"), F.Id("J"))), CloseBrace);
    private static Formula Val(Formula x) => Call("val", x);
    private static Formula Instances(string name, Formula body, bool finite) => finite
        ? Seq(OpenBracket, Call("Fintype", F.Id(name)), CloseBracket, Sp, OpenBracket, Call("DecidableEq", F.Id(name)), CloseBracket, Comma, Sp, body)
        : Seq(OpenBracket, Call("DecidableEq", F.Id(name)), CloseBracket, Comma, Sp, body);
    private static Formula Context(Formula body) => All("V", F.Id("Type"), All("L", F.Id("Type"), Instances("V", Instances("L", body, true), true)));
    private static Formula DensityPsdFormula() => All("L", F.Id("Type"), Instances("L",
        All("sigma", Call("DensityState", F.Id("L")),
            Qualified("Matrix", "PosSemidef", Apply(
                Seq(Operatorname, Grp(F.Id("CStarMatrix"), Dot, F.Id("ofMatrix"), Dot, F.Id("symm"))),
                Val(F.Id("sigma"))))), true));
    private static Formula SumOver(string name, Formula type, Formula body) => Seq(new Formula.Subscript(Sum, Seq(F.Id(name), Colon, type)), Sp, Parenthesized(body));
    private static Formula ProductOver(string name, Formula type, Formula body) => Seq(new Formula.Subscript(Prod, Seq(F.Id(name), Colon, type)), Sp, Parenthesized(body));

    private static Formula JoinFormula()
    {
        Formula v = F.Id("v"), j = F.Id("J"), h = F.Id("h");
        Formula pair = Seq(Langle, Sp, v, Comma, h, Rangle);
        Formula cond = Member(v, j);
        Formula rhs = Call("dite", cond, Lam("h", cond, Apply(F.Id("z"), pair)), Lam("h", new Formula.Not(cond), Apply(F.Id("x"), pair)));
        return Disp(All("V", F.Id("Type"), All("L", F.Id("Type"), Instances("V",
            All("J", Call("Finset", F.Id("V")), All("z", Config(j), All("x", Config(Retained()), All("v", F.Id("V"),
                Eqn(Call("joinLocal", j, F.Id("z"), F.Id("x"), v), rhs))))), false))));
    }
    private static Formula TraceFormula()
    {
        Formula j = F.Id("J"), rho = F.Id("rho");
        Formula qtype = Seq(Parenthesized(Config(j)), Sp, Times, Sp, Parenthesized(Config(Retained())));
        Formula f = Lam("q", qtype, Call("joinLocal", j, Qualified("Prod", "fst", F.Id("q")), Qualified("Prod", "snd", F.Id("q"))));
        return Disp(Context(All("rho", Mat(F.Id("V")), All("J", Call("Finset", F.Id("V")),
            Eqn(Call("partialTraceLocal", rho, j), Call("partialTraceFirst", Qualified("Matrix", "submatrix", rho, f, f)))))));
    }
    private static Formula SeparableFormula()
    {
        Formula v = F.Id("V"), rho = F.Id("rho"), k = F.Id("k"), p = F.Id("p"), j = F.Id("j");
        Formula entry = Mul(Qualified("Complex", "ofReal", Apply(p, j)), ProductOver("v", v,
            Apply(Val(Apply(F.Id("sigma"), j, F.Id("v"))), Apply(F.Id("x"), F.Id("v")), Apply(F.Id("y"), F.Id("v")))));
        Formula eq = All("x", Config(v), All("y", Config(v), Eqn(Apply(rho, F.Id("x"), F.Id("y")), SumOver("j", Call("Fin", k), entry))));
        Formula body = Ex("k", Nat(), Ex("p", Arr(Call("Fin", k), Real()), Ex("sigma", Arr(Call("Fin", k), Arr(v, Call("DensityState", F.Id("L")))),
            And(All("j", Call("Fin", k), Leq(D(0), Apply(p, j))), And(Eqn(SumOver("j", Call("Fin", k), Apply(p, j)), D(1)), eq)))));
        return Disp(Context(All("rho", Mat(v), IffTo(Call("IsFullySeparableLocal", rho), body))));
    }
    private static Formula ExchangeFormula()
    {
        Formula rho = F.Id("rho"), x = F.Id("x"), y = F.Id("y"), i = F.Id("i");
        Formula u = Qualified("Function", "update", x, i, Apply(y, i));
        return Disp(Context(All("rho", Mat(F.Id("V")), All("x", Config(F.Id("V")), All("y", Config(F.Id("V")), All("i", F.Id("V"),
            Imp(Call("IsFullySeparableLocal", rho), Imp(Eqn(Apply(rho, u, u), D(0)), Eqn(Apply(rho, x, y), D(0))))))))));
    }
}

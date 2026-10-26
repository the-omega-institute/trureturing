using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class JohnsonWakefieldRankThreeMoebiusDocument : IScribeDocumentDefinition
{
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/FiniteGeometry/johnsonwakefield2024incidencenearring");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "No finite rank-three nonmodular matroid has zero J-Möbius evaluation at minus one.",
        H("Johnson–Wakefield Question 6.19"), Blocks(
            Node("Flats", MatroidScoped(Equal(Call("Flats", V("M")),
                Call("Subtype", Lam("F", Call("Set", V("A")), App(Q("M", "IsFlat"), V("F")))))),
                AssessedProvenance.FromLiterature(Source),
                "The lattice L(M) consists of the flats of M, ordered by inclusion. A flat is Mathlib's Matroid.IsFlat; the subtype retains this predicate.", DescribeRole.Definition),
            Node("rk", MatroidScoped(All("F", Call("Set", V("A")),
                Equal(Call("rk", V("M"), V("F")), App(Q("ENat", "toNat"), App(Q("M", "eRk"), V("F")))))),
                AssessedProvenance.FromLiterature(Source),
                "The natural-number rank is ENat.toNat of Matroid.eRk. The theorem concerns finite carriers, so all these extended ranks are finite.", DescribeRole.Definition),
            Node("IsJFunction", MatroidScoped(All("J", JType(),
                IffFormula(Call("IsJFunction", V("M"), V("J")), JBody()))),
                AssessedProvenance.FromLiterature(Source),
                "Page 11, Definition 5.1: “Define J : Fl_3(P) → Z for all fixed (x, y, z) ∈ Fl_3(P) by Σ_{(a,b)⊴(x,y,z)} J(a, y, b) = δ_3(x, y, z).” Section 3 states: “(a, b) ⊴ (x, y, z) means x ≤ a ≤ y ≤ b ≤ z in P.” The proof-indexed finsums impose precisely these inequalities; ite is one at x = y = z and zero otherwise. Values away from partial flags are irrelevant.", DescribeRole.Definition),
            Node("MoebiusPoly", MatroidScoped(All("J", JType(),
                Equal(Call("MoebiusPoly", V("M"), V("J")), PolynomialBody()))),
                AssessedProvenance.FromLiterature(Source),
                "Page 14, Definition 6.2: “Let P be a ranked finite poset and for (x, y, z) ∈ Fl_3(P) let ρ(x, y, z) = 3rk(P) − rk(x) − rk(y) − rk(z). The J-Möbius polynomial of P is M(P, t) = Σ_{(x,y,z)∈Fl_3(P)} J(x, y, z)t^{ρ(x,y,z)}.” Here P is Flats M, its top rank is rk M M.E, and the coefficient ring is ℤ. Subtractions in the exponent are natural-number subtractions; for the finite matroids in the theorem, rank bounds prevent truncation on flags.", DescribeRole.Definition),
            Node("Connected", MatroidScoped(IffFormula(Call("Connected", V("M")), ConnectedBody())),
                AssessedProvenance.FromLiterature(Source),
                "Every two distinct ground elements belong to a common circuit. This is the connectedness hypothesis of Question 6.19; the nonvanishing argument also applies when this hypothesis is omitted.", DescribeRole.Definition),
            Node("Modular", MatroidScoped(IffFormula(Call("Modular", V("M")), ModularBody())),
                AssessedProvenance.FromLiterature(Source),
                "Every pair of flats satisfies r(F) + r(G) = r(F ∪ G) + r(F ∩ G). Ranks in this equality are the extended natural Matroid.eRk values. Disjoint rank-two flats in the proof have a rank-zero intersection, which may contain loops.", DescribeRole.Definition),
            Node("claim", IffFormula(V("claim"), ClaimBody()), AssessedProvenance.FromLiterature(Source),
                "Page 20, Question 6.19: “Is there a rank 3 non-modular connected matroid M such that M(M, −1) = 0?” The proposition is its negative answer for finite matroids: every function satisfying Definition 5.1 has nonzero evaluation. The carrier is a finite Type, and rank three is M.eRank = 3.", DescribeRole.Definition),
            Node("result", ClaimBody(), AssessedProvenance.FromRepo(Source),
                "The identity at minus one is twice the difference between the numbers of rank-two and rank-one flats. A nonmodular rank-three matroid has two lines whose intersection has rank zero. The finite configuration theorem gives at least as many lines as points. Its equality case forces every pair of distinct lines to meet in a point, contradicting the rank-zero intersection; therefore there are strictly more lines than points. The J function exists as the product of ordinary Möbius values and is unique on flags. Connectedness is unnecessary. No assertion about the classification in arbitrary rank is made.", DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("johnson-wakefield-2022-rank-three-moebius-question-6-19"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, Formula formula, AssessedProvenance provenance, string prose, DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Combinatorics/Matroids/JohnsonWakefieldRankThreeMoebius." + name),
            H(name), StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role, resolution);
    private static Formula ConnectedBody()
    {
        var circuit = Some("C", Call("Set", V("A")), And(App(Q("M", "IsCircuit"), V("C")), And(Member(V("e"), V("C")), Member(V("f"), V("C")))));
        return All("e", V("A"), Imp(Member(V("e"), Q("M", "E")),
            All("f", V("A"), Imp(Member(V("f"), Q("M", "E")), Imp(Ne(V("e"), V("f")), circuit)))));
    }
    private static Formula ModularBody()
    {
        var union = App(Q("Set", "union"), V("F"), V("G"));
        var inter = App(Q("Set", "inter"), V("F"), V("G"));
        var equality = Equal(Add(ERank(V("F")), ERank(V("G"))), Add(ERank(union), ERank(inter)));
        return All("F", Call("Set", V("A")), All("G", Call("Set", V("A")),
            Imp(App(Q("M", "IsFlat"), V("F")), Imp(App(Q("M", "IsFlat"), V("G")), equality))));
    }
    private static Formula ClaimBody()
    {
        var evaluation = App(Q("Polynomial", "eval"), NegOne(), Call("MoebiusPoly", V("M"), V("J")));
        var answer = All("J", JType(), Imp(Call("IsJFunction", V("M"), V("J")), Ne(evaluation, D(0))));
        answer = Imp(Not(Call("Modular", V("M"))), answer);
        answer = Imp(Call("Connected", V("M")), answer);
        answer = Imp(Equal(Q("M", "eRank"), D(3)), answer);
        return All("A", V("Type"), Seq(Instance("Finite", V("A")), Sp, All("M", Call("Matroid", V("A")), answer)));
    }
    private static Formula JBody()
    {
        var value = Call("J", V("a"), V("y"), V("b"));
        var right = FSum("b", FlatType(), FSumGuard(And(LeFormula(V("y"), V("b")), LeFormula(V("b"), V("z"))), value));
        var left = FSum("a", FlatType(), FSumGuard(And(LeFormula(V("x"), V("a")), LeFormula(V("a"), V("y"))), right));
        var equation = Equal(left, Call("ite", And(Equal(V("x"), V("y")), Equal(V("y"), V("z"))), D(1), D(0)));
        return All("x", FlatType(), All("y", FlatType(), All("z", FlatType(),
            Imp(LeFormula(V("x"), V("y")), Imp(LeFormula(V("y"), V("z")), equation)))));
    }
    private static Formula PolynomialBody()
    {
        var exponent = Multiply(D(3), Call("rk", V("M"), Q("M", "E")));
        exponent = Subtract(exponent, Call("rk", V("M"), Call("val", V("x"))));
        exponent = Subtract(exponent, Call("rk", V("M"), Call("val", V("y"))));
        exponent = Subtract(exponent, Call("rk", V("M"), Call("val", V("z"))));
        var term = Multiply(App(Q("Polynomial", "C"), Call("J", V("x"), V("y"), V("z"))), new Formula.Power(Q("Polynomial", "X"), exponent));
        return FSum("x", FlatType(), FSum("y", FlatType(), FSum("z", FlatType(),
            FSumGuard(And(LeFormula(V("x"), V("y")), LeFormula(V("y"), V("z"))), term))));
    }
    private static Formula ERank(Formula set) => App(Q("M", "eRk"), set);
    private static Formula MatroidScoped(Formula body) => All("A", V("Type"), All("M", Call("Matroid", V("A")), body));
    private static Formula FlatType() => Call("Flats", V("M"));
    private static Formula JType() => Arrow(FlatType(), Arrow(FlatType(), Arrow(FlatType(), Integer)));
    private static Formula FSum(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(new Formula.Power(Sum, V("f")), Parenthesized(Seq(V(name), Colon, Sp, type))), Sp, Parenthesized(body));
    private static Formula FSumGuard(Formula condition, Formula body) =>
        Seq(new Formula.Subscript(new Formula.Power(Sum, V("f")), Parenthesized(condition)), Sp, Parenthesized(body));
    private static Formula V(string name) => F.Id(name);
    private static Formula Integer => Seq(Mathbb, Grp(V("Z")));
    private static Formula NegOne() => Parenthesized(Seq(Minus, D(1)));
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(V(name), args);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) => Seq(Exists, Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Lam(string name, Formula type, Formula body) => Parenthesized(Seq(V(name), Colon, Sp, type, Sp, Mapsto, Sp, body));
    private static Formula Instance(string name, Formula type) => Seq(OpenBracket, Call(name, type), CloseBracket);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula IffFormula(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Not(Formula a) => Seq(Neg, Sp, Parenthesized(a));
    private static Formula LeFormula(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
}

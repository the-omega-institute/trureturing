using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class SvininDiscretePolynomialIdentityDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/Algebraic/SvininDiscretePolynomialIdentity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/svinin2015discrete");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Svinin's discrete-polynomial convolution identity holds over every commutative ring.",
        H("Svinin's Discrete-Polynomial Identity"),
        Blocks(
            Paragraph(Text(
                "The field T(i) in Svinin's paper is an arbitrary function u from the integers "
                    + "to a commutative ring R. Section 3 fixes (h,n)=(1,1). The finite maps "
                    + "lambda:Fin(r) to Fin(Int.toNat(s)) enumerate the increasing or weakly "
                    + "increasing tuples, with indices starting at zero. A product over Fin(0) "
                    + "is one. For positive degree a nonpositive subscript gives an empty sum. "
                    + "Natural subtraction in degree indices and finite-range lengths is truncated "
                    + "at zero; subscript and lattice arithmetic takes place in the integers. "
                    + "The displayed integer casts include the coercions from Fin through val.")),
            Node("T", "Strictly increasing tuple polynomials", TFormula(),
                "Page 3, Eq. (4): \"T^r_s(i) := Σ_{{λ_j}∈D_{r,s}} T(i + λ_1h)T(i + λ_2h + n) ⋯ T(i + λ_rh + (r − 1)n) with D_{r,s} := {λ_j : 0 ≤ λ_1 < ⋯ < λ_r ≤ s − 1} … we put T^0_s(i) ≡ 1.\" "
                    + "Here h=n=1, u is the paper's field T, and a:Fin(r) is its factor index minus one.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("S", "Weakly increasing tuple polynomials", SFormula(),
                "Page 5, Section 2.3: \"S^r_s(i) := Σ_{{λ_j}∈B_{r,s}} T(i + λ_1h + (k − 1)n) ⋯ T(i + λ_{r−1}h + n)T(i + λ_rh) … B_{r,s} ≡ {λ_j : 0 ≤ λ_1 ≤ ⋯ ≤ λ_r ≤ s − 1}.\" "
                    + "The printed k in the first offset is read as r, as determined by the displayed factor pattern and recurrences (10)–(11). "
                    + "With h=n=1 the offset at zero-based factor a is r−1−a in the integers.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("bracket", "The alternating binary operation", BracketFormula(),
                "Page 12, Section 3.4: \"⟨F, G⟩^r_s(i) = Σ_{j=0}^{r} (−1)^j F^{r−j}_{s+j}(i) G^j_{s−r+j}(i + r − j). Remark that in this formula we put F^r_s(i) ≡ 0 for s ≤ 0.\" "
                    + "The sum uses Finset.range(r+1). For the polynomial families T and S, the zero-degree value stays one, including at nonpositive subscripts, while positive degrees vanish there.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 1, Eq. (48)",
                Disp(Seq(Named("claim"), Sp, Iff, Sp, Parenthesized(ClaimBody()))),
                "Page 12, Conjecture 1: \"The relations ⟨S, T⟩^r_s(i) = Σ_{j=0}^{r−2} (−1)^j T(i + r − j − 2)T(i + s + j) × S^{r−j−2}_{s+j+2}(i) T^j_{s−r+j}(i + r − j), ∀ s ≥ r − 1 (48) are identities. Unfortunately, by now we can prove this conjecture only for r = 1, 2, 3.\" "
                    + "The formula quantifies every commutative ring, every field u, every natural r≥1, and all integer s≥r−1 and i. "
                    + "For r=1 the right side is empty. Completeness of the literature search is ASSUMED-UNVERIFIED.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The identity in every degree", Disp(ClaimBody()),
                "The weighted tuple partitions give the left Pascal recurrences; reversal gives their right counterparts. "
                    + "Subtracting the quadratic correction from S produces a polynomial Q whose convolution with T "
                    + "is invariant under (s,i)↦(s−1,i+1). At s=r−1 all positive-degree T factors vanish. "
                    + "The remaining Q depends on a finite window and is invariant under translation for every field. "
                    + "A field cut off beyond that window agrees with zero on a disjoint translated window, so Q equals zero. "
                    + "Induction on s−r+1 and expansion of the correction prove the displayed identity. "
                    + "No division or nonzero field value is required; commutative rings with zero divisors are included. "
                    + "This proves the prerequisite used by the paper's later difference-equation equivalences for (h,n)=(1,1); "
                    + "those equivalences and their other hypotheses are separate statements. General coprime (h,n) and noncommutative coefficients remain open here.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("svinin-2015-discrete-polynomial-identity"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
            DescribeId.Create("svinin48-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) =>
        Seq(Named(owner), Dot, Named(name));
    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => App(Named(name), arguments);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Z() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula RingContext(Formula body) => All("R", Named("Type"),
        Seq(OpenBracket, Call("CommRing", F.Id("R")), CloseBracket, Comma, Sp, body));
    private static Formula Eqn(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula ZCast(Formula value) => Parenthesized(Seq(value, Colon, Sp, Z()));
    private static Formula SumRange(Formula size, Formula body) => Seq(
        new Formula.Subscript(F.Sum, Seq(F.Id("j"), Sp, InMacro, Sp,
            App(Qualified("Finset", "range"), size))), Sp, Parenthesized(body));
    private static Formula TuplesFormula(string name, string order, bool reverse)
    {
        var r = F.Id("r");
        var s = F.Id("s");
        var i = F.Id("i");
        var u = F.Id("u");
        var a = F.Id("a");
        var lam = F.Id("lam");
        var finr = Call("Fin", r);
        var fins = Call("Fin", App(Qualified("Int", "toNat"), s));
        var tuples = Parenthesized(Seq(Qualified("Finset", "univ"), Colon, Sp,
            Call("Finset", Parenthesized(Arrow(finr, fins)))));
        var filtered = App(Qualified("Finset", "filter"), Named(order), tuples);
        var offset = reverse ? Sub(Sub(ZCast(r), D(1)), ZCast(Call("val", a))) : ZCast(Call("val", a));
        var argument = Add(Add(i, ZCast(Call("val", App(lam, a)))), reverse ? Parenthesized(offset) : offset);
        var product = Seq(new Formula.Subscript(F.Prod, Seq(a, Colon, Sp, finr)), Sp, App(u, argument));
        var sum = Seq(new Formula.Subscript(F.Sum, Seq(lam, Sp, InMacro, Sp, filtered)),
            Sp, Parenthesized(product));
        return Disp(RingContext(All("u", Arrow(Z(), F.Id("R")), All("r", N(),
            All("s", Z(), All("i", Z(), Eqn(Call(name, u, r, s, i), sum)))))));
    }
    private static Formula TFormula() => TuplesFormula("T", "StrictMono", false);
    private static Formula SFormula() => TuplesFormula("S", "Monotone", true);
    private static Formula BracketFormula()
    {
        var r = F.Id("r");
        var s = F.Id("s");
        var i = F.Id("i");
        var j = F.Id("j");
        var family = Arrow(N(), Arrow(Z(), Arrow(Z(), F.Id("R"))));
        var summand = Mul(Mul(new Formula.Power(new Formula.Negate(D(1)), j),
            App(F.Id("F"), Sub(r, j), Add(s, ZCast(j)), i)),
            App(F.Id("G"), j, Add(Sub(s, ZCast(r)), ZCast(j)), Sub(Add(i, ZCast(r)), ZCast(j))));
        return Disp(RingContext(All("F", family, All("G", family, All("r", N(),
            All("s", Z(), All("i", Z(), Eqn(Call("bracket", F.Id("F"), F.Id("G"), r, s, i),
                SumRange(Add(r, D(1)), summand)))))))));
    }
    private static Formula ClaimBody()
    {
        var r = F.Id("r");
        var s = F.Id("s");
        var i = F.Id("i");
        var j = F.Id("j");
        var u = F.Id("u");
        var summand = Mul(Mul(Mul(Mul(new Formula.Power(new Formula.Negate(D(1)), j),
            App(u, Sub(Sub(Add(i, ZCast(r)), ZCast(j)), D(2)))),
            App(u, Add(Add(i, s), ZCast(j)))),
            Call("S", u, Sub(Sub(r, j), D(2)), Add(Add(s, ZCast(j)), D(2)), i)),
            Call("T", u, j, Add(Sub(s, ZCast(r)), ZCast(j)), Sub(Add(i, ZCast(r)), ZCast(j))));
        var equality = Eqn(Call("bracket", Call("S", u), Call("T", u), r, s, i),
            SumRange(Sub(r, D(1)), summand));
        return RingContext(All("u", Arrow(Z(), F.Id("R")), All("r", N(),
            Seq(Parenthesized(Le(D(1), r)), Sp, Implies, Sp,
                Parenthesized(All("s", Z(), Seq(Parenthesized(Le(Sub(ZCast(r), D(1)), s)), Sp,
                    Implies, Sp, Parenthesized(All("i", Z(), equality)))))))));
    }
}

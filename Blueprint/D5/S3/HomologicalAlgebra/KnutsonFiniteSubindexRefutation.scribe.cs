using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra;

internal sealed class KnutsonFiniteSubindexRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/HomologicalAlgebra/KnutsonFiniteSubindexRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HomologicalAlgebra/johnston2025knutson");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A rank-five commutative ring has no finite subset that computes all its Knutson indices.",
        H("A negative answer to the finite-subindex question"),
        Blocks(
            Node("IsRegularElement", "Regular elements", RegularFormula(),
                "Section 2, p. 4794: “We call an element r ∈ R regular if α(r) ≠ 0 and x·r = α(x) r for all x ∈ R.” Here R is a commutative ring, α is a unital ring homomorphism to ℤ, and the right-hand side uses integer scalar multiplication. This meaning of regular is specific to the source.",
                AssessedProvenance.FromLiterature(Source)),
            Node("knutsonIndex", "The Knutson index", IndexFormula(),
                "Definition 2.1, p. 4794: “The Knutson Index 𝒦_r(x) of an element x ∈ R with respect to a regular element r ∈ R is the non-negative integer m such that Rx ∩ ℤr = mℤr.” The display gives the least positive coefficient of r in Rx, and zero if no positive coefficient occurs; sInf on ℕ has that empty-set value. For regular r this agrees with the generator in the quoted definition, since r has infinite additive order and the coefficient set is an ideal of ℤ. The natural coefficient is explicitly cast to ℤ before scalar multiplication.",
                AssessedProvenance.FromLiterature(Source)),
            Node("eligible", "Eligible multipliers", EligibleFormula(),
                "Definition 2.2, p. 4794: “Let S ⊂ R be a subset, and for any x ∈ R define S(x) = {s ∈ S: s·x ∈ ℤr}.” Finset represents the finite subset S. Membership in ℤr is the existence of an integer m with s * x = m • r.",
                AssessedProvenance.FromLiterature(Source)),
            Node("eligibleIndex", "The integer coefficient", EligibleIndexFormula(),
                "Definition 2.2, p. 4794, states: “Associated to S(x) we also set Ind(x) = {m ∈ ℤ: s·x = m·r for s ∈ S(x)}.” The displayed dependent conditional chooses that integer when it exists and returns zero otherwise. For a regular r it is unique, because applying α to m • r and using α(r) ≠ 0 proves injectivity of the integer coefficient. The variable h is the existence proof used by Exists.choose.",
                AssessedProvenance.FromLiterature(Source)),
            Node("knutsonSubindex", "The finite-set subindex", SubindexFormula(),
                "Definition 2.2, p. 4794, states: “Define the Knutson S-subindex of x ∈ R with respect to the regular element r ∈ R as 𝒦_r^S(x) := gcd(Ind(x)).” It adds: “By convention, if S(x) = ∅ then we set 𝒦_r^S(x) = ∞.” The gcd is taken on the natural absolute values of all eligible integer coefficients and cast to ℕ∞. An empty eligible set gives ⊤, the infinity of ℕ∞. The finite-set gcd includes zero coefficients without changing a nonzero gcd.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Question 2.5", Disp(ClaimBody()),
                "Question 2.5, p. 4795: “Does there exist a finite subset S ⊂ R such that for all x ∈ R we have 𝒦_r(x) = 𝒦_r^S(x)?” Section 2, p. 4794, begins: “Let R be a finitely generated commutative ring. Suppose that R is equipped with a ring homomorphism α: R → ℤ.” The proposition is the affirmative answer for every ring in that setting and every regular r. Algebra.FiniteType ℤ R expresses finite generation as a commutative ring. Both instance parameters are displayed anonymously. The ordinary index is cast from ℕ to ℕ∞ for the comparison.",
                AssessedProvenance.FromLiterature(Source)),
            Node("result", "No finite subset suffices in general", Disp(Seq(F.Neg, Parenthesized(ClaimBody()))),
                "Use a ring whose elements are integer tuples (d,a,b,f,t), with augmentation d + 2a + 2b + 4t. Its multiplication is the coordinate multiplication of the fiber product of ℤ and ℤ[u,v]/(u²,v²) over ℤ/4, where u and v map to 2. The tuple r = (0,0,0,0,1) is regular and has augmentation 4. For every integer k, X(k) = (0,1,2k,0,−k) and Y(k) = (0,1,−2k,0,k) multiply to r, so X(k) has Knutson index one. Given a finite S, choose k = 1 + ∑(s ∈ S) |s.b|. Eligibility of s forces s.d = 0 and s.b = −2k s.a. The bound on |s.b| forces s.a = s.b = 0, and the coefficient of r is then 2s.t, an even integer. The subindex is therefore divisible by two or infinite, so it differs from one. Proposition 2.6 still gives a finite subset for reduced rings. The source states that the rings in its subsequent applications embed in finite products of ℂ and hence are reduced; those applications retain that hypothesis.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("johnston-martin-duro-rumynin-2024-knutson-index-question-2-5"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance, DescribeRole role = DescribeRole.Definition,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("knutson-finite-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name) => Seq(Operatorname,
        Grp(Seq([.. name.Split('.').SelectMany((part, index) =>
            index == 0 ? new[] { F.Id(part) } : new[] { Dot, F.Id(part) })])));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula All(Formula x, Formula type, Formula body) =>
        Seq(Forall, Sp, x, Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(Formula x, Formula type, Formula body) =>
        Seq(Exists, Sp, x, Colon, Sp, type, Comma, Sp, body);
    private static Formula Equal(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula And(Formula x, Formula y) =>
        new Formula.Logic(Parenthesized(x), FormulaLogicOperator.And, Parenthesized(y));
    private static Formula Arrow(Formula x, Formula y) =>
        new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Implies, Parenthesized(y));
    private static Formula Ints() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Nats() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula ENats() => new Formula.Power(Nats(), Infty);
    private static Formula Cast(Formula x, Formula type) => Parenthesized(Seq(x, Colon, Sp, type));
    private static Formula Lam(Formula x, Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, x, Colon, Sp, type, Comma, Sp, body));
    private static Formula RingParameters(Formula rType, Formula body) =>
        All(rType, Named("Type"), Seq(OpenBracket, Call("CommRing", rType), CloseBracket, Comma, Sp, body));
    private static Formula Scalar(Formula m, Formula r) => Call("SMul.smul", m, r);
    private static Formula EligibleCondition(Formula r, Formula s, Formula x) =>
        Some(F.Id("m"), Ints(), Equal(new Formula.Binary(s, FormulaBinaryOperator.Multiply, x), Scalar(F.Id("m"), r)));

    private static Formula RegularFormula()
    {
        Formula rt = F.Id("R"), a = Alpha, r = F.Id("r"), x = F.Id("x");
        Formula condition = And(new Formula.Relation(App(a, r), FormulaRelationOperator.NotEqual, D(0)),
            All(x, rt, Equal(new Formula.Binary(x, FormulaBinaryOperator.Multiply, r), Scalar(App(a, x), r))));
        return Disp(RingParameters(rt, All(a, Seq(rt, Sp, To, Plus, Star, Sp, Ints()),
            All(r, rt, Equal(Call("IsRegularElement", a, r), Parenthesized(condition))))));
    }

    private static Formula IndexFormula()
    {
        Formula rt = F.Id("R"), r = F.Id("r"), x = F.Id("x"), m = F.Id("m"), y = F.Id("y");
        Formula condition = And(new Formula.Relation(D(0), FormulaRelationOperator.LessThan, m),
            Some(y, rt, Equal(new Formula.Binary(y, FormulaBinaryOperator.Multiply, x), Scalar(Cast(m, Ints()), r))));
        Formula set = Seq(OpenBrace, m, Colon, Sp, Nats(), Sp, Mid, Sp, condition, CloseBrace);
        return Disp(RingParameters(rt, All(r, rt, All(x, rt,
            Equal(Call("knutsonIndex", r, x), Call("sInf", set))))));
    }

    private static Formula EligibleFormula()
    {
        Formula rt = F.Id("R"), r = F.Id("r"), s = F.Id("s"), x = F.Id("x"), set = F.Id("S");
        return Disp(RingParameters(rt, All(r, rt, All(set, Call("Finset", rt), All(x, rt,
            Equal(Call("eligible", r, set, x), Call("Finset.filter", Lam(s, rt, EligibleCondition(r, s, x)), set)))))));
    }

    private static Formula EligibleIndexFormula()
    {
        Formula rt = F.Id("R"), r = F.Id("r"), s = F.Id("s"), x = F.Id("x"), h = F.Id("h");
        Formula conditional = Seq(Named("if"), Sp, h, Colon, Sp, Parenthesized(EligibleCondition(r, s, x)), Sp,
            Named("then"), Sp, Call("Exists.choose", h), Sp, Named("else"), Sp, D(0));
        return Disp(RingParameters(rt, All(r, rt, All(s, rt, All(x, rt,
            Equal(Call("eligibleIndex", r, s, x), Parenthesized(conditional)))))));
    }

    private static Formula SubindexFormula()
    {
        Formula rt = F.Id("R"), r = F.Id("r"), set = F.Id("S"), x = F.Id("x"), s = F.Id("s");
        Formula eligible = Call("eligible", r, set, x);
        Formula gcd = Call("Finset.gcd", eligible, Lam(s, rt, Call("Int.natAbs", Call("eligibleIndex", r, s, x))));
        Formula conditional = Call("ite", Call("Finset.Nonempty", eligible), Cast(Cast(gcd, Nats()), ENats()), Infty);
        return Disp(RingParameters(rt, All(r, rt, All(set, Call("Finset", rt), All(x, rt,
            Equal(Call("knutsonSubindex", r, set, x), conditional))))));
    }

    private static Formula ClaimBody()
    {
        Formula rt = F.Id("R"), a = Alpha, r = F.Id("r"), set = F.Id("S"), x = F.Id("x");
        Formula equality = Equal(Cast(Call("knutsonIndex", r, x), ENats()), Call("knutsonSubindex", r, set, x));
        return RingParameters(rt, Seq(OpenBracket, Call("Algebra.FiniteType", Ints(), rt), CloseBracket, Comma, Sp,
            All(a, Seq(rt, Sp, To, Plus, Star, Sp, Ints()), All(r, rt,
                Arrow(Call("IsRegularElement", a, r), Some(set, Call("Finset", rt), All(x, rt, equality)))))));
    }
}

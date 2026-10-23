using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class VariableExponentHornichHlawkaDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/VariableExponentHornichHlawka.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Geometry/marinescuniculescu2024survey");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A two-valued variable exponent gives a Luxemburg norm violating the Hornich–Hlawka inequality.",
        H("Variable-exponent Hornich–Hlawka refutation"),
        Blocks(
            SourceQuotation(),
            Entry("modular", "modular", "The variable-exponent modular", Modular(),
                "For real functions p and f and a real scale lam, modular is the Lebesgue lower integral "
                + "on (0,1) of ENNReal.ofReal (|f(t)/lam| raised to p(t)). Its values are extended nonnegative reals. "
                + "The scale is restricted to positive values in the norm and membership definitions.",
                DescribeRole.Definition, true),
            Entry("luxemburg-norm", "luxNorm", "The Luxemburg norm", Luxemburg(),
                "The real infimum is taken over positive scales with modular at most one. "
                + "Functions are represented on the real line, with the integral restricted to (0,1). "
                + "The definition is the Luxemburg norm on the variable-exponent space, "
                + "using the convention of Diening, Harjulehto, Hästö and Ruzicka cited in §3 of the survey.",
                DescribeRole.Definition, true),
            Entry("membership", "InLp", "Variable-exponent membership", Membership(),
                "InLp p f requires measurability of the representative on the real line and a positive scale "
                + "at which the modular is at most one. For exponents bounded between one and two, "
                + "this is the scaled-modular membership condition. The counterexample functions satisfy "
                + "global measurability and therefore give measurable representatives on (0,1).",
                DescribeRole.Definition, true),
            Entry("hornich-hlawka-claim", "claim", "The universal Hornich–Hlawka claim", Claim(),
                "The formal encoding of Problem 3 quantifies over measurable real exponents p with "
                + "1≤p(t)≤2 for t in (0,1), and every triple f, g, h satisfying InLp p. "
                + "It requires the sum of the three pair-sum Luxemburg norms to be at most the sum of "
                + "the three individual norms and the triple-sum norm. The definitions use representatives; "
                + "the integrals and strict violation depend only on their almost-everywhere classes. "
                + "For constant p in [1,2], the survey's isometric embedding into L¹ gives a positive answer.",
                DescribeRole.Definition, true),
            Entry("refutation", "result", "A two-valued exponent refutes the claim", Disp(Seq(Neg, Sp, V("claim"))),
                "Let p(t)=1 for t<1/2 and p(t)=2 otherwise. The private lemmas exponent_measurable "
                + "and exponent_range prove the hypotheses. For u=(a,b,c), let J(u) equal 4a on (0,1/4), "
                + "4b on [1/4,1/2), √2 c on [1/2,1), and zero elsewhere. "
                + "The lemma modular_J gives (|a|+|b|)/lam+c²/lam² at every positive scale. "
                + "Writing A=|a|+|b|, scale_iff identifies modular≤1 with "
                + "N(a,b,c)≤lam, where N=(A+√(A²+4c²))/2. The lemmas luxNorm_J and J_InLp "
                + "give this norm and membership whenever N>0. Take x=J(0,1,1/2), "
                + "y=J(0,−1,1/2), z=J(−1,0,−1/2). N_special gives "
                + "‖x‖=‖y‖=‖z‖=‖x+y+z‖=(1+√2)/2; J_add and pair_norms give "
                + "‖x+y‖=1 and ‖y+z‖=‖z+x‖=2. Since √2<3/2, the inequality would require "
                + "5≤2+2√2<5. This answers Problem 3 negatively. "
                + "As mathematical reasoning, J identifies a three-dimensional subspace with the Luxemburg "
                + "norm of |a|+|b|+c², a nonlinear mixture of an ℓ¹ and an ℓ² part; each part separately "
                + "embeds in L¹. A linear isometry and the norm axioms are not separately formalized. "
                + "Problem 4 for variable-exponent Sobolev spaces is unsettled for positive derivative order; "
                + "W⁰ is L, so order zero inherits the example. Continuous exponents, exponents close "
                + "to constant, and a classification of the Hornich–Hlawka exponents remain unsettled. "
                + "The journal full text is ASSUMED-UNVERIFIED. Persistence of the strict violation when "
                + "the two powers move slightly into (1,2) is also ASSUMED-UNVERIFIED: continuity of the "
                + "seven finite-sum modular unit levels gives the reasoning, but no perturbation theorem "
                + "or quantitative radius is formalized. The quotation refers to arXiv:2407.03278v1, §3, Problem 3.",
                DescribeRole.Theorem, false))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, DescribeRole role, bool literature) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role,
            name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("marinescu-niculescu-2024-variable-exponent-hornich-hlawka"),
                ResolutionKind.Refuted) : null);

    private static DocumentBlock SourceQuotation() => Paragraph(Text(
        "Marinescu and Niculescu, A survey of the Hornich-Hlawka inequality, arXiv:2407.03278v1, "
        + "§3, the paragraph introducing Problem 3 and Problem 3 itself, verbatim: “A natural generalization "
        + "of Lp spaces is provided by the class of Lp(·) spaces with variable exponent. They differ from the "
        + "classical Lp spaces in that the exponent p is not constant but a function from the measure space "
        + "under attention to [1, ∞]. See the monograph of L. Diening, P. Harjulehto, P. Hästö and M. Ruzicka "
        + "[6] for a thorough presentation. Problem 3. Is every Lp(·)(0, 1) space with a variable exponent "
        + "p(·) : (0, 1) → [1, 2] a Hornich-Hlawka space?”"));

    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Functions => Seq(Real, Sp, To, Sp, Real);
    private static Formula Interval => Parenthesized(Seq(D(0), Comma, Sp, D(1)));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Positive(Formula a) =>
        new Formula.Relation(D(0), FormulaRelationOperator.LessThan, a);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Norm(Formula f) => Call("luxNorm", V("p"), f);
    private static Formula UnitScale => And(Positive(V("lam")),
        Le(Call("modular", V("p"), V("f"), V("lam")), D(1)));

    private static Formula Modular()
    {
        Formula power = new Formula.Power(new Formula.Absolute(
            new Formula.Fraction(Call("f", V("t")), V("lam"))), Call("p", V("t")));
        Formula integral = Seq(Int, Caret, Grp(Minus), Underscore,
            Grp(V("t"), Sp, InMacro, Sp, Interval), Sp, Call("ofReal", power), Sp, V("dt"));
        return Disp(new Formula.Relation(Call("modular", V("p"), V("f"), V("lam")),
            FormulaRelationOperator.Equal, integral));
    }

    private static Formula Luxemburg() => Disp(new Formula.Relation(Norm(V("f")),
        FormulaRelationOperator.Equal, Call("sInf",
            Seq(OpenBrace, Sp, V("lam"), Colon, Sp, Real, Sp, Mid, Sp, UnitScale, Sp, CloseBrace))));

    private static Formula Membership() => Disp(new Formula.Logic(Call("InLp", V("p"), V("f")),
        FormulaLogicOperator.Iff, And(Call("Measurable", V("f")),
            Seq(Exists, Sp, V("lam"), Colon, Sp, Real, Comma, Sp, UnitScale))));

    private static Formula Claim()
    {
        Formula f = V("f"), g = V("g"), h = V("h");
        Formula inequality = Le(Add(Add(Norm(Add(f, g)), Norm(Add(g, h))), Norm(Add(h, f))),
            Add(Add(Add(Norm(f), Norm(g)), Norm(h)), Norm(Add(Add(f, g), h))));
        Formula triples = All("f", Functions, All("g", Functions, All("h", Functions,
            Imp(Call("InLp", V("p"), f), Imp(Call("InLp", V("p"), g),
                Imp(Call("InLp", V("p"), h), inequality))))));
        Formula range = All("t", Real, Imp(new Formula.Relation(V("t"),
            FormulaRelationOperator.MemberOf, Interval),
            And(Le(D(1), Call("p", V("t"))), Le(Call("p", V("t")), D(2)))));
        Formula body = All("p", Functions, Imp(Call("Measurable", V("p")), Imp(range, triples)));
        return Disp(new Formula.Logic(V("claim"), FormulaLogicOperator.Iff, Parenthesized(body)));
    }
}

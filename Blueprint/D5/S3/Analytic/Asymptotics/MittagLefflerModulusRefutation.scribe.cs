using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Asymptotics;

internal sealed class MittagLefflerModulusRefutationDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/AnalyticClosure/garrappa2025mittagmodulus");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite complex witness refutes the reverse Mittag-Leffler characterization.",
        H("The reverse Mittag-Leffler modulus characterization fails"),
        Blocks(
            Entry("ggps-source-series", "IsSourceSeries", "The convergent two-parameter series",
                SeriesFormula(), AssessedProvenance.FromLiterature(Source),
                "Page 1, equation (1.1): “In this paper we study several inequalities of the two-parameter Mittag-Leffler function Eα,β, which is defined on the complex plane for α > 0 and β ∈ ℝ by the series representation” Eα,β(z) = ∑ from k = 0 to infinity of z^k/Γ(αk+β), z ∈ ℂ. The formula uses HasSum, so convergence is part of the relation. Alpha and beta are real, z is complex, and k is natural. The value val(k,Real) is the natural-to-real coercion, and val(Real.Gamma(alpha*val(k,Real)+beta),Complex) embeds the denominator in the complex plane. Division is totalized at Gamma poles.",
                DescribeRole.Definition),
            Entry("ggps-reciprocal", "reciprocal", "The real reciprocal on the positive axis",
                ReciprocalFormula(), AssessedProvenance.FromLiterature(Source),
                "Page 18, Conjecture 25 uses “1/Eα,β(x)”. Here E is a real-real-complex-complex family and alpha, beta and x are real. The real part reads the real-valued series on real arguments, after embedding x in Complex.",
                DescribeRole.Definition),
            Entry("ggps-characterization", "claim", "Conjecture 25 in full",
                Equal(F.Id("claim"), ClaimBody()), AssessedProvenance.FromLiterature(Source),
                "Page 18: “Conjecture 25. For every α ∈ (1, 2), one has The inequality (1.4) holds globally ⇐⇒ β ∈ [α − 1, α] ⇐⇒ 1/Eα,β(x) is CM on (0, ∞).” Inequality (1.4) is |Eα,β(z)| ≥ Eα,β(Re z), and globally means every complex z. The parameter beta is nonnegative, as in the paper's inequality problem. The leading existential supplies the entire convergent family. The second conjunct expresses both equivalences for every such family. CompletelyMonotoneOn supplies smoothness and all nonnegative signed derivatives; the separate positivity clause preserves the positive codomain. The displayed val operations are the real-to-complex coercions.",
                DescribeRole.Definition),
            Entry("ggps-refutation", "result", "The characterization is false",
                Seq(Neg, Sp, Parenthesized(ClaimBody())), AssessedProvenance.FromRepo(Source),
                "At alpha = 3/2 and beta = 1/2, the interval condition holds. For z = −115+10i, the series instead satisfies norm(E(3/2,1/2,z)) < re(E(3/2,1/2,−115)). The 64-term sum on the real axis is greater than 3/100000, while the absolute real and imaginary parts at z are at most 1/1000000 and 1/100000. At either argument the omitted tail has norm at most 4/10^13. The series exists for every positive alpha and every real beta, including the reciprocal-Gamma pole values. The example refutes the implication from the parameter interval to the global reverse inequality. The all-alpha family, an interior-beta neighbourhood and a corrected universal region remain open here.",
                DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        AssessedProvenance provenance, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Analytic/Asymptotics/MittagLefflerModulusRefutation." + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula SeriesFormula()
    {
        Formula e = F.Id("E");
        Formula alpha = F.Id("alpha");
        Formula beta = F.Id("beta");
        Formula z = F.Id("z");
        Formula k = F.Id("k");
        Formula summand = new Formula.Fraction(new Formula.Power(z, k),
            Cast(App(Qualified("Real", "Gamma"), Add(Multiply(alpha, Cast(k, F.Id("Real"))), beta)),
                F.Id("Complex")));
        Formula sequence = Parenthesized(Seq(Parenthesized(Seq(k, Colon, Sp, F.Id("Nat"))),
            Sp, Mapsto, Sp, summand));
        Formula sums = All("beta", F.Id("Real"), All("z", F.Id("Complex"),
            Call("HasSum", sequence, App(e, alpha, beta, z))));
        Formula parameters = All("alpha", F.Id("Real"), Implies(Lt(Num(0), alpha), sums));
        return All("E", FamilyType(), Iff(Call("IsSourceSeries", e), parameters));
    }

    private static Formula ReciprocalFormula()
    {
        Formula e = F.Id("E");
        Formula alpha = F.Id("alpha");
        Formula beta = F.Id("beta");
        Formula x = F.Id("x");
        Formula value = App(Qualified("Complex", "re"),
            App(e, alpha, beta, Cast(x, F.Id("Complex"))));
        Formula equation = Equal(Call("reciprocal", e, alpha, beta, x),
            new Formula.Fraction(Num(1), value));
        return All("E", FamilyType(), All("alpha", F.Id("Real"),
            All("beta", F.Id("Real"), All("x", F.Id("Real"), equation))));
    }

    private static Formula ClaimBody()
    {
        Formula e = F.Id("E");
        Formula alpha = F.Id("alpha");
        Formula beta = F.Id("beta");
        Formula z = F.Id("z");
        Formula x = F.Id("x");
        Formula interval = And(Le(Subtract(alpha, Num(1)), beta), Le(beta, alpha));
        Formula global = All("z", F.Id("Complex"), Le(
            App(Qualified("Complex", "re"), App(e, alpha, beta,
                Cast(App(Qualified("Complex", "re"), z), F.Id("Complex")))),
            new Formula.Norm(App(e, alpha, beta, z))));
        Formula positive = All("x", F.Id("Real"), Implies(Lt(Num(0), x),
            Lt(Num(0), Call("reciprocal", e, alpha, beta, x))));
        Formula cm = App(Qualified("D5", "S3", "Analytic", "ExpRatioCM", "Defs", "CompletelyMonotoneOn"),
            App(F.Id("reciprocal"), e, alpha, beta));
        Formula equivalences = And(Iff(global, interval), Iff(interval, And(positive, cm)));
        Formula hypotheses = Implies(Lt(Num(1), alpha),
            Implies(Lt(alpha, Num(2)), Implies(Le(Num(0), beta), equivalences)));
        Formula parameters = All("alpha", F.Id("Real"), All("beta", F.Id("Real"), hypotheses));
        Formula family = All("E", FamilyType(), Implies(Call("IsSourceSeries", e), parameters));
        return And(new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("E"),
            FamilyType(), Call("IsSourceSeries", e)), family);
    }

    private static Formula FamilyType() => new Formula.TypeArrow(F.Id("Real"),
        new Formula.TypeArrow(F.Id("Real"), new Formula.TypeArrow(F.Id("Complex"), F.Id("Complex"))));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => App(F.Id(name), arguments);
    private static Formula Cast(Formula value, Formula type) => Call("val", value, type);
    private static Formula Qualified(params string[] names) =>
        Seq(names.SelectMany((name, index) => index == 0
            ? new[] { Operatorname, Grp(F.Id(name)) }
            : new[] { Dot, Operatorname, Grp(F.Id(name)) }).ToArray());
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
}

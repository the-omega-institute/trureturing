using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.SeriesInequalities;

internal sealed class KarpQuadraticTruncationsDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/SeriesInequalities/KarpQuadraticTruncations.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two quadratic truncations of the Karp-Zhang series have nonnegative generalized "
            + "Turan coefficients for every nonnegative real pair of shifts.",
        H("Karp-Zhang Quadratic Truncations"),
        Blocks(
            Paragraph(Text(
                "The two-term r = 3 polynomial and the quadratic with coefficients h0, h1*t and h2*t*(t+3)/2 are truncations of the multiple-Pochhammer series studied by Dmitrii Karp and Yi Zhang, "
                    + "Log-concavity and log-convexity of series containing multiple Pochhammer "
                    + "symbols, Fractional Calculus and Applied Analysis 27 (2024), 458-486, "
                    + "DOI 10.1007/s13540-023-00238-0. The results concern only the specified "
                    + "truncations of Conjectures 1 and 2, not either full series conjecture.")),
            Describe.Lean(
                DescribeId.Create("pochhammer-turan-nonneg"),
                DeclarationHandle.Create(Prefix + "pochhammer_turan_nonneg"),
                H("Nonnegative equal-degree Pochhammer difference"),
                StatementSource.FromAuthor(Disp(
                    All("n", F.Id("Nat"), All("mu", F.Id("Real"),
                        All("alpha", F.Id("Real"), All("beta", F.Id("Real"),
                            Implies(Lt(Num(0), F.Id("mu")),
                                Implies(Le(Num(0), F.Id("alpha")),
                                    Implies(Le(Num(0), F.Id("beta")),
                                        Le(Num(0), Subtract(
                                            Multiply(Poch(Add(F.Id("mu"), F.Id("alpha"))),
                                                Poch(Add(F.Id("mu"), F.Id("beta")))),
                                            Multiply(Poch(F.Id("mu")),
                                                Poch(Add(Add(F.Id("mu"), F.Id("alpha")), F.Id("beta"))))))))))))))),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Asymptotics/karpzhang2023pochhammer")),
                Blocks(Paragraph(Text(
                    "Equation (6), printed page 4 of arXiv:2305.09029v3: “Note that [log((µ)ₙᵣ)]″ = ψ′(µ + rn) − ψ′(µ) ≤ 0,” "
                        + "where ψ is the digamma function. This log-concavity gives the four-point form: "
                        + "the product at µ+α and µ+β dominates the product at µ and µ+α+β "
                        + "for a positive base and nonnegative shifts. For each degree at least two, "
                        + "take the source index to be one and its multiplier r to be the degree. "
                        + "Degree zero gives equality; degree one gives the difference αβ ≥ 0. "
                        + "Each Pochhammer symbol is Mathlib's ascending Pochhammer polynomial "
                        + "in degree n evaluated at its parameter."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("r2-polynomial"),
                DeclarationHandle.Create(Prefix + "r2Polynomial"),
                H("The two-term r = 3 polynomial"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The rising factorial is Mathlib's ascending Pochhammer polynomial evaluated "
                        + "at t. Only indices 1 and 2 are retained, with denominators 2! and 5!. "
                        + "The two weights can be any nonnegative real numbers."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("r3-polynomial"),
                DeclarationHandle.Create(Prefix + "r3Polynomial"),
                H("The truncation at k = 2"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The constant, linear and quadratic coefficients are respectively h0, h1*t "
                        + "and h2*t*(t+3)/2. The last expression is the k=2 Pochhammer quotient "
                        + "in the source series; no integer restriction is placed on t."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("r2-all-coefficients"),
                DeclarationHandle.Create(Prefix + "r2_coeff_nonneg"),
                H("Conjecture 1 for the two-term truncation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For nonnegative weights c1,c2, positive mu and arbitrary nonnegative real "
                        + "alpha and beta, every "
                        + "coefficient of F(mu+alpha)*F(mu+beta)-F(mu)*F(mu+alpha+beta) is "
                        + "nonnegative. The equal-index terms follow by factorwise comparison. "
                        + "The mixed (3,6) term is alpha*beta*(alpha+beta+2*mu+8) times a "
                        + "polynomial with positive coefficients in mu, alpha+beta, alpha*beta "
                        + "and (alpha-beta)^2; the identity is checked by the Lean kernel."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("r3-real-shifts"),
                DeclarationHandle.Create(Prefix + "r3_coeff_nonneg"),
                H("Conjecture 2 for three terms and real shifts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume h0,h1,h2 are nonnegative, h1^2 >= h0*h2, and mu is positive. "
                        + "For arbitrary nonnegative real alpha and beta, the degree-two "
                        + "Turan coefficient is alpha*beta*(h1^2-h0*h2). The degree-three "
                        + "coefficient is h1*h2*alpha*beta*(alpha+beta+2*mu+6)/2. The "
                        + "degree-four coefficient is h2^2*alpha*beta/4 times a polynomial "
                        + "with positive coefficients. All other coefficients vanish. The "
                        + "shifts are arbitrary nonnegative reals, extending the integer-shift "
                        + "scope of the paper's Theorem 3 for this truncation."))),
                DescribeRole.Theorem))));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Seq(Open, F.Id(name), Colon, Sp, type, Close), Comma, Sp, body);
    private static Formula Poch(Formula t) =>
        App(Qualified("Polynomial", "eval"), t,
            App(F.Id("ascPochhammer"), F.Id("Real"), F.Id("n")));
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
}

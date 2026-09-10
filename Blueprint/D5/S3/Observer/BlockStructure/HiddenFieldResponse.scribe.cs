using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.BlockStructure;

internal sealed class HiddenFieldResponseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/BlockStructure/HiddenFieldResponse.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact nonresonant hidden-field elimination and its leading-order coefficient companions.",
        H("Hidden Field Response"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solve-the-hidden-frequency-equation"),
                DeclarationHandle.Create(Prefix + "hidden_field_solve_eq"),
                H("Solve the hidden field"),
                StatementSource.FromAuthor(EliminationStatement(false)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The second frequency-domain Euler-Lagrange equation is an explicit premise. "
                    + "Its nonzero hidden coefficient permits division while retaining the full "
                    + "frequency and squared-wave-number dependence. The variational and Fourier "
                    + "steps leading to that equation are outside this formalization."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("exact-visible-schur-response"),
                DeclarationHandle.Create(Prefix + "hidden_field_schur_response"),
                H("Exact inverse response coefficient"),
                StatementSource.FromAuthor(EliminationStatement(true)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Substitution of hidden_field_solve_eq into the visible equation identifies "
                    + "the exact inverse response as the coefficient multiplying q. The identity "
                    + "also holds at q = 0; no cancellation by the visible amplitude is used."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("effective-speed-shift-companion"),
                DeclarationHandle.Create(Prefix + "c_eff_sq_sub_bare"),
                H("Companion: squared-speed shift"),
                StatementSource.FromAuthor(CoefficientStatement(false)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The shift is a nonnegative mixing weight times the difference of the "
                    + "two squared speeds. In particular, zero coupling gives zero shift."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("effective-speed-interval-companion"),
                DeclarationHandle.Create(Prefix + "c_eff_sq_bounds"),
                H("Companion: squared-speed interval"),
                StatementSource.FromAuthor(CoefficientStatement(true)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The weights are nonnegative and sum to one, placing the coefficient "
                    + "between the two squared speeds."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("principal-symbol-companion"),
                DeclarationHandle.Create(Prefix + "principal_symbol_eq_zero_iff"),
                H("Companion: characteristic locus"),
                StatementSource.FromAuthor(SymbolStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The equivalence rewrites the zero set of the normalized massless principal "
                    + "symbol as the leading-order dispersion relation."))),
                DescribeRole.Lemma),
            Paragraph(Text(
                "The source's physical model has positive gaps and a positive zero-momentum "
                + "restoring matrix. The coefficient interpretation requires its low-frequency "
                + "window; the total real expressions at a zero hidden gap carry no such claim. "
                + "No controlled expansion remainder or limiting PDE is certified here.")),
            Paragraph(Text(
                "The source does not resolve hidden resonance in this elimination. The explicit "
                + "nonzero-denominator hypothesis remains; totalized division supplies no physical "
                + "response at resonance. Changing the parameters can change the effective speed, "
                + "so there is no universal constant or identification with the full signal front.")),
            Paragraph(Text(
                "The parameter lam is solely the field coupling and is not identified with a "
                + "resource price. This quadratic classical calculation provides no Born rule, "
                + "quantum state, or thermal fluctuation distribution.")))));

    private static Formula EliminationStatement(bool schur)
    {
        Formula oh = F.Id("Oh"), ch = F.Id("ch"), k = F.Id("kSq"), omega = F.Id("omega");
        Formula lam = F.Id("lam"), q = F.Id("q"), r = F.Id("r");
        Formula hidden = Call("hiddenDen", oh, ch, k, omega);
        Formula premise = Seq(Open, hidden, Sp, Neq, Sp, D(0), Sp, Land, Sp,
            Add(Mul(lam, q), Mul(hidden, r)), Sp, Eq, Sp, D(0), Close);
        Formula result = Equal(r, Mul(Negative(Divide(lam, hidden)), q));
        string[] variables = ["Oh", "ch", "kSq", "omega", "lam", "q", "r"];
        if (schur)
        {
            Formula bare = Sub(Add(Square(F.Id("O0")), Mul(Square(F.Id("c0")), k)),
                Square(omega));
            result = Equal(Add(Mul(bare, q), Mul(lam, r)),
                Mul(Sub(bare, Divide(Square(lam), hidden)), q));
            variables = ["O0", "Oh", "c0", "ch", "kSq", "omega", "lam", "q", "r"];
        }
        return ForReals(variables, Seq(premise, Sp, Rightarrow, Sp, result));
    }

    private static Formula CoefficientStatement(bool bounds)
    {
        Formula c0 = F.Id("c0"), ch = F.Id("ch"), lam = F.Id("lam"), oh = F.Id("Oh");
        Formula speed = Call("cEffSq", c0, ch, lam, oh);
        Formula result = bounds
            ? Seq(Call("min", Square(c0), Square(ch)), Sp, Leq, Sp, speed,
                Sp, Land, Sp, speed, Sp, Leq, Sp, Call("max", Square(c0), Square(ch)))
            : Equal(Sub(speed, Square(c0)),
                Mul(Divide(Call("inertiaCorrection", lam, oh), Call("kineticCoeff", lam, oh)),
                    Sub(Square(ch), Square(c0))));
        return ForReals(["c0", "ch", "lam", "Oh"], result);
    }

    private static Formula SymbolStatement()
    {
        Formula c0 = F.Id("c0"), ch = F.Id("ch"), lam = F.Id("lam"), oh = F.Id("Oh");
        Formula k = F.Id("kSq"), omega = F.Id("omega");
        return ForReals(["c0", "ch", "lam", "Oh", "kSq", "omega"],
            Seq(Equal(Call("principalSymbol", c0, ch, lam, oh, k, omega), D(0)),
                Sp, Iff, Sp, Equal(Square(omega), Mul(Call("cEffSq", c0, ch, lam, oh), k))));
    }

    private static Formula ForReals(string[] names, Formula body) =>
        Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. names.Select(name => new Formula.BoundVariable(
                FormulaIdentifier.Create(name), Seq(Mathbb, Grp(F.Id("R")))))], body));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Square(Formula value) => Seq(Grp(value), Caret, Grp(D(2)));
    private static Formula Negative(Formula value) => Seq(Minus, Grp(value));
    private static Formula Divide(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
}

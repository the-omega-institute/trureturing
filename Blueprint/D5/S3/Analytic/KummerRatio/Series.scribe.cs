using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.KummerRatio;

internal sealed class SeriesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Convergence, regularity, positivity and recurrences of the Kummer series.",
        H("The entire Kummer series"), Blocks(
            Entry("kummer-coefficient-successor", "coeff_succ", "Successive Kummer coefficients",
                "For every real s, positive real c and natural n, kummerCoeff s c (n+1) equals ((s+n)/(c+n)/(n+1)) times kummerCoeff s c n. KarpZhangReciprocal.Coeff.c_succ applies this recurrence at s=2t and c=t."),
            Entry("kummer-summable", "summable_kummer", "Convergence for every real argument",
                "For every real upper parameter s, positive lower parameter c and real argument x, the defining series is summable. The recurrence between successive coefficients gives a multiplier tending to zero. The norm ratio bound proves absolute convergence even when the rising factorial in the numerator vanishes."),
            Entry("kummer-at-zero", "kummer_zero", "The value at zero",
                "For arbitrary real s and c, M(s;c;0)=1. Only the constant term contributes, so this identity does not require positivity of c."),
            Entry("kummer-positive", "one_le_kummer", "A positive lower bound",
                "When s and x are nonnegative and c is positive, all terms are nonnegative. The constant term is one, and hence M(s;c;x) is at least one."),
            Entry("kummer-derivative", "hasDerivAt_kummer", "Differentiation shifts both parameters",
                "For real s, positive c and every real x, the derivative of M(s;c;x) is (s/c) M(s+1;c+1;x). On each bounded interval, the differentiated terms are bounded by a constant multiple of an absolutely summable Kummer series at a larger nonnegative argument. Termwise differentiation therefore applies."),
            Entry("kummer-continuous", "continuous_kummer", "Continuity on the real line",
                "For real s and positive c, the function x mapped to M(s;c;x) is continuous on the whole real line, as a consequence of its derivative formula."),
            Entry("kummer-equation", "kummer_ode", "The confluent hypergeometric equation",
                "For real s, positive c and every real x, the shifted series satisfy x (s/c) ((s+1)/(c+1)) M(s+2;c+2;x)+(c-x) (s/c) M(s+1;c+1;x)-s M(s;c;x)=0. The coefficient recurrence cancels every coefficient. The derivative formula identifies this identity with x y''+(c-x)y'-s y=0, including x=0."),
            Entry("kummer-contiguous", "kummer_contiguous", "A relation between lower parameters",
                "For real s, positive c and every real x, M(s;c;x)=M(s;c+1;x)+s x/(c(c+1)) M(s+1;c+2;x). The rising factorial identity c (c+1)_n=(c+n)(c)_n gives the coefficient identity; absolute convergence justifies summing it."))));

    private static DocumentBlock Entry(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Analytic/KummerRatio/Series." + name),
            H(title), name == "coeff_succ" ? StatementSource.FromAuthor(Disp(All("s", F.Id("Real"), All("c", F.Id("Real"), Implies(Lt(Num(0), F.Id("c")), All("n", F.Id("Nat"), Equal(Call("kummerCoeff", F.Id("s"), F.Id("c"), Add(F.Id("n"), Num(1))), Multiply(new Formula.Fraction(new Formula.Fraction(Add(F.Id("s"), F.Id("n")), Add(F.Id("c"), F.Id("n"))), Add(F.Id("n"), Num(1))), Call("kummerCoeff", F.Id("s"), F.Id("c"), F.Id("n"))))))))))
                : StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class TranslationDomainWeakStrongDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Smooth compact-test weak differentiation and strong differentiation of the L2 translation orbit have the same domain.",
        H("Translation Domain: Weak and Strong Derivatives"),
        Blocks(Describe.Lean(
            DescribeId.Create("translation-domain-iff"),
            DeclarationHandle.Create("D5/S3/Quantum/Analysis/TranslationDomainWeakStrong.translation_domain_iff"),
            H("Translation-domain equivalence"),
            StatementSource.FromAuthor(Disp(TheoremFormula())),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("All integrals and MemLp conditions use Lebesgue measure volume on the real line. "
                    + "The symbols hf and hh are witnesses of the two displayed MemLp conditions. The classes [f] and [h] "
                    + "denote hf.toLp f and hh.toLp h in L2. V(t)[f] is the actual DomAddAct translation "
                    + "DomAddAct.mk t acting on [f], represented almost everywhere by x mapping to f(x+t).")),
                Paragraph(Text("The test class T consists of all real-valued smooth compactly supported functions: "
                    + "ContDiff Real (WithTop.some ENat.top) and HasCompactSupport. Test values and their "
                    + "ordinary derivatives are cast into Complex in the two integrals. HasDerivAt denotes "
                    + "the norm derivative in the actual L2 space, with real time.")),
                Paragraph(Text("Compact-support finite-measure domination differentiates translated test pairings. "
                    + "Scalar FTC, continuous-linear-map interval-integral commutation and separation by "
                    + "compact tests give V(t)[f]-[f] equal to the integral from zero to t of V(r)[h]. "
                    + "Vector FTC proves the forward implication; pairing derivatives and uniqueness prove "
                    + "the reverse. The only function hypotheses are the two square-integrability conditions."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula f = F.Id("f"), h = F.Id("h"), p = F.Id("p"), t = F.Id("t"), x = F.Id("x");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula function = new Formula.TypeArrow(real, complex);
        Formula weak = All([Bound("p", F.Id("T"))],
            Equal(Integral(Mul(Call("deriv", p, x), Apply(f, x))),
                Seq(Minus, Integral(Mul(Apply(p, x), Apply(h, x))))));
        Formula orbit = Seq(Open, t, Colon, Sp, real, Sp, Mapsto, Sp,
            Call("V", t, Bracket(f)), Close);
        Formula strong = Call("HasDerivAt", orbit, Bracket(h), D(0));
        Formula hypotheses = new Formula.Logic(
            Call("MemLp", f, D(2), F.Id("volume")), FormulaLogicOperator.And,
            Call("MemLp", h, D(2), F.Id("volume")));
        return All([Bound("f", function), Bound("h", function)],
            new Formula.Logic(Parenthesized(hypotheses), FormulaLogicOperator.Implies,
                Parenthesized(new Formula.Logic(weak, FormulaLogicOperator.Iff, strong))));
    }

    private static Formula.BoundVariable Bound(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Apply(Formula function, Formula value) => new Formula.Apply(function, [value]);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Bracket(Formula f) => Seq(OpenBracket, f, CloseBracket);
    private static Formula Parenthesized(Formula formula) => Seq(Open, formula, Close);
    private static Formula Integral(Formula expression) => Seq(Int, Underscore, Grp(F.Id("x"), Colon, Sp,
        Mathbb, Grp(F.Id("R"))), Sp, expression, Sp, F.Id("dx"));
}

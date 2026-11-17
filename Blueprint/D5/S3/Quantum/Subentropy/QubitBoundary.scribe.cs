using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Subentropy;

internal sealed class QubitBoundaryDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Subentropy/QubitBoundary.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A determinant expansion with a quantitative logarithmic remainder at the pure qubit boundary.",
        H("Qubit subentropy near a pure state"), Blocks(
            Paragraph(Text("Let A be a complex two by two positive semidefinite matrix with trace one, let delta be the real part of its determinant, and let Q(A) be the determinant-integral subentropy. All logarithms are natural. The two eigenvalues are nonnegative, sum to one, and have product delta, so 0<=delta<=1/4.")),
            Describe.Lean(DescribeId.Create("qubit-subentropy-near-pure"),
                DeclarationHandle.Create(Owner + "qubit_subentropy_near_pure"),
                H("The determinant remainder"), StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For t>0 the determinant kernel is delta t/((1+t)(t squared+t+delta)). Subtracting it from delta/(1+t) squared gives the nonnegative remainder delta squared/((1+t) squared(t squared+t+delta)). Its denominator is at least (t+delta)(t+1), because their difference is t(t+1)(t squared+2t+delta), which is nonnegative.")),
                    Paragraph(Text("When delta>0, the comparison function is delta squared/(1-delta) times the convergent reciprocal difference 1/(t+delta)-1/(t+1). Its integral is delta squared log(1/delta)/(1-delta). The inverse-square comparison has integral delta, and the density kernel is integrable, so integral monotonicity proves both bounds. When delta=0 the original determinant kernel vanishes pointwise on t>0 and Q(A)=0; no logarithmic formula at zero is used."))),
                DescribeRole.Theorem),
            Paragraph(Text("The error bound implies Q(A)=delta+O(delta squared times the absolute value of log delta) as delta decreases to zero through positive values, and Q(A)/delta tends to one. This supplies the leading term for any density family whose determinant is already known: delta asymptotic to epsilon squared/9 gives Q asymptotic to epsilon squared/9, while delta=sin(theta) squared/4 gives Q asymptotic to theta squared/4 as theta tends to zero. The determinant identities and normalization of those families are separate premises.")),
            Paragraph(Text("The result concerns finite density matrices. It makes no claim about a continuum path measure, tunneling probabilities, the emergence of time, or a physical realization of an early/late history model.")))));

    private static Formula Statement()
    {
        Formula a = F.Id("A");
        Formula delta = Call("Re", Call("det", a));
        Formula q = Call("Q", a);
        Formula deficit = Sub(delta, q);
        Formula boundary = ImpliesFormula(Equal(delta, D(0)), Equal(q, D(0)));
        Formula positive = ImpliesFormula(Less(D(0), delta), And(Le(D(0), deficit),
            Le(deficit, Rat(Mul(Pow(delta, D(2)), Call("log", Rat(D(1), delta))), Sub(D(1), delta)))));
        return new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("A"),
            Call("Matrix", Call("Fin", D(2)), Call("Fin", D(2)), Seq(Mathbb, Grp(F.Id("C")))),
            ImpliesFormula(And(Call("PosSemidef", a), Equal(Call("trace", a), D(1))),
                And(Le(D(0), delta), And(Le(delta, Rat(D(1), D(4))), And(boundary, positive)))));
    }

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula ImpliesFormula(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Rat(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
}

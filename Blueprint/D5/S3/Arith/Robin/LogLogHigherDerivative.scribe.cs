using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class LogLogHigherDerivativeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/LogLogHigherDerivative.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The log-log scale has strict alternating derivative signs at every positive order on x>1.",
        H("Higher Derivatives of the Log-Log Scale"),
        Blocks(
            Paragraph(Text("Put f(x)=log(log(x)), with natural logarithms. The domain "
                + "is x>1; no claim is made at x=1 or below. In the arithmetic Robin "
                + "margin the scale variable is x=log(n), so this is the derivative "
                + "kernel for the triple-logarithmic threshold, rather than a "
                + "derivative with respect to the integer n.")),
            Describe.Lean(
                DescribeId.Create("positive-kernel"),
                DeclarationHandle.Create(Prefix + "positiveKernel"),
                H("A positive kernel recursion"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For natural m,a,b, define "
                    + "K(0,a,b;x)=x^(-(a+1))*(log(x))^(-(b+1)). Recursively, "
                    + "K(m+1,a,b;x)=(a+1)*K(m,a+1,b;x) "
                    + "+(b+1)*K(m,a+1,b+1;x). Every coefficient and base factor "
                    + "is positive on x>1. Induction also proves "
                    + "d K(m,a,b;x)/dx=-K(m+1,a,b;x)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("positive-kernel-positive"),
                DeclarationHandle.Create(Prefix + "positiveKernel_pos"),
                H("Strict positivity of the recursive kernel"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For all natural m,a,b and every real x>1, K(m,a,b;x)>0. "
                    + "The base inverse powers are positive; each recursion step is a sum "
                    + "of two positive multiples. At m=1 and a=b=0 the kernel equals "
                    + "(log(x)+1)/(x^2*log(x)^2), the activation density used by the "
                    + "mixed arithmetic response."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("signed-higher-derivative"),
                DeclarationHandle.Create(Prefix + "signed_iteratedDeriv_logLog_pos"),
                H("The exact all-order sign"),
                StatementSource.FromAuthor(Disp(ResultFormula())), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The natural parameter m starts at zero, so the "
                        + "statement covers every positive derivative order m+1. "
                        + "The proof identifies f^(m+1)(x)=(-1)^m*K(m,0,0;x) "
                        + "on the entire open domain and proves strict positivity "
                        + "of the kernel by induction. Elementary log, power and "
                        + "product derivatives and locality of iterated derivatives "
                        + "are reused from Mathlib. This is an analytic statement "
                        + "for arbitrary orders and scales, with no finite cutoff.")),
                    Paragraph(Text("To infer alternating mixed corner responses of "
                        + "actual integer menus, one still needs the repeated "
                        + "fundamental-theorem-of-calculus transport over the "
                        + "positive increment box and cancellation of the "
                        + "prime-local divisor terms for distinct prime axes. "
                        + "Those corner statements are not asserted by this "
                        + "module. Derivative signs also supply no absolute "
                        + "Robin margin, zeta zero exclusion or proof of RH."))),
                DescribeRole.Theorem))));

    private static Formula ResultFormula()
    {
        Formula m = F.Id("m");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula f = Seq(Open, y, Sp, Mapsto, Sp, Call("log", Call("log", y)), Close);
        Formula order = new Formula.Binary(m, FormulaBinaryOperator.Add, D(1));
        Formula sign = new Formula.Power(Seq(Open, Minus, D(1), Close), m);
        Formula signedDerivative = new Formula.Binary(sign, FormulaBinaryOperator.Multiply,
            Call("iteratedDeriv", order, f, x));
        return new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("m"), Seq(Mathbb, Grp(F.Id("N")))),
             new Formula.BoundVariable(FormulaIdentifier.Create("x"), Seq(Mathbb, Grp(F.Id("R"))))],
            new Formula.Logic(new Formula.Relation(D(1), FormulaRelationOperator.LessThan, x),
                FormulaLogicOperator.Implies,
                new Formula.Relation(D(0), FormulaRelationOperator.LessThan, signedDerivative)));
    }

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
}

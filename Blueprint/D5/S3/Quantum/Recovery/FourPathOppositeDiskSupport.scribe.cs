using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class FourPathOppositeDiskSupportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A uniform complex disk support estimate for the opposite four-path coefficients.",
        H("Opposite four-disk support"),
        Blocks(Describe.Lean(
            DescribeId.Create("four-disk-support"),
            DeclarationHandle.Create("D5/S3/Quantum/Recovery/FourPathOppositeDiskSupport.four_disk_support"),
            H("Uniform support at every scale at least two"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("All four complex coordinates vary independently in their closed unit disks. The three real coefficients satisfy l at least two, h squared equal to one half, and c squared between five sixths and one. No phase restriction is imposed on the coordinates.")),
                Paragraph(Text("Align the complex amplitude by one common unit scalar. The disk support inequality then bounds the expression by the sum of the norms of l plus or minus h times that scalar, and l plus or minus i c times that scalar. Write x and y for its real and imaginary parts, so that x squared plus y squared equals one.")),
                Paragraph(Text("For the real pair a,b, the product identity (ab) squared equals (l squared minus h squared) squared plus four l squared h squared y squared. Nonnegativity of (ab-(l squared-h squared)) squared and (a+b-2l) squared bounds the gain a+b-2l by l h squared y squared divided by l squared minus h squared. This is at most four y squared divided by seven l.")),
                Paragraph(Text("Put L=sqrt(l squared+c squared). The complementary pair has deficit at least l squared c squared y squared divided by L cubed, using the paired deficit estimate. Since L is at most nine l eighths and L squared is at most five l squared fourths, L cubed is at most forty-five l cubed over thirty-two. The deficit coefficient is therefore at least four divided by seven l and pays the complete real-pair gain.")),
                Paragraph(Text("The four-path coefficients h=1/sqrt(2) and c=cos(pi/8) satisfy these hypotheses: h squared equals one half and c squared equals (2+sqrt(2))/4. The displayed theorem therefore gives the uniform disk support inequality for those coefficients. Further amplitude envelopes and producer matrix inequalities require additional arguments."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sq(Formula a) => new Formula.Power(a, Num(2));
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Norm(Formula a) => Call("norm", a);
    private static Formula TheoremFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R"))), complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula l=F.Id("l"), h=F.Id("h"), c=F.Id("c"), i=F.Id("i");
        Formula a=F.Id("a"), b=F.Id("b"), d=F.Id("d"), e=F.Id("e");
        Formula hypotheses=And(Le(Num(2),l), And(
            new Formula.Relation(Sq(h), FormulaRelationOperator.Equal, new Formula.Fraction(Num(1),Num(2))),
            And(Le(new Formula.Fraction(Num(5),Num(6)),Sq(c)), And(Le(Sq(c),Num(1)),
            And(Le(Norm(a),Num(1)), And(Le(Norm(b),Num(1)),
            And(Le(Norm(d),Num(1)), Le(Norm(e),Num(1)))))))));
        Formula amplitude=Sub(Mul(h,Sub(a,b)),Mul(Mul(i,c),Sub(d,e)));
        Formula left=Add(Norm(amplitude),Mul(l,Call("Re",Add(Add(Add(a,b),d),e))));
        Formula right=Add(Mul(Num(2),Call("sqrt",Add(Sq(l),Sq(c)))),Mul(Num(2),l));
        return Disp(All("l",real,All("h",real,All("c",real,
            All("a",complex,All("b",complex,All("d",complex,All("e",complex,
            new Formula.Logic(hypotheses,FormulaLogicOperator.Implies,Le(left,right))))))))));
    }
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.RenyiCombining;

internal sealed class ArimotoHyperbolicDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Entropy/RenyiCombining/ArimotoHyperbolic.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Entropy/hirche2020renyibounds");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The hyperbolic elasticity of the binary Arimoto coordinate increases below order one and from one through three halves.",
        H("Arimoto hyperbolic elasticity"), Blocks(
            Describe.Lean(DescribeId.Create("arimoto-hyperbolic-elasticity"),
                DeclarationHandle.Create(Prefix + "elasticity"), H("Hyperbolic elasticity"),
                StatementSource.FromAuthor(Disp(All("b", All("s", Equal(Call("elasticity", N("b"), N("s")),
                    new Formula.Fraction(
                        Multiply(Multiply(N("b"), Call("sinh", N("s"))), Pow(Call("cosh", N("s")), D(2))),
                        Multiply(Call("sinh", Multiply(N("b"), N("s"))),
                            Call("cosh", Multiply(Add(N("b"), D(1)), N("s")))))))))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(
                    "With b=alpha-1 and t=tanh(s), this quotient is the elasticity t psi''(t)/psi'(t) "
                    + "of psi(t)=k(alpha,(1-t)/2). The total quotient is used only at s>0 and b≠0."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("arimoto-hyperbolic-increasing"),
                DeclarationHandle.Create(Prefix + "strictMonoOn_elasticity"), H("Increasing elasticity"),
                StatementSource.FromAuthor(Disp(All("b", new Formula.Logic(
                    new Formula.Logic(
                        And(Lt(Subtract(D(0), D(1)), N("b")), Lt(N("b"), D(0))),
                        FormulaLogicOperator.Or,
                        And(Lt(D(0), N("b")), Le(N("b"), new Formula.Fraction(D(1), D(2))))),
                    FormulaLogicOperator.Implies,
                    Call("StrictMonoOn", Call("elasticity", N("b")), Call("Ioi", D(0))))))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(
                    "For s>0 the functions r cosh(rs)/sinh(rs) and r sinh(rs)/cosh(rs) strictly increase for r>0. "
                    + "Mathlib’s inequality 2z<sinh(2z), together with the double-angle identity, gives sinh(z)cosh(z)>z for the first comparison. "
                    + "The elasticity derivative divided by the positive elasticity is "
                    + "coth(s)+2tanh(s)-b coth(bs)-(b+1)tanh((b+1)s). "
                    + "For -1<b<0, oddness of sinh replaces b by -b in the coth term; both comparisons give positivity. "
                    + "For 0<b≤1/2, parameter comparison reduces the sign to b=1/2. "
                    + "At that endpoint the quotient equals cosh(s)^2/(2cosh(s)-1), whose derivative is "
                    + "2cosh(s)(cosh(s)-1)sinh(s)/(2cosh(s)-1)^2>0. "
                    + "No logarithm of a negative sinh value and no numerical sign test is used."))),
                DescribeRole.Theorem))));

    private static Formula N(string x) => F.Id(x);
    private static Formula All(string x, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), Seq(Mathbb, Grp(N("R"))), body);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(x, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.SpinChains.HKNNBlockBlochLargestWeight;
internal sealed class HKNNArcCoefficientsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/ArcCoefficients.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The strict coefficient deficit outside cyclic arcs", H("The strict coefficient deficit outside cyclic arcs"), Blocks(
            Node("strict_coefficient_non_arc", "A balanced cyclic binary word outside the block orbit contains alternating down-up-down-up sites or the complementary pattern. The prescribed partner swap supplies opposite signs. Unbalanced configurations have zero coefficient, and K is positive.", strictcoefficientnonarcFormula(), DescribeRole.Theorem, AssessedProvenance.FromRepo())
        ), []));
    private static DocumentBlock Node(string name, string prose, Formula formula, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("hknn-arccoefficients-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(name), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Implies, Parenthesized(y));
    private static Formula All(string v, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(v), type, body);
    private static Formula Negate(Formula x) => Seq(Neg, Sp, Parenthesized(x));
    private static Formula Abs(Formula x) => Seq(Lvert, Sp, x, Rvert);
    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Z() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Config(Formula m) => Call("Stationing", Mul(D(2), m));
    private static Formula strictcoefficientnonarcFormula()
    {
        Formula m=F.Id("m"), x=F.Id("x");
        return All("m",N(),Imp(Le(D(1),m),All("x",Config(m),Imp(Negate(Call("isArc",m,x)),Lt(Abs(Call("psi",m,x)),Parenthesized(Seq(Call("K",m),Colon,Sp,Z())))))));
    }
}

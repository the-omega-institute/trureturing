using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum;

internal sealed class OriginExclusionSegmentRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "XI origin exclusion: recentered quadratic constraint",
        H("XI origin exclusion: recentered quadratic constraint"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("b-constraint-recenter"),
                DeclarationHandle.Create("D5/S3/Quantum/OriginExclusionSegmentRigidity.b_constraint_recenter"),
                H("Recentered quadratic constraint"),
                StatementSource.FromAuthor(Disp(Forall("t", R(), Forall("b", R(),
                    Iff(
                        LE(Pow(Id("b"), Num(2)), Mul(Id("t"), Sub(Num(1), Id("t")))),
                        LE(Add(Pow(Sub(Id("t"), Frac(Num(1), Num(2))), Num(2)), Pow(Id("b"), Num(2))),
                            Pow(Frac(Num(1), Num(2)), Num(2)))))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The identity rewrites the XI auxiliary quadratic constraint as a translated closed-ball inequality. It is the algebraic step used before compactness and pure-locus analysis; the higher-dimensional effect and extremal-point claims remain outside this declaration."))),
                DescribeRole.Lemma))));

    private static Formula R() => Seq(Mathbb, Grp(Id("R")));
    private static Formula Id(string x) => DefinitionDsl.Id(x);
    private static Formula Num(int n) => DefinitionDsl.Num(n);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Frac(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula LE(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Forall(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
}

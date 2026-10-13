using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.NullSets;

internal sealed class AnalyticZeroSetNullDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/NullSets/AnalyticZeroSetNull.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A real analytic function on finite-dimensional real coordinate space has a null zero set whenever it has a nonzero value.",
        H("AnalyticZeroSetNull"),
        Blocks(Describe.Lean(DescribeId.Create("analytic-zero-set-null-ae-ne-zero"),
            DeclarationHandle.Create(Prefix + "ae_ne_zero_of_analytic"), H("ae_ne_zero_of_analytic"),
            StatementSource.FromAuthor(Statement()), AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/AnalyticClosure/mityagin2015zeroset")),
            Blocks(Paragraph(Text("The one-dimensional identity theorem rules out a positive-measure zero set for a nontrivial analytic function. Induction on dimension applies this fact to sections, with Fubini and the measure-preserving decomposition of finite coordinate space. Polynomial evaluations and analytic circuit determinants are two applications."))), DescribeRole.Theorem)),
        []));

    private static Formula Statement()
    {
        Formula n=F.Id("n"),f=F.Id("f"),a=F.Id("a"),x=F.Id("x");
        Formula space=Arrow(Fin(n),Reals());
        Formula nonzero=new Formula.Relation(At(f,a),FormulaRelationOperator.NotEqual,D(0));
        Formula premise=new Formula.Logic(Call("AnalyticOnNhd",Reals(),f,Named("Set.univ")),
            FormulaLogicOperator.And,nonzero);
        Formula volume=Typed(Named("volume"),Call("Measure",space));
        Formula conclusion=Seq(new Formula.Subscript(
            new Formula.Power(Forall,Seq(Mathrm,Grp(F.Id("m")))),volume),Sp,
            Typed(x,space),Comma,Sp,new Formula.Relation(At(f,x),FormulaRelationOperator.NotEqual,D(0)));
        return All(n,Seq(Mathbb,Grp(F.Id("N"))),All(f,Arrow(space,Reals()),All(a,space,
            new Formula.Logic(Parenthesized(premise),FormulaLogicOperator.Implies,conclusion))));
    }
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Named(string name) => Seq(Operatorname,
        Grp(name.Split('.').SelectMany((part, index) => index == 0
            ? new Formula[] { F.Id(part) } : new Formula[] { Dot, F.Id(part) }).ToArray()));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula At(Formula function, Formula argument) => new Formula.Apply(function, [argument]);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Sp, Colon, Sp, type));
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(variable, type), Comma, Sp, body);
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Fin(Formula size) => Call("Fin", size);
}

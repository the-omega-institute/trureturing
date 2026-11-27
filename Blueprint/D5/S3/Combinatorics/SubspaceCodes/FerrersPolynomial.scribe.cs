using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SubspaceCodes;

internal sealed class FerrersPolynomialDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Combinatorics/SubspaceCodes/FerrersPolynomial";
    private const string Digest = "The root bound for a four-term linearized polynomial gives rank at least nine.";
    private static readonly Formula Base = F.Id("F");
    private static readonly Formula Extension = F.Id("E");
    private static readonly Formula Coefficients = F.Id("a");
    private static readonly Formula Point = F.Id("x");
    private static readonly Formula Index = F.Id("i");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        GeneralHeader(Gid, Digest, "evidence-not-specified-by-formal-manifest"),
        H("Linearized polynomial rank"), Blocks(
            Node("evaluate-linearized", "evaluateLinearized",
                "Linearized evaluation map", DescribeRole.Definition, MapDefinition(),
                "Each power of the Frobenius denotes iteration, starting with the identity. The sum uses the scalar action of E on the space of F-linear maps."),
            Node("evaluate-linearized-apply", "evaluateLinearized_apply",
                "Evaluation by Frobenius powers", DescribeRole.Theorem, Evaluation(),
                "Applying the linear map to x gives the scalar polynomial formula."),
            Node("finrank-range-evaluate-linearized-ge-nine", "finrank_range_evaluateLinearized_ge_nine",
                "Rank bound in degree twelve", DescribeRole.Theorem, RankBound(),
                "The nonzero polynomial has distinct exponents 1, q, q² and q³, where q is the order of F. Its degree is at most q³, so its kernel has at most q³ elements and dimension at most three."))));

    private static Formula MapDefinition() =>
        OverFields(false, All("a", CoefficientType(), Equal(
            Seq(Open, EvaluationMap(), Sp, Colon, Sp, Call("LinearMap", Base, Extension, Extension), Close),
            SumOverIndices(Seq(App(Coefficients, Index), Sp, Cdot, Sp,
                new Formula.Power(Call("frobenius", Base, Extension), Call("val", Index)))))));

    private static Formula Evaluation() =>
        OverFields(false, All("a", CoefficientType(), All("x", Extension,
            Equal(App(EvaluationMap(), Point), SumOverIndices(
                Multiply(App(Coefficients, Index), new Formula.Power(Point,
                    new Formula.Power(Call("card", Base), Call("val", Index)))))))));

    private static Formula RankBound() =>
        OverFields(true, ImpliesTo(Equal(Call("finrank", Base, Extension), Num(12)),
            All("a", CoefficientType(), ImpliesTo(NotEqual(Coefficients, Num(0)),
                new Formula.Relation(Num(9), FormulaRelationOperator.LessThanOrEqual,
                    Call("finrank", Base, Call("range", EvaluationMap())))))));

    private static Formula OverFields(bool finiteExtension, Formula body) =>
        All("F", F.Id("Type"), WithInstance(Call("Field", Base), WithInstance(Call("Fintype", Base),
            All("E", F.Id("Type"), WithInstance(Call("Field", Extension),
                WithInstance(Call("Algebra", Base, Extension),
                    finiteExtension ? WithInstance(Call("Finite", Extension), body) : body))))));

    private static Formula WithInstance(Formula type, Formula body) =>
        Seq(OpenBracket, type, CloseBracket, Sp, body);
    private static Formula CoefficientType() => new Formula.TypeArrow(Call("Fin", Num(4)), Extension);
    private static Formula EvaluationMap() => Call("evaluateLinearized", Base, Extension, Coefficients);
    private static Formula SumOverIndices(Formula term) =>
        Seq(Sum, Underscore, Grp(Index, InMacro, Sp, Call("Fin", Num(4))), Sp, term);
    private static Formula App(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula ImpliesTo(Formula premise, Formula conclusion) =>
        new Formula.Logic(Seq(Open, premise, Close), FormulaLogicOperator.Implies, Seq(Open, conclusion, Close));

    private static DocumentBlock Node(
        string id, string declaration, string title, DescribeRole role, Formula statement, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Gid + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}

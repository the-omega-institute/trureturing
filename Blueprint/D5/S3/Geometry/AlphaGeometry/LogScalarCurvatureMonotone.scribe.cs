using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.AlphaGeometry;

internal sealed class LogScalarCurvatureMonotoneDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/AlphaGeometry/LogScalarCurvatureMonotone.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Geometry/gibiliscoisola2005scalarcurvature");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict Schur increase of logarithmic simplex scalar curvature.", H("LogScalarCurvatureMonotone"), Blocks(
            Node("claim", Disp(Seq(F.Id("claim"), Sp, Iff, Sp, Parenthesized(Seq(Forall, Sp, Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N")))), Comma, Sp, Parenthesized(Seq(Parenthesized(new Formula.Relation(D(3), FormulaRelationOperator.LessThanOrEqual, F.Id("n"))), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, Seq(F.Id("x"), Sp, F.Id("y"), Sp, Colon, Sp, Seq(Parenthesized(App(Op("Fin"), F.Id("n"))), Sp, To, Sp, Parenthesized(Seq(Mathbb, Grp(F.Id("R")))))), Comma, Sp, Parenthesized(Seq(Parenthesized(new Formula.Relation(F.Id("x"), FormulaRelationOperator.MemberOf, App(Op("simplex"), F.Id("n")))), Sp, To, Sp, Parenthesized(Seq(Parenthesized(new Formula.Relation(F.Id("y"), FormulaRelationOperator.MemberOf, App(Op("simplex"), F.Id("n")))), Sp, To, Sp, Parenthesized(Seq(Parenthesized(App(Op("moreMixed"), F.Id("x"), F.Id("y"))), Sp, To, Sp, Parenthesized(new Formula.Logic(new Formula.Relation(App(Op("scalInfty"), F.Id("y")), FormulaRelationOperator.LessThanOrEqual, App(Op("scalInfty"), F.Id("x"))), FormulaLogicOperator.And, Parenthesized(Seq(Parenthesized(Parenthesized(Seq(Neg, Sp, Parenthesized(Seq(Exists, Sp, Seq(SigmaLower, Sp, Colon, Sp, App(Seq(Op("Equiv"), Dot, Sp, Op("Perm")), Parenthesized(App(Op("Fin"), F.Id("n"))))), Comma, Sp, Parenthesized(new Formula.Relation(F.Id("x"), FormulaRelationOperator.Equal, Seq(Parenthesized(F.Id("y")), Sp, Circ, Sp, Parenthesized(SigmaLower))))))))), Sp, To, Sp, Parenthesized(new Formula.Relation(App(Op("scalInfty"), F.Id("y")), FormulaRelationOperator.LessThan, App(Op("scalInfty"), F.Id("x")))))))))))))))))))))), "Source quotation (arXiv:math-ph/0407007v2, printed p. 11, Conjecture 4.1): Suppose n>2. For the function Scalₚ(·):𝒫¹ₙ → R one has the following properties: - if p ∈ (1,2) then Scalₚ(·) is a strictly Schur-decreasing function; - if p ∈ (2,+∞] then Scalₚ(·) is a strictly Schur-increasing function. Encoding: n is natural, n>2 becomes 3≤n; x and y are positive normalized Fin n real vectors. moreMixed x y means x is more mixed. Only p=∞ is asserted, with equality allowed for permutations.", DescribeRole.Definition),
            Node("moreMixed_positive_chain", Disp(Seq(Forall, Sp,
                Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp,
                Forall, Sp, Parenthesized(Seq(F.Id("x"), Sp, F.Id("y"), Sp, Colon, Sp,
                    Seq(Parenthesized(App(Op("Fin"), F.Id("n"))), Sp, To, Sp,
                        Seq(Mathbb, Grp(F.Id("R")))))), Comma, Sp,
                Parenthesized(new Formula.Relation(F.Id("x"), FormulaRelationOperator.MemberOf,
                    App(Op("simplex"), F.Id("n")))), Sp, To, Sp,
                Parenthesized(new Formula.Relation(F.Id("y"), FormulaRelationOperator.MemberOf,
                    App(Op("simplex"), F.Id("n")))), Sp, To, Sp,
                App(Op("moreMixed"), F.Id("x"), F.Id("y")), Sp, To, Sp,
                App(Seq(Op("Relation"), Dot, Op("ReflTransGen")), Op("PositiveT"),
                    F.Id("y"), F.Id("x")))),
                "Majorization of positive normalized vectors is realized by a finite chain of positive T-transforms, from the less mixed vector to the more mixed vector.", DescribeRole.Theorem),
            Node("result", Disp(Seq(Forall, Sp, Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N")))), Comma, Sp, Parenthesized(Seq(Parenthesized(new Formula.Relation(D(3), FormulaRelationOperator.LessThanOrEqual, F.Id("n"))), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, Seq(F.Id("x"), Sp, F.Id("y"), Sp, Colon, Sp, Seq(Parenthesized(App(Op("Fin"), F.Id("n"))), Sp, To, Sp, Parenthesized(Seq(Mathbb, Grp(F.Id("R")))))), Comma, Sp, Parenthesized(Seq(Parenthesized(new Formula.Relation(F.Id("x"), FormulaRelationOperator.MemberOf, App(Op("simplex"), F.Id("n")))), Sp, To, Sp, Parenthesized(Seq(Parenthesized(new Formula.Relation(F.Id("y"), FormulaRelationOperator.MemberOf, App(Op("simplex"), F.Id("n")))), Sp, To, Sp, Parenthesized(Seq(Parenthesized(App(Op("moreMixed"), F.Id("x"), F.Id("y"))), Sp, To, Sp, Parenthesized(new Formula.Logic(new Formula.Relation(App(Op("scalInfty"), F.Id("y")), FormulaRelationOperator.LessThanOrEqual, App(Op("scalInfty"), F.Id("x"))), FormulaLogicOperator.And, Parenthesized(Seq(Parenthesized(Parenthesized(Seq(Neg, Sp, Parenthesized(Seq(Exists, Sp, Seq(SigmaLower, Sp, Colon, Sp, App(Seq(Op("Equiv"), Dot, Sp, Op("Perm")), Parenthesized(App(Op("Fin"), F.Id("n"))))), Comma, Sp, Parenthesized(new Formula.Relation(F.Id("x"), FormulaRelationOperator.Equal, Seq(Parenthesized(F.Id("y")), Sp, Circ, Sp, Parenthesized(SigmaLower))))))))), Sp, To, Sp, Parenthesized(new Formula.Relation(App(Op("scalInfty"), F.Id("y")), FormulaRelationOperator.LessThan, App(Op("scalInfty"), F.Id("x")))))))))))))))))))), "The logarithmic endpoint follows from the geometric power-sum identity, strict pair equalization and a finite positive transfer chain. No finite-p or quantum clause is asserted.", DescribeRole.Theorem, new OpenProblemResolutionClaim(ProblemSlugRef.Create("gibilisco-isola-2004-log-geometry-scalar-curvature"), ResolutionKind.Proved))
        )));
    private static DocumentBlock Node(string name, Formula statement, string prose, DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("logscalarcurvaturemonotone-" + name.Replace('.', '-').Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(name),
            StatementSource.FromAuthor(statement), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Op(string name) => Seq(Operatorname, Grp(F.Id(name)));
}

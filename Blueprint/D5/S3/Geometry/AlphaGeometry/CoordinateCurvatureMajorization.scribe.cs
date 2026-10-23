using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.AlphaGeometry;

internal sealed class CoordinateCurvatureMajorizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict positive T-transform chains for spectral cube-root curvature.", H("CoordinateCurvatureMajorization"), Blocks(
            Node("D5/S3/Geometry/AlphaGeometry/CoordinateCurvatureMajorization.spectral_moreMixed_monotone",
                Seq(Forall, Sp, OpenBrace, Sp, F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, CloseBrace, Sp, Parenthesized(Seq(F.Id("p"), Sp, F.Id("q"), Sp, Colon, Sp, Op("Fin"), Sp, F.Id("n"), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Comma, Sp, Parenthesized(Seq(D(2), Sp, Leq, Sp, F.Id("n"))), Sp, To, Sp, Parenthesized(Seq(F.Id("p"), Sp, InMacro, Sp, Op("simplex"), Sp, F.Id("n"))), Sp, To, Sp, Parenthesized(Seq(F.Id("q"), Sp, InMacro, Sp, Op("simplex"), Sp, F.Id("n"))), Sp, To, Sp, Parenthesized(Seq(Op("moreMixed"), Sp, F.Id("q"), Sp, F.Id("p"))), Sp, To, Sp, Op("lambdaRatio"), Sp, F.Id("p"), Sp, Leq, Sp, Op("lambdaRatio"), Sp, F.Id("q")),
                "The stated identity or implication holds for every displayed parameter.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("D5/S3/Geometry/AlphaGeometry/CoordinateCurvatureMajorization.spectral_moreMixed_strict",
                Seq(Forall, Sp, OpenBrace, Sp, F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, CloseBrace, Sp, Parenthesized(Seq(F.Id("p"), Sp, F.Id("q"), Sp, Colon, Sp, Op("Fin"), Sp, F.Id("n"), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Comma, Sp, Parenthesized(Seq(D(2), Sp, Leq, Sp, F.Id("n"))), Sp, To, Sp, Parenthesized(Seq(F.Id("p"), Sp, InMacro, Sp, Op("simplex"), Sp, F.Id("n"))), Sp, To, Sp, Parenthesized(Seq(F.Id("q"), Sp, InMacro, Sp, Op("simplex"), Sp, F.Id("n"))), Sp, To, Sp, Parenthesized(Seq(Op("moreMixed"), Sp, F.Id("q"), Sp, F.Id("p"))), Sp, To, Sp, Parenthesized(Seq(Neg, Sp, Exists, Sp, Pi, Sp, Colon, Sp, Op("Equiv"), Sp, Dot, Sp, Op("Perm"), Sp, Parenthesized(Seq(Op("Fin"), Sp, F.Id("n"))), Sp, Comma, Sp, F.Id("q"), Sp, F.Eq, Sp, F.Id("p"), Sp, Circ, Sp, Pi)), Sp, To, Sp, Op("lambdaRatio"), Sp, F.Id("p"), Sp, Lt, Sp, Op("lambdaRatio"), Sp, F.Id("q")),
                "The positive T-transform chain contains a strict step unless its endpoints differ by a permutation. Monotonicity before and after that step gives strict spectral curvature comparison.", DescribeRole.Theorem, AssessedProvenance.FromRepo())
        )));
    private static DocumentBlock Node(string declaration, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(declaration.Replace('/', '-').Replace('.', '-').Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(declaration), H(declaration.Split('.')[^1]),
            StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role);
    private static Formula Op(string value) => Seq(Operatorname, Grp(F.Id(value)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}

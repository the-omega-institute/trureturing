using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.AlphaGeometry;

internal sealed class CubeRootSpectralMonotonicityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Moment-deficit positivity and strict spectral cube-root T-transform growth.", H("CubeRootSpectralMonotonicity"), Blocks(
            Node("D5/S3/Geometry/AlphaGeometry/CubeRootSpectralMonotonicity.spectralN",
                Seq(Forall, Sp, OpenBrace, Sp, F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, CloseBrace, Sp, Parenthesized(Seq(F.Id("r"), Sp, Colon, Sp, Op("Fin"), Sp, F.Id("n"), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Comma, Sp, Op("spectralN"), Sp, F.Id("r"), Sp, F.Eq, Sp, Parenthesized(Seq(Parenthesized(Seq(D(4), Sp, Star, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Seq(Caret, Grp(Seq(D(2)))), Sp, Minus, Sp, D(2))), Sp, Star, Sp, Parenthesized(Seq(F.Id("P"), Sp, F.Id("n"), Sp, F.Id("r"), Sp, D(1))), Sp, Seq(Caret, Grp(Seq(D(2)))), Sp, Minus, Sp, D(2), Sp, Star, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Star, Sp, F.Id("P"), Sp, F.Id("n"), Sp, F.Id("r"), Sp, D(2))), Sp, Star, Sp, F.Id("P"), Sp, F.Id("n"), Sp, F.Id("r"), Sp, D(4), Sp, Minus, Sp, D(8), Sp, Star, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Star, Sp, F.Id("P"), Sp, F.Id("n"), Sp, F.Id("r"), Sp, D(1), Sp, Star, Sp, F.Id("P"), Sp, F.Id("n"), Sp, F.Id("r"), Sp, D(5), Sp, Plus, Sp, D(8), Sp, Star, Sp, F.Id("P"), Sp, F.Id("n"), Sp, F.Id("r"), Sp, D(6)),
                "The defining expression of spectralN.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("D5/S3/Geometry/AlphaGeometry/CubeRootSpectralMonotonicity.spectralRatio",
                Seq(Forall, Sp, OpenBrace, Sp, F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, CloseBrace, Sp, Parenthesized(Seq(F.Id("r"), Sp, Colon, Sp, Op("Fin"), Sp, F.Id("n"), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Comma, Sp, Op("spectralRatio"), Sp, F.Id("r"), Sp, F.Eq, Sp, Op("spectralN"), Sp, F.Id("r"), Sp, Slash, Sp, Parenthesized(Seq(D(9), Sp, Star, Sp, Parenthesized(Seq(F.Id("P"), Sp, F.Id("n"), Sp, F.Id("r"), Sp, D(4))), Sp, Seq(Caret, Grp(Seq(D(2))))))),
                "The defining expression of spectralRatio.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("D5/S3/Geometry/AlphaGeometry/CubeRootSpectralMonotonicity.lambdaRatio",
                Seq(Forall, Sp, OpenBrace, Sp, F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, CloseBrace, Sp, Parenthesized(Seq(F.Id("l"), Sp, Colon, Sp, Op("Fin"), Sp, F.Id("n"), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Comma, Sp, Op("lambdaRatio"), Sp, F.Id("l"), Sp, F.Eq, Sp, Op("spectralRatio"), Sp, Parenthesized(Seq(Op("fun"), Sp, F.Id("i"), Sp, Mapsto, Sp, F.Id("l"), Sp, F.Id("i"), Sp, Seq(Caret, Grp(Seq(Parenthesized(Seq(D(1), Sp, Slash, Sp, D(3), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))))))))),
                "The defining expression of lambdaRatio.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("D5/S3/Geometry/AlphaGeometry/CubeRootSpectralMonotonicity.lambdaRatio_perm",
                Seq(Forall, Sp, OpenBrace, Sp, F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, CloseBrace, Sp, Parenthesized(Seq(F.Id("l"), Sp, Colon, Sp, Op("Fin"), Sp, F.Id("n"), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Parenthesized(Seq(F.Id("p"), Sp, Colon, Sp, Op("Equiv"), Sp, Dot, Sp, Op("Perm"), Sp, Parenthesized(Seq(Op("Fin"), Sp, F.Id("n"))))), Sp, Comma, Sp, Op("lambdaRatio"), Sp, Parenthesized(Seq(F.Id("l"), Sp, Circ, Sp, F.Id("p"))), Sp, F.Eq, Sp, Op("lambdaRatio"), Sp, F.Id("l")),
                "The stated identity or implication holds for every displayed parameter.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("D5/S3/Geometry/AlphaGeometry/CubeRootSpectralMonotonicity.strict_t_transform_any_pair",
                Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Parenthesized(Seq(F.Id("l"), Sp, Colon, Sp, Op("Fin"), Sp, F.Id("n"), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Parenthesized(Seq(F.Id("i"), Sp, F.Id("j"), Sp, Colon, Sp, Op("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("t"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Comma, Sp, Parenthesized(Seq(D(2), Sp, Leq, Sp, F.Id("n"))), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, F.Id("k"), Sp, Comma, Sp, D(0), Sp, Lt, Sp, F.Id("l"), Sp, F.Id("k"))), Sp, To, Sp, Parenthesized(Seq(F.Id("l"), Sp, F.Id("j"), Sp, Lt, Sp, F.Id("l"), Sp, F.Id("i"))), Sp, To, Sp, Parenthesized(Seq(D(0), Sp, Lt, Sp, F.Id("t"))), Sp, To, Sp, Parenthesized(Seq(F.Id("t"), Sp, Lt, Sp, D(1))), Sp, To, Sp, Op("lambdaRatio"), Sp, F.Id("l"), Sp, Lt, Sp, Op("lambdaRatio"), Sp, Parenthesized(Seq(Parenthesized(Seq(Parenthesized(Seq(D(1), Sp, Minus, Sp, F.Id("t"))), Sp, Cdot, Sp, F.Id("l"), Sp, Plus, Sp, F.Id("t"), Sp, Cdot, Sp, Parenthesized(Seq(F.Id("l"), Sp, Circ, Sp, Op("Equiv"), Sp, Dot, Sp, Op("swap"), Sp, F.Id("i"), Sp, F.Id("j")))))))),
                "A strict equalizing T-transform increases the spectral curvature ratio. The derivative is positive before the midpoint; permutation symmetry handles the other half.", DescribeRole.Theorem, AssessedProvenance.FromRepo())
        )));
    private static DocumentBlock Node(string declaration, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(declaration.Replace('/', '-').Replace('.', '-').Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(declaration), H(declaration.Split('.')[^1]),
            StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role);
    private static Formula Op(string value) => Seq(Operatorname, Grp(F.Id(value)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}

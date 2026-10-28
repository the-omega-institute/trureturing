using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.CubicGain;

internal sealed class LiteralSylvesterBoundsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact parameter degrees of the original fixed elimination determinants",
        H("Fixed row and column orders"),
        Blocks(
            Paragraph(Text("The coefficient ring is Z[b] and the outer polynomial variable is the original independent r. sourcePolynomial has entries E01, E02 and E12, in that order. For k:Fin 2, sylvesterRow consists of r^14 E01 through E01 followed by r^14 E(k+1) through E(k+1). literalSylvester retains these thirty rows in columns r^29 through 1. actualResultant(k) is exactly its determinant, so k=0 denotes the source R1 and k=1 denotes R2. In the formulas, sourcePair(b,0)=sourceE1(b) and sourcePair(b,1)=sourceE2(b), and resultantEvaluation(b,p) evaluates the integer polynomial p at the real parameter b.")),
            Paragraph(Text("Every source coefficient of r^j has b degree at most 17-j when nonzero. A row shifted by s and a column of exponent c therefore have nonzero entry degree plus c at most 17+s. Every nonzero permutation product uses every column once. Summing these inequalities gives the degree bound for each determinant term and hence the determinant. Zero entries and zero determinant terms are included.")),
            Describe.Lean(DescribeId.Create("literal-sylvester-degree-bound"),
                DeclarationHandle.Create("D5/S3/Observer/CubicGain/LiteralSylvesterBounds.literal_resultant_degree_bound"),
                H("Both original fixed resultants have degree at most 285"),
                StatementSource.FromAuthor(ResultantBound()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every k:Fin 2, actualResultant(k) has natural degree at most 285. The row weights are 17 plus shifts 14 through 0, twice; the column weights are 29 through 0. No assumption requires a leading coefficient to remain nonzero at any parameter value."))), DescribeRole.Theorem),
            Paragraph(Text("The original fixed linear minors are actualMinorA0 and actualMinorC0 of ActualMinorLift. They retain rows r^13 E01 through E01 followed by r^13 E02 through E02. Their first twenty-seven columns are r^28 through r^2; their final columns are respectively r and 1, with no sign or scale adjustment.")),
            Describe.Lean(DescribeId.Create("literal-linear-minor-degree-bounds"),
                DeclarationHandle.Create("D5/S3/Observer/CubicGain/LiteralSylvesterBounds.literal_minor_degree_bounds"),
                H("The original fixed linear-minor degree bounds"),
                StatementSource.FromAuthor(MinorBounds()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The natural degrees of actualMinorA0 and actualMinorC0 are at most 252 and 253 respectively. The same weighted argument uses shifts 13 through 0 twice and the original retained column exponents."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("literal-elimination-exact-degrees"),
                DeclarationHandle.Create("D5/S3/Observer/CubicGain/LiteralSylvesterBounds.literal_elimination_exact_degrees"),
                H("Exact degrees of the original fixed determinants"),
                StatementSource.FromAuthor(ExactDegrees()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Both original fixed Sylvester determinants have natural degree 285; the original r-column and constant-column minors have natural degrees 252 and 253 respectively. For each entry the proof extracts the coefficient at row weight minus column exponent. Scaling rows and columns by powers of X identifies the determinant coefficient with the determinant of this integer leading matrix. The exact full-matrix certificates in LiteralLeadingCertificates prove that all four leading determinants are nonzero. Every coefficient array is checked against sourcePolynomial, and every matrix entry is connected to the original fixed rows and columns."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("literal-resultant-common-root-cover"),
                DeclarationHandle.Create("D5/S3/Observer/CubicGain/LiteralSylvesterBounds.literal_resultant_vanishes_of_common_root"),
                H("A literal fixed-degree resultant vanishes at every common source root"),
                StatementSource.FromAuthor(CommonRootCover()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For either original pair, a common real source root supplies the nonzero vector (z^29,...,1) to the exact thirty-row fixed Sylvester matrix. The determinant therefore vanishes after evaluating the parameter b, even when a specialized leading coefficient drops. The theorem uses the original E0/E1/E2 coefficient arrays and does not select a root or divide by a leading coefficient."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("literal-minor-common-root-relation"),
                DeclarationHandle.Create("D5/S3/Observer/CubicGain/LiteralSylvesterBounds.literal_minor_relation_of_common_root"),
                H("The literal fixed linear minors obey the common-root relation"),
                StatementSource.FromAuthor(MinorRelation()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A common real root of the original E0 and E1 rows gives z times the evaluated r-column determinant plus the evaluated constant-column determinant equal to zero. The proof transports the existing 28-row fixed-minor relation through the integer coefficient determinants, retaining every row and column and dividing by no leading coefficient."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("source-critical-literal-elimination"),
                DeclarationHandle.Create("D5/S3/Observer/CubicGain/LiteralSylvesterBounds.source_critical_literal_elimination"),
                H("Critical sources satisfy the original elimination equations"),
                StatementSource.FromAuthor(SourceElimination()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real t,b, let M(i,j,t,b)=sourceBt(i,t,b) sourceBb(j,t,b)-sourceBb(i,t,b) sourceBt(j,t,b). If all three ordered minors vanish, then either D(t,b)=0 or both actual fixed resultants vanish at b and the actual fixed linear minors satisfy (t b) a0(b)+c0(b)=0. The three division-free normalization identities supply the common source roots; the E12 identity supplies the second resultant. The singular branch is explicit, so the statement retains b=0, all real parameters and all leading-degree drops. It gives necessary elimination equations, without asserting that a projected resultant root lifts to a critical source."))), DescribeRole.Theorem),
            Paragraph(Text("These are polynomial bounds and exact degrees before specialization. All rows, columns and zero padding remain fixed even when specialization lowers a leading degree. These results do not prove exact resultant or minor factorizations, the displayed common factors, primitive positive normalization, coprimality, or any root or world exhaustion.")))));

    private static Formula Call(string name, params Formula[] args)
    {
        var pieces = new System.Collections.Generic.List<Formula>();
        for (int i = 0; i < args.Length; i++)
        {
            if (i > 0) { pieces.Add(Comma); pieces.Add(Sp); }
            pieces.Add(args[i]);
        }
        return Seq(Operatorname, Grp(F.Id(name)), Open, Seq(pieces.ToArray()), Close);
    }
    private static Formula ResultantBound() => Disp(Seq(
        Forall, Sp, F.Id("k"), InMacro, Sp, Call("Fin", D(2)), Comma, Sp,
        Call("natDegree", Call("actualResultant", F.Id("k"))), Leq, Sp, D(2,8,5)));
    private static Formula ExactDegrees() => Disp(Seq(
        Open, Forall, Sp, F.Id("k"), InMacro, Sp, Call("Fin", D(2)), Comma, Sp,
        Call("natDegree", Call("actualResultant", F.Id("k"))), Eq, Sp, D(2,8,5), Close,
        Land, Sp, Call("natDegree", Seq(F.Id("a"), Underscore, Grp(D(0)))), Eq, Sp, D(2,5,2),
        Land, Sp, Call("natDegree", Seq(F.Id("c"), Underscore, Grp(D(0)))), Eq, Sp, D(2,5,3)));
    private static Formula MinorBounds() => Disp(Seq(
        Call("natDegree", Seq(F.Id("a"), Underscore, Grp(D(0)))), Leq, Sp, D(2,5,2), Land, Sp,
        Call("natDegree", Seq(F.Id("c"), Underscore, Grp(D(0)))), Leq, Sp, D(2,5,3)));
    private static Formula CommonRootCover() => Disp(Seq(
        Forall, Sp, F.Id("b"), Comma, Sp, F.Id("z"), InMacro, Sp,
        Mathbb, Grp(F.Id("R")), Comma, Sp, Forall, Sp, F.Id("k"), InMacro, Sp,
        Call("Fin", D(2)), Comma, Sp,
        Grp(Call("eval", F.Id("z"), Call("sourceE0", F.Id("b")))), Eq, Sp, D(0), Land, Sp,
        Grp(Call("eval", F.Id("z"), Call("sourcePair", F.Id("b"), F.Id("k")))), Eq, Sp, D(0),
        Implies, Sp,
        Call("resultantEvaluation", F.Id("b"), Call("actualResultant", F.Id("k"))), Eq, Sp, D(0)));
    private static Formula MinorRelation() => Disp(Seq(
        Forall, Sp, F.Id("b"), Comma, Sp, F.Id("z"), InMacro, Sp,
        Mathbb, Grp(F.Id("R")), Comma, Sp,
        Grp(Call("eval", F.Id("z"), Call("sourceE0", F.Id("b")))), Eq, Sp, D(0), Land, Sp,
        Grp(Call("eval", F.Id("z"), Call("sourceE1", F.Id("b")))), Eq, Sp, D(0),
        Implies, Sp,
        F.Id("z"), Sp, Call("evalB", F.Id("b"), Call("actualMinorA0")), Plus, Sp,
        Call("evalB", F.Id("b"), Call("actualMinorC0")), Eq, Sp, D(0)));
    private static Formula SourceElimination()
    {
        var t = F.Id("t"); var b = F.Id("b"); var k = F.Id("k");
        Formula M(byte i, byte j) => Call("M", D(i), D(j), t, b);
        return Disp(Seq(Forall, Sp, t, Comma, Sp, b, InMacro, Sp,
            Mathbb, Grp(F.Id("R")), Comma, Sp,
            M(0,1), Eq, Sp, D(0), Land, Sp, M(0,2), Eq, Sp, D(0), Land, Sp,
            M(1,2), Eq, Sp, D(0), Implies, Sp,
            Call("sourceD", t, b), Eq, Sp, D(0), Lor, Sp, Open,
            Open, Forall, Sp, k, InMacro, Sp, Call("Fin", D(2)), Comma, Sp,
            Call("resultantEvaluation", b, Call("actualResultant", k)), Eq, Sp, D(0), Close,
            Land, Sp, t, b, Call("evalB", b, Call("actualMinorA0")), Plus, Sp,
            Call("evalB", b, Call("actualMinorC0")), Eq, Sp, D(0), Close));
    }

}

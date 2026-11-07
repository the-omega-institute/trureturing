using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Probability;

internal sealed class GaussianPolynomialLogDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Analytic/Probability/GaussianPolynomialLog";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/chafaidadounyoussef2024logenergy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "GaussianPolynomialLog mathematical statements.",
        H("Gaussian Polynomial Log"),
        Blocks(
            Describe.Lean(DescribeId.Create("cdy-gaussianpolynomiallog-gaussian-roots-nonzero"),
                DeclarationHandle.Create(Module + ".gaussian_roots_nonzero"),
                H("gaussian_roots_nonzero"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Parenthesized(Seq(F.Id("v"), Sp, Colon, Sp, Q("NNReal"))), Sp, Parenthesized(Seq(F.Id("s"), Sp, Colon, Sp, F.Id("Multiset"), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Comma, Sp, Parenthesized(Seq(F.Id("v"), Sp, Neq, Sp, D(0))), Sp, To, Sp, Seq(Forall, Caret, Grp(F.Id("ae")), Sp), Sp, F.Id("x"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Sp, Q("d"), Sp, F.Id("gaussianReal"), Sp, F.Id("m"), Sp, F.Id("v"), Comma, Sp, Parenthesized(Seq(F.Id("s"), Dot, Sp, F.Id("map"), Sp, Parenthesized(Seq(F.Id("fun"), Sp, F.Id("z"), Sp, Mapsto, Sp, Parenthesized(Seq(F.Id("x"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Minus, Sp, F.Id("z"))))), Dot, Sp, F.Id("prod"), Sp, Neq, Sp, D(0)))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("gaussian_roots_nonzero satisfies the displayed statement."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("cdy-gaussianpolynomiallog-gaussian-polynomial-log-integrable"),
                DeclarationHandle.Create(Module + ".gaussian_polynomial_log_integrable"),
                H("gaussian_polynomial_log_integrable"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Parenthesized(Seq(F.Id("v"), Sp, Colon, Sp, Q("NNReal"))), Sp, Parenthesized(Seq(F.Id("p"), Sp, Colon, Sp, F.Id("Polynomial"), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Comma, Sp, Parenthesized(Seq(F.Id("v"), Sp, Neq, Sp, D(0))), Sp, To, Sp, Parenthesized(Seq(F.Id("p"), Sp, Neq, Sp, D(0))), Sp, To, Sp, F.Id("Integrable"), Sp, Parenthesized(Seq(F.Id("fun"), Sp, F.Id("x"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Sp, Mapsto, Sp, F.Id("Real"), Dot, Sp, F.Id("log"), Sp, Vert, Sp, F.Id("p"), Dot, Sp, F.Id("eval"), Sp, Parenthesized(Seq(F.Id("x"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Vert, Sp)), Sp, Parenthesized(Seq(F.Id("gaussianReal"), Sp, F.Id("m"), Sp, F.Id("v")))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("gaussian_polynomial_log_integrable satisfies the displayed statement."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("cdy-gaussianpolynomiallog-rootlogcost"),
                DeclarationHandle.Create(Module + ".rootLogCost"),
                H("rootLogCost"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Parenthesized(Seq(F.Id("v"), Sp, Colon, Sp, Q("NNReal"))), Comma, Sp, F.Id("rootLogCost"), Sp, F.Id("m"), Sp, F.Id("v"), Sp, Eq, Sp, Parenthesized(Seq(Parenthesized(Seq(Int, Sp, F.Id("x"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Comma, Sp, Bar, Sp, F.Id("x"), Bar, Sp, Q("d"), Sp, F.Id("gaussianReal"), Sp, F.Id("m"), Sp, F.Id("v"))), Sp, Plus, Sp, new Formula.Power(Parenthesized(Seq(F.Id("Real"), Dot, Sp, F.Id("sqrt"), Sp, Parenthesized(Seq(D(2), Sp, Star, Sp, F.Id("Real"), Dot, Sp, F.Id("pi"), Sp, Star, Sp, F.Id("v"))))), Seq(Minus, D(1))), Sp, Star, Sp, Parenthesized(Seq(Int, Sp, F.Id("x"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Comma, Sp, F.Id("Real"), Dot, Sp, F.Id("posLog"), Sp, new Formula.Power(F.Id("x"), Seq(Minus, D(1)))))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("rootLogCost is given by the displayed expression."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cdy-gaussianpolynomiallog-rootlogcost-nonneg"),
                DeclarationHandle.Create(Module + ".rootLogCost_nonneg"),
                H("rootLogCost_nonneg"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Parenthesized(Seq(F.Id("v"), Sp, Colon, Sp, Q("NNReal"))), Comma, Sp, D(0), Sp, Leq, Sp, F.Id("rootLogCost"), Sp, F.Id("m"), Sp, F.Id("v")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("rootLogCost_nonneg satisfies the displayed statement."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("cdy-gaussianpolynomiallog-gaussian-polynomial-log-coeff-lower"),
                DeclarationHandle.Create(Module + ".gaussian_polynomial_log_coeff_lower"),
                H("gaussian_polynomial_log_coeff_lower"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Parenthesized(Seq(F.Id("v"), Sp, Colon, Sp, Q("NNReal"))), Sp, Parenthesized(Seq(F.Id("p"), Sp, Colon, Sp, F.Id("Polynomial"), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Parenthesized(Seq(F.Id("j"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Parenthesized(Seq(F.Id("v"), Sp, Neq, Sp, D(0))), Sp, To, Sp, Parenthesized(Seq(F.Id("p"), Dot, Sp, F.Id("coeff"), Sp, F.Id("j"), Sp, Neq, Sp, D(0))), Sp, To, Sp, F.Id("Real"), Dot, Sp, F.Id("log"), Sp, Vert, Sp, F.Id("p"), Dot, Sp, F.Id("coeff"), Sp, F.Id("j"), Vert, Sp, Minus, Sp, F.Id("p"), Dot, Sp, F.Id("natDegree"), Sp, Star, Sp, Parenthesized(Seq(F.Id("Real"), Dot, Sp, F.Id("log"), Sp, D(2), Sp, Plus, Sp, F.Id("rootLogCost"), Sp, F.Id("m"), Sp, F.Id("v"))), Sp, Leq, Sp, Int, Sp, F.Id("x"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Comma, Sp, F.Id("Real"), Dot, Sp, F.Id("log"), Sp, Vert, Sp, F.Id("p"), Dot, Sp, F.Id("eval"), Sp, Parenthesized(Seq(F.Id("x"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Vert, Sp, Q("d"), Sp, F.Id("gaussianReal"), Sp, F.Id("m"), Sp, F.Id("v")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("gaussian_polynomial_log_coeff_lower satisfies the displayed statement."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("cdy-gaussianpolynomiallog-gaussian-complex-pow-integrable"),
                DeclarationHandle.Create(Module + ".gaussian_complex_pow_integrable"),
                H("gaussian_complex_pow_integrable"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Parenthesized(Seq(F.Id("v"), Sp, Colon, Sp, Q("NNReal"))), Sp, Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, F.Id("Integrable"), Sp, Parenthesized(Seq(F.Id("fun"), Sp, F.Id("x"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Sp, Mapsto, Sp, new Formula.Power(Parenthesized(Seq(F.Id("x"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), F.Id("k")))), Sp, Parenthesized(Seq(F.Id("gaussianReal"), Sp, F.Id("m"), Sp, F.Id("v")))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("gaussian_complex_pow_integrable satisfies the displayed statement."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("cdy-gaussianpolynomiallog-norm-eq-two-pos-sub"),
                DeclarationHandle.Create(Module + ".norm_eq_two_pos_sub"),
                H("norm_eq_two_pos_sub"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("t"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Comma, Sp, Vert, Sp, F.Id("t"), Vert, Sp, Eq, Sp, D(2), Sp, Star, Sp, F.Id("max"), Sp, F.Id("t"), Sp, D(0), Sp, Minus, Sp, F.Id("t")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("norm_eq_two_pos_sub satisfies the displayed statement."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("cdy-gaussianpolynomiallog-integrable-prod-of-pos-and-fiber-lower"),
                DeclarationHandle.Create(Module + ".integrable_prod_of_pos_and_fiber_lower"),
                H("integrable_prod_of_pos_and_fiber_lower"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Seq(OpenBrace, Sp, Seq(Alpha, Sp, Beta, Sp, Colon, Sp, F.Id("Type"), Star, Sp), Sp, CloseBrace), Sp, Seq(OpenBracket, Sp, Seq(F.Id("MeasurableSpace"), Sp, Alpha), Sp, CloseBracket), Sp, Seq(OpenBracket, Sp, Seq(F.Id("MeasurableSpace"), Sp, Beta), Sp, CloseBracket), Sp, Parenthesized(Seq(Mu, Sp, Colon, Sp, F.Id("Measure"), Sp, Alpha)), Sp, Parenthesized(Seq(Nu, Sp, Colon, Sp, F.Id("Measure"), Sp, Beta)), Sp, Seq(OpenBracket, Sp, Seq(F.Id("SFinite"), Sp, Mu), Sp, CloseBracket), Sp, Seq(OpenBracket, Sp, Seq(F.Id("SFinite"), Sp, Nu), Sp, CloseBracket), Sp, Parenthesized(Seq(F.Id("f"), Sp, Colon, Sp, Alpha, Sp, Times, Sp, Beta, Sp, To, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Parenthesized(Seq(F.Id("g"), Sp, Colon, Sp, Beta, Sp, To, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Comma, Sp, Parenthesized(Seq(F.Id("AEStronglyMeasurable"), Sp, F.Id("f"), Sp, Parenthesized(Seq(Mu, Dot, Sp, F.Id("prod"), Sp, Nu)))), Sp, To, Sp, Parenthesized(Seq(F.Id("Integrable"), Sp, Parenthesized(Seq(F.Id("fun"), Sp, F.Id("z"), Sp, Mapsto, Sp, F.Id("max"), Sp, Parenthesized(Seq(F.Id("f"), Sp, F.Id("z"))), Sp, D(0))), Sp, Parenthesized(Seq(Mu, Dot, Sp, F.Id("prod"), Sp, Nu)))), Sp, To, Sp, Parenthesized(Seq(Seq(Forall, Caret, Grp(F.Id("ae")), Sp), Sp, F.Id("y"), Sp, Q("d"), Sp, Nu, Comma, Sp, F.Id("Integrable"), Sp, Parenthesized(Seq(F.Id("fun"), Sp, F.Id("x"), Sp, Mapsto, Sp, F.Id("f"), Sp, Parenthesized(Seq(F.Id("x"), Comma, Sp, F.Id("y"))))), Sp, Mu)), Sp, To, Sp, Parenthesized(Seq(F.Id("Integrable"), Sp, F.Id("g"), Sp, Nu)), Sp, To, Sp, Parenthesized(Seq(Seq(Forall, Caret, Grp(F.Id("ae")), Sp), Sp, F.Id("y"), Sp, Q("d"), Sp, Nu, Comma, Sp, F.Id("g"), Sp, F.Id("y"), Sp, Leq, Sp, Int, Sp, F.Id("x"), Comma, Sp, F.Id("f"), Sp, Parenthesized(Seq(F.Id("x"), Comma, Sp, F.Id("y"))), Sp, Q("d"), Sp, Mu)), Sp, To, Sp, F.Id("Integrable"), Sp, F.Id("f"), Sp, Parenthesized(Seq(Mu, Dot, Sp, F.Id("prod"), Sp, Nu))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("integrable_prod_of_pos_and_fiber_lower satisfies the displayed statement."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("cdy-gaussianpolynomiallog-covariance-affinegrampoly"),
                DeclarationHandle.Create(Module + ".affineGramPoly"),
                H("Covariance.affineGramPoly"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Seq(OpenBrace, Sp, Seq(F.Id("R"), Sp, Colon, Sp, F.Id("Type"), Star, Sp), Sp, CloseBrace), Sp, Seq(OpenBracket, Sp, Seq(F.Id("CommRing"), Sp, F.Id("R")), Sp, CloseBracket), Sp, Seq(OpenBracket, Sp, Seq(F.Id("StarRing"), Sp, F.Id("R")), Sp, CloseBracket), Sp, Seq(OpenBrace, Sp, Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N")))), Sp, CloseBrace), Sp, Parenthesized(Seq(F.Id("A"), Sp, F.Id("G"), Sp, Colon, Sp, F.Id("Matrix"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, F.Id("R"))), Comma, Sp, F.Id("Covariance"), Dot, Sp, F.Id("affineGramPoly"), Sp, F.Id("A"), Sp, F.Id("G"), Sp, Eq, Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("A"), Sp, Star, Sp, new Formula.Power(F.Id("A"), F.Id("H")))), Dot, Sp, F.Id("map"), Sp, F.Id("Polynomial"), Dot, Sp, F.Id("C"), Sp, Plus, Sp, Parenthesized(Seq(F.Id("Polynomial"), Dot, Sp, F.Id("X"), Sp, Colon, Sp, F.Id("Polynomial"), Sp, F.Id("R"))), Sp, Cdot, Sp, Parenthesized(Seq(F.Id("A"), Sp, Star, Sp, new Formula.Power(F.Id("G"), F.Id("H")), Sp, Plus, Sp, F.Id("G"), Sp, Star, Sp, new Formula.Power(F.Id("A"), F.Id("H")))), Dot, Sp, F.Id("map"), Sp, F.Id("Polynomial"), Dot, Sp, F.Id("C"), Sp, Plus, Sp, new Formula.Power(Parenthesized(Seq(F.Id("Polynomial"), Dot, Sp, F.Id("X"), Sp, Colon, Sp, F.Id("Polynomial"), Sp, F.Id("R"))), D(2)), Sp, Cdot, Sp, Parenthesized(Seq(F.Id("G"), Sp, Star, Sp, new Formula.Power(F.Id("G"), F.Id("H")))), Dot, Sp, F.Id("map"), Sp, F.Id("Polynomial"), Dot, Sp, F.Id("C")))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Covariance.affineGramPoly is given by the displayed expression."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cdy-gaussianpolynomiallog-covariance-pairdet"),
                DeclarationHandle.Create(Module + ".pairDet"),
                H("Covariance.pairDet"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Seq(OpenBrace, Sp, Seq(F.Id("R"), Sp, Colon, Sp, F.Id("Type"), Star, Sp), Sp, CloseBrace), Sp, Seq(OpenBracket, Sp, Seq(F.Id("CommRing"), Sp, F.Id("R")), Sp, CloseBracket), Sp, Seq(OpenBracket, Sp, Seq(F.Id("StarRing"), Sp, F.Id("R")), Sp, CloseBracket), Sp, Seq(OpenBrace, Sp, Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N")))), Sp, CloseBrace), Sp, Parenthesized(Seq(F.Id("A"), Sp, F.Id("C"), Sp, F.Id("G"), Sp, F.Id("K"), Sp, Colon, Sp, F.Id("Matrix"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, F.Id("R"))), Comma, Sp, F.Id("Covariance"), Dot, Sp, F.Id("pairDet"), Sp, F.Id("A"), Sp, F.Id("C"), Sp, F.Id("G"), Sp, F.Id("K"), Sp, Eq, Sp, Parenthesized(Seq(F.Id("Matrix"), Dot, Sp, F.Id("det"), Sp, Parenthesized(Seq(F.Id("affineGramPoly"), Sp, F.Id("A"), Sp, F.Id("G"), Sp, Q("Matrix", "kronecker"), Sp, Parenthesized(Seq(D(1), Sp, Colon, Sp, F.Id("Matrix"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("Polynomial"), Sp, F.Id("R"))))), Sp, Minus, Sp, Parenthesized(Seq(D(1), Sp, Colon, Sp, F.Id("Matrix"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("Polynomial"), Sp, F.Id("R"))))), Sp, Q("Matrix", "kronecker"), Sp, F.Id("affineGramPoly"), Sp, F.Id("C"), Sp, F.Id("K")))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Covariance.pairDet is given by the displayed expression."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cdy-gaussianpolynomiallog-covariance-rankone-order-lower"),
                DeclarationHandle.Create(Module + ".rankOne_order_lower"),
                H("Covariance.rankOne_order_lower"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Seq(OpenBrace, Sp, Seq(F.Id("R"), Sp, Colon, Sp, F.Id("Type"), Star, Sp), Sp, CloseBrace), Sp, Seq(OpenBracket, Sp, Seq(F.Id("CommRing"), Sp, F.Id("R")), Sp, CloseBracket), Sp, Seq(OpenBracket, Sp, Seq(F.Id("StarRing"), Sp, F.Id("R")), Sp, CloseBracket), Sp, Seq(OpenBracket, Sp, Seq(F.Id("Nontrivial"), Sp, F.Id("R")), Sp, CloseBracket), Sp, Seq(OpenBrace, Sp, Seq(F.Id("s"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N")))), Sp, CloseBrace), Sp, Parenthesized(Seq(F.Id("a"), Sp, Colon, Sp, F.Id("R"))), Sp, Parenthesized(Seq(F.Id("G"), Sp, F.Id("K"), Sp, Colon, Sp, F.Id("Matrix"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, Parenthesized(Seq(F.Id("s"), Plus, Sp, D(1))))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, Parenthesized(Seq(F.Id("s"), Plus, Sp, D(1))))), Sp, F.Id("R"))), Comma, Sp, new Formula.Power(Parenthesized(Seq(F.Id("Polynomial"), Dot, Sp, F.Id("X"), Sp, Colon, Sp, F.Id("Polynomial"), Sp, F.Id("R"))), Seq(D(2), Star, Sp, F.Id("s"), Star, Sp, F.Id("s"), Plus, Sp, D(1))), Sp, Mid, Sp, F.Id("pairDet"), Sp, Parenthesized(Seq(F.Id("Matrix"), Dot, Sp, F.Id("single"), Sp, D(0), Sp, D(0), Sp, F.Id("a"))), Sp, Parenthesized(Seq(F.Id("Matrix"), Dot, Sp, F.Id("single"), Sp, D(0), Sp, D(0), Sp, F.Id("a"))), Sp, F.Id("G"), Sp, F.Id("K")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Covariance.rankOne_order_lower satisfies the displayed statement."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("cdy-gaussianpolynomiallog-covariance-pairdet-degree-le"),
                DeclarationHandle.Create(Module + ".pairDet_degree_le"),
                H("Covariance.pairDet_degree_le"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Seq(OpenBrace, Sp, Seq(F.Id("R"), Sp, Colon, Sp, F.Id("Type"), Star, Sp), Sp, CloseBrace), Sp, Seq(OpenBracket, Sp, Seq(F.Id("CommRing"), Sp, F.Id("R")), Sp, CloseBracket), Sp, Seq(OpenBracket, Sp, Seq(F.Id("StarRing"), Sp, F.Id("R")), Sp, CloseBracket), Sp, Seq(OpenBracket, Sp, Seq(F.Id("Nontrivial"), Sp, F.Id("R")), Sp, CloseBracket), Sp, Seq(OpenBrace, Sp, Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N")))), Sp, CloseBrace), Sp, Parenthesized(Seq(F.Id("A"), Sp, F.Id("C"), Sp, F.Id("G"), Sp, F.Id("K"), Sp, Colon, Sp, F.Id("Matrix"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, F.Id("R"))), Comma, Sp, Parenthesized(Seq(F.Id("pairDet"), Sp, F.Id("A"), Sp, F.Id("C"), Sp, F.Id("G"), Sp, F.Id("K"))), Dot, Sp, F.Id("natDegree"), Sp, Leq, Sp, D(2), Star, Sp, F.Id("n"), Star, Sp, F.Id("n")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Covariance.pairDet_degree_le satisfies the displayed statement."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("cdy-gaussianpolynomiallog-covariance-pairdet-identity-noise-ne-zero"),
                DeclarationHandle.Create(Module + ".pairDet_identity_noise_ne_zero"),
                H("Covariance.pairDet_identity_noise_ne_zero"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Seq(OpenBrace, Sp, Seq(F.Id("R"), Sp, Colon, Sp, F.Id("Type"), Star, Sp), Sp, CloseBrace), Sp, Seq(OpenBracket, Sp, Seq(F.Id("CommRing"), Sp, F.Id("R")), Sp, CloseBracket), Sp, Seq(OpenBracket, Sp, Seq(F.Id("StarRing"), Sp, F.Id("R")), Sp, CloseBracket), Sp, Seq(OpenBracket, Sp, Seq(F.Id("Nontrivial"), Sp, F.Id("R")), Sp, CloseBracket), Sp, Seq(OpenBrace, Sp, Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N")))), Sp, CloseBrace), Sp, Parenthesized(Seq(F.Id("A"), Sp, F.Id("C"), Sp, Colon, Sp, F.Id("Matrix"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, F.Id("R"))), Comma, Sp, F.Id("pairDet"), Sp, F.Id("A"), Sp, F.Id("C"), Sp, D(1), Sp, D(0), Sp, Neq, Sp, D(0)))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Covariance.pairDet_identity_noise_ne_zero satisfies the displayed statement."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("cdy-gaussianpolynomiallog-covariance-pairdet-rankone-witness-order"),
                DeclarationHandle.Create(Module + ".pairDet_rankOne_witness_order"),
                H("Covariance.pairDet_rankOne_witness_order"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Seq(OpenBrace, Sp, Seq(F.Id("s"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N")))), Sp, CloseBrace), Sp, Parenthesized(Seq(F.Id("a"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Comma, Sp, Parenthesized(Seq(F.Id("a"), Sp, Neq, Sp, D(0))), Sp, To, Sp, Parenthesized(Seq(F.Id("pairDet"), Sp, Parenthesized(Seq(F.Id("Matrix"), Dot, Sp, F.Id("single"), Sp, D(0), Sp, D(0), Sp, Parenthesized(Seq(F.Id("a"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Sp, Parenthesized(Seq(F.Id("Matrix"), Dot, Sp, F.Id("single"), Sp, D(0), Sp, D(0), Sp, Parenthesized(Seq(F.Id("a"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Sp, Parenthesized(Seq(D(1), Sp, Colon, Sp, F.Id("Matrix"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, Parenthesized(Seq(F.Id("s"), Plus, Sp, D(1))))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, Parenthesized(Seq(F.Id("s"), Plus, Sp, D(1))))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, D(0))), Dot, Sp, F.Id("natTrailingDegree"), Sp, Eq, Sp, D(2), Star, Sp, F.Id("s"), Star, Sp, F.Id("s"), Plus, Sp, D(1)))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Covariance.pairDet_rankOne_witness_order satisfies the displayed statement."))), DescribeRole.Lemma))));

    private static Formula Q(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Probability;

internal sealed class SampleCovarianceBernoulliOrdersDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Analytic/Probability/SampleCovarianceBernoulliOrders";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/chafaidadounyoussef2024logenergy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "SampleCovarianceBernoulliOrders mathematical statements.",
        H("Sample Covariance Bernoulli Orders"),
        Blocks(
            Describe.Lean(DescribeId.Create("cdy-samplecovariancebernoulliorders-noise-noise"),
                DeclarationHandle.Create(Module + ".noise"),
                H("Noise.noise"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Seq(OpenBrace, Sp, Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N")))), Sp, CloseBrace), Sp, Parenthesized(Seq(F.Id("b"), Sp, Colon, Sp, F.Id("Bool"))), Comma, Sp, F.Id("Noise"), Dot, Sp, F.Id("noise"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Eq, Sp, F.Id("n"))), Sp, F.Id("b"), Sp, Eq, Sp, Parenthesized(Seq(F.Id("fun"), Sp, Parenthesized(Seq(F.Id("i"), Sp, F.Id("j"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("n"))), Sp, Mapsto, Sp, F.Id("MvPolynomial"), Dot, Sp, F.Id("X"), Sp, Parenthesized(Seq(F.Id("b"), Comma, Sp, F.Id("false"), Comma, Sp, F.Id("i"), Comma, Sp, F.Id("j"))), Sp, Plus, Sp, F.Id("MvPolynomial"), Dot, Sp, F.Id("C"), Sp, F.Id("Complex"), Dot, Sp, F.Id("I"), Sp, Star, Sp, F.Id("MvPolynomial"), Dot, Sp, F.Id("X"), Sp, Parenthesized(Seq(F.Id("b"), Comma, Sp, F.Id("true"), Comma, Sp, F.Id("i"), Comma, Sp, F.Id("j")))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Noise.noise is given by the displayed expression."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cdy-samplecovariancebernoulliorders-noise-poly"),
                DeclarationHandle.Create(Module + ".poly"),
                H("Noise.poly"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Seq(OpenBrace, Sp, Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N")))), Sp, CloseBrace), Sp, Parenthesized(Seq(F.Id("A"), Sp, F.Id("C"), Sp, Colon, Sp, F.Id("Matrix"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Comma, Sp, F.Id("Noise"), Dot, Sp, F.Id("poly"), Sp, F.Id("A"), Sp, F.Id("C"), Sp, Eq, Sp, Parenthesized(Seq(F.Id("D5"), Dot, Sp, F.Id("S3"), Dot, Sp, F.Id("Analytic"), Dot, Sp, F.Id("Probability"), Dot, Sp, F.Id("GaussianPolynomialLog"), Dot, Sp, F.Id("Covariance"), Dot, Sp, F.Id("pairDet"), Sp, Parenthesized(Parenthesized(Seq(F.Id("A"), Dot, Sp, F.Id("map"), Sp, F.Id("MvPolynomial"), Dot, Sp, F.Id("C")))), Sp, Parenthesized(Parenthesized(Seq(F.Id("C"), Dot, Sp, F.Id("map"), Sp, F.Id("MvPolynomial"), Dot, Sp, F.Id("C")))), Sp, Parenthesized(Seq(F.Id("noise"), Sp, F.Id("false"))), Sp, Parenthesized(Seq(F.Id("noise"), Sp, F.Id("true")))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Noise.poly is given by the displayed expression."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cdy-samplecovariancebernoulliorders-noise-evalnoise"),
                DeclarationHandle.Create(Module + ".evalNoise"),
                H("Noise.evalNoise"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Seq(OpenBrace, Sp, Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N")))), Sp, CloseBrace), Sp, Parenthesized(Seq(F.Id("G"), Sp, F.Id("K"), Sp, Colon, Sp, F.Id("Matrix"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Comma, Sp, F.Id("Noise"), Dot, Sp, F.Id("evalNoise"), Sp, F.Id("G"), Sp, F.Id("K"), Sp, Eq, Sp, Parenthesized(Seq(F.Id("MvPolynomial"), Dot, Sp, Seq(new Formula.Subscript(F.Id("eval"), D(2)), F.Id("Hom")), Sp, Parenthesized(Seq(F.Id("RingHom"), Dot, Sp, F.Id("id"), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Parenthesized(Seq(F.Id("fun"), Sp, Seq(Langle, Sp, Seq(F.Id("b"), Comma, Sp, F.Id("im"), Comma, Sp, F.Id("i"), Comma, Sp, F.Id("j")), Sp, Rangle), Sp, Mapsto, Sp, F.Id("if"), Sp, F.Id("im"), Sp, F.Id("then"), Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("if"), Sp, F.Id("b"), Sp, F.Id("then"), Sp, F.Id("K"), Sp, F.Id("i"), Sp, F.Id("j"), Sp, F.Id("else"), Sp, F.Id("G"), Sp, F.Id("i"), Sp, F.Id("j"))), Dot, Sp, F.Id("im"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, F.Id("else"), Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("if"), Sp, F.Id("b"), Sp, F.Id("then"), Sp, F.Id("K"), Sp, F.Id("i"), Sp, F.Id("j"), Sp, F.Id("else"), Sp, F.Id("G"), Sp, F.Id("i"), Sp, F.Id("j"))), Dot, Sp, F.Id("re"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C")))))))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Noise.evalNoise is given by the displayed expression."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cdy-samplecovariancebernoulliorders-noise-poly-ne-zero"),
                DeclarationHandle.Create(Module + ".poly_ne_zero"),
                H("Noise.poly_ne_zero"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Seq(OpenBrace, Sp, Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N")))), Sp, CloseBrace), Sp, Parenthesized(Seq(F.Id("A"), Sp, F.Id("C"), Sp, Colon, Sp, F.Id("Matrix"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Comma, Sp, F.Id("poly"), Sp, F.Id("A"), Sp, F.Id("C"), Sp, Neq, Sp, D(0)))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Noise.poly_ne_zero satisfies the displayed statement."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("cdy-samplecovariancebernoulliorders-events-w"),
                DeclarationHandle.Create(Module + ".w"),
                H("Events.w"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Seq(OpenBrace, Sp, Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N")))), Sp, CloseBrace), Sp, Parenthesized(Seq(F.Id("b"), Sp, Colon, Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("Bool"), Sp, Times, Sp, F.Id("Fin"), Sp, F.Id("n"), Sp, Times, Sp, F.Id("Fin"), Sp, F.Id("n"))), Sp, To, Sp, F.Id("Bool"))))), Comma, Sp, F.Id("Events"), Dot, Sp, F.Id("w"), Sp, F.Id("b"), Sp, Eq, Sp, Parenthesized(Seq(Prod, Sp, F.Id("i"), Comma, Sp, F.Id("if"), Sp, F.Id("b"), Sp, F.Id("i"), Sp, F.Id("then"), Sp, Parenthesized(Seq(D(1), Slash, Sp, D(2,5,6), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, F.Id("else"), Sp, D(2,5,5), Slash, Sp, D(2,5,6)))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Events.w is given by the displayed expression."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cdy-samplecovariancebernoulliorders-events-bmat"),
                DeclarationHandle.Create(Module + ".bmat"),
                H("Events.bmat"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Seq(OpenBrace, Sp, Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N")))), Sp, CloseBrace), Sp, Parenthesized(Seq(F.Id("b"), Sp, Colon, Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("Bool"), Sp, Times, Sp, F.Id("Fin"), Sp, F.Id("n"), Sp, Times, Sp, F.Id("Fin"), Sp, F.Id("n"))), Sp, To, Sp, F.Id("Bool"))))), Sp, Parenthesized(Seq(F.Id("side"), Sp, Colon, Sp, F.Id("Bool"))), Comma, Sp, F.Id("Events"), Dot, Sp, F.Id("bmat"), Sp, F.Id("b"), Sp, F.Id("side"), Sp, Eq, Sp, Parenthesized(Seq(F.Id("Matrix"), Dot, Sp, F.Id("of"), Sp, Parenthesized(Seq(F.Id("fun"), Sp, F.Id("i"), Sp, F.Id("j"), Sp, Mapsto, Sp, F.Id("if"), Sp, F.Id("b"), Sp, Parenthesized(Seq(F.Id("side"), Comma, Sp, F.Id("i"), Comma, Sp, F.Id("j"))), Sp, F.Id("then"), Sp, Parenthesized(Seq(F.Id("Real"), Dot, Sp, F.Id("sqrt"), Sp, D(2,5,5), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, F.Id("else"), Sp, Parenthesized(Seq(Minus, Sp, D(1), Slash, Sp, F.Id("Real"), Dot, Sp, F.Id("sqrt"), Sp, D(2,5,5), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R")))))))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Events.bmat is given by the displayed expression."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cdy-samplecovariancebernoulliorders-events-k"),
                DeclarationHandle.Create(Module + ".k"),
                H("Events.k"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Seq(OpenBrace, Sp, Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N")))), Sp, CloseBrace), Sp, Parenthesized(Seq(F.Id("b"), Sp, Colon, Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("Bool"), Sp, Times, Sp, F.Id("Fin"), Sp, F.Id("n"), Sp, Times, Sp, F.Id("Fin"), Sp, F.Id("n"))), Sp, To, Sp, F.Id("Bool"))))), Comma, Sp, F.Id("Events"), Dot, Sp, F.Id("k"), Sp, F.Id("b"), Sp, Eq, Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("poly"), Sp, Parenthesized(Seq(F.Id("bmat"), Sp, F.Id("b"), Sp, F.Id("false"))), Sp, Parenthesized(Seq(F.Id("bmat"), Sp, F.Id("b"), Sp, F.Id("true"))))), Dot, Sp, F.Id("natTrailingDegree")))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Events.k is given by the displayed expression."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cdy-samplecovariancebernoulliorders-events-l"),
                DeclarationHandle.Create(Module + ".L"),
                H("Events.L"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, F.Id("Events"), Dot, Sp, F.Id("L"), Sp, F.Id("n"), Sp, Eq, Sp, Parenthesized(Seq(Parenthesized(Seq(Sum, Sp, F.Id("b"), Sp, Colon, Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("Bool"), Sp, Times, Sp, F.Id("Fin"), Sp, F.Id("n"), Sp, Times, Sp, F.Id("Fin"), Sp, F.Id("n"))), Sp, To, Sp, F.Id("Bool"))), Comma, Sp, F.Id("w"), Sp, F.Id("b"), Sp, Star, Sp, F.Id("k"), Sp, F.Id("b"))), Sp, Slash, Sp, new Formula.Power(Parenthesized(Seq(F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), D(2))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Events.L is given by the displayed expression."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cdy-samplecovariancebernoulliorders-events-w-sum"),
                DeclarationHandle.Create(Module + ".w_sum"),
                H("Events.w_sum"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Sum, Sp, F.Id("b"), Sp, Colon, Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("Bool"), Sp, Times, Sp, F.Id("Fin"), Sp, F.Id("n"), Sp, Times, Sp, F.Id("Fin"), Sp, F.Id("n"))), Sp, To, Sp, F.Id("Bool"))), Comma, Sp, F.Id("w"), Sp, F.Id("b"), Sp, Eq, Sp, D(1)))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Events.w_sum satisfies the displayed statement."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("cdy-samplecovariancebernoulliorders-events-l-gap"),
                DeclarationHandle.Create(Module + ".L_gap"),
                H("Events.L_gap"),
                StatementSource.FromAuthor(Disp(Seq(F.Id("L"), Sp, D(2), Sp, Lt, Sp, F.Id("L"), Sp, D(3)))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Events.L_gap satisfies the displayed statement."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("cdy-samplecovariancebernoulliorders-noise-eval-pairdet"),
                DeclarationHandle.Create(Module + ".eval_pairDet"),
                H("Noise.eval_pairDet"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Seq(OpenBrace, Sp, Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N")))), Sp, CloseBrace), Sp, Parenthesized(Seq(Varepsilon, Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Parenthesized(Seq(F.Id("A"), Sp, F.Id("C"), Sp, F.Id("G"), Sp, F.Id("K"), Sp, Colon, Sp, F.Id("Matrix"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Comma, Sp, Parenthesized(Seq(F.Id("D5"), Dot, Sp, F.Id("S3"), Dot, Sp, F.Id("Analytic"), Dot, Sp, F.Id("Probability"), Dot, Sp, F.Id("GaussianPolynomialLog"), Dot, Sp, F.Id("Covariance"), Dot, Sp, F.Id("pairDet"), Sp, F.Id("A"), Sp, F.Id("C"), Sp, F.Id("G"), Sp, F.Id("K"))), Dot, Sp, F.Id("eval"), Sp, Parenthesized(Seq(Varepsilon, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Eq, Sp, F.Id("Matrix"), Dot, Sp, F.Id("det"), Sp, Parenthesized(Seq(Parenthesized(Seq(Parenthesized(Seq(F.Id("A"), Plus, Sp, Parenthesized(Seq(Varepsilon, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Cdot, Sp, F.Id("G"))), Star, Sp, new Formula.Power(Parenthesized(Seq(F.Id("A"), Plus, Sp, Parenthesized(Seq(Varepsilon, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Cdot, Sp, F.Id("G"))), F.Id("H")))), Sp, Q("Matrix", "kronecker"), Sp, Parenthesized(Seq(D(1), Sp, Colon, Sp, F.Id("Matrix"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Minus, Sp, Parenthesized(Seq(D(1), Sp, Colon, Sp, F.Id("Matrix"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Q("Matrix", "kronecker"), Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("C"), Plus, Sp, Parenthesized(Seq(Varepsilon, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Cdot, Sp, F.Id("K"))), Star, Sp, new Formula.Power(Parenthesized(Seq(F.Id("C"), Plus, Sp, Parenthesized(Seq(Varepsilon, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Cdot, Sp, F.Id("K"))), F.Id("H"))))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Noise.eval_pairDet satisfies the displayed statement."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("cdy-samplecovariancebernoulliorders-noise-polyat"),
                DeclarationHandle.Create(Module + ".polyAt"),
                H("Noise.polyAt"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Seq(OpenBrace, Sp, Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N")))), Sp, CloseBrace), Sp, Parenthesized(Seq(F.Id("A"), Sp, F.Id("C"), Sp, Colon, Sp, F.Id("Matrix"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Parenthesized(Seq(Varepsilon, Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Comma, Sp, F.Id("Noise"), Dot, Sp, F.Id("polyAt"), Sp, F.Id("A"), Sp, F.Id("C"), Sp, Varepsilon, Sp, Eq, Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("poly"), Sp, F.Id("A"), Sp, F.Id("C"))), Dot, Sp, F.Id("eval"), Sp, Parenthesized(Seq(F.Id("MvPolynomial"), Dot, Sp, F.Id("C"), Sp, Parenthesized(Seq(Varepsilon, Colon, Sp, Seq(Mathbb, Grp(F.Id("C")))))))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Noise.polyAt is given by the displayed expression."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cdy-samplecovariancebernoulliorders-noise-evalnoise-polyat"),
                DeclarationHandle.Create(Module + ".evalNoise_polyAt"),
                H("Noise.evalNoise_polyAt"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Seq(OpenBrace, Sp, Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N")))), Sp, CloseBrace), Sp, Parenthesized(Seq(Varepsilon, Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Parenthesized(Seq(F.Id("A"), Sp, F.Id("C"), Sp, F.Id("G"), Sp, F.Id("K"), Sp, Colon, Sp, F.Id("Matrix"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Comma, Sp, F.Id("evalNoise"), Sp, F.Id("G"), Sp, F.Id("K"), Sp, Parenthesized(Seq(F.Id("polyAt"), Sp, F.Id("A"), Sp, F.Id("C"), Sp, Varepsilon)), Sp, Eq, Sp, Parenthesized(Seq(F.Id("D5"), Dot, Sp, F.Id("S3"), Dot, Sp, F.Id("Analytic"), Dot, Sp, F.Id("Probability"), Dot, Sp, F.Id("GaussianPolynomialLog"), Dot, Sp, F.Id("Covariance"), Dot, Sp, F.Id("pairDet"), Sp, F.Id("A"), Sp, F.Id("C"), Sp, F.Id("G"), Sp, F.Id("K"))), Dot, Sp, F.Id("eval"), Sp, Parenthesized(Seq(Varepsilon, Colon, Sp, Seq(Mathbb, Grp(F.Id("C")))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Noise.evalNoise_polyAt satisfies the displayed statement."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("cdy-samplecovariancebernoulliorders-noise-polyat-ne-zero"),
                DeclarationHandle.Create(Module + ".polyAt_ne_zero"),
                H("Noise.polyAt_ne_zero"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Seq(OpenBrace, Sp, Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N")))), Sp, CloseBrace), Sp, Parenthesized(Seq(F.Id("A"), Sp, F.Id("C"), Sp, Colon, Sp, F.Id("Matrix"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Parenthesized(Seq(Varepsilon, Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Comma, Sp, Parenthesized(Seq(Varepsilon, Sp, Neq, Sp, D(0))), Sp, To, Sp, F.Id("polyAt"), Sp, F.Id("A"), Sp, F.Id("C"), Sp, Varepsilon, Sp, Neq, Sp, D(0)))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Noise.polyAt_ne_zero satisfies the displayed statement."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("cdy-samplecovariancebernoulliorders-gaussian-noisefamily"),
                DeclarationHandle.Create(Module + ".noiseFamily"),
                H("Gaussian.noiseFamily"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Seq(OpenBrace, Sp, Seq(F.Id("n"), Sp, F.Id("N"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N")))), Sp, CloseBrace), Sp, Parenthesized(Seq(F.Id("q"), Sp, Colon, Sp, F.Id("Fin"), Sp, Parenthesized(Seq(F.Id("N"), Plus, Sp, D(1))), Sp, To, Sp, F.Id("MvPolynomial"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Parenthesized(Seq(Varepsilon, Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Comma, Sp, F.Id("Gaussian"), Dot, Sp, F.Id("noiseFamily"), Sp, F.Id("q"), Sp, Varepsilon, Sp, Eq, Sp, Parenthesized(Seq(Sum, Sp, F.Id("k"), Sp, Colon, Sp, F.Id("Fin"), Sp, Parenthesized(Seq(F.Id("N"), Plus, Sp, D(1))), Comma, Sp, F.Id("MvPolynomial"), Dot, Sp, F.Id("C"), Sp, Parenthesized(new Formula.Power(Parenthesized(Seq(Varepsilon, Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Seq(F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N")))))), Sp, Star, Sp, F.Id("q"), Sp, F.Id("k")))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Gaussian.noiseFamily is given by the displayed expression."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cdy-samplecovariancebernoulliorders-gaussian-gaussian-mv-log-integrable"),
                DeclarationHandle.Create(Module + ".gaussian_mv_log_integrable"),
                H("Gaussian.gaussian_mv_log_integrable"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Parenthesized(Seq(F.Id("v"), Sp, Colon, Sp, Q("NNReal"))), Sp, Seq(OpenBrace, Sp, Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N")))), Sp, CloseBrace), Sp, Parenthesized(Seq(F.Id("p"), Sp, Colon, Sp, F.Id("MvPolynomial"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Comma, Sp, F.Id("v"), Sp, Neq, Sp, D(0), Sp, To, Sp, F.Id("p"), Sp, Neq, Sp, D(0), Sp, To, Sp, Parenthesized(Seq(Seq(Forall, Caret, Grp(F.Id("ae")), Sp), Sp, F.Id("x"), Sp, Q("d"), Sp, F.Id("Measure"), Dot, Sp, F.Id("pi"), Sp, Parenthesized(Seq(F.Id("Function"), Dot, Sp, F.Id("const"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("gaussianReal"), Sp, F.Id("m"), Sp, F.Id("v"))))), Comma, Sp, F.Id("MvPolynomial"), Dot, Sp, F.Id("eval"), Sp, Parenthesized(Seq(F.Id("fun"), Sp, F.Id("i"), Sp, Mapsto, Sp, Parenthesized(Seq(F.Id("x"), Sp, F.Id("i"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Sp, F.Id("p"), Sp, Neq, Sp, D(0))), Sp, Land, Sp, F.Id("Integrable"), Sp, Parenthesized(Seq(F.Id("fun"), Sp, F.Id("x"), Sp, Mapsto, Sp, F.Id("Real"), Dot, Sp, F.Id("log"), Sp, Vert, Sp, F.Id("MvPolynomial"), Dot, Sp, F.Id("eval"), Sp, Parenthesized(Seq(F.Id("fun"), Sp, F.Id("i"), Sp, Mapsto, Sp, Parenthesized(Seq(F.Id("x"), Sp, F.Id("i"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Sp, F.Id("p"), Vert, Sp)), Sp, Parenthesized(Seq(F.Id("Measure"), Dot, Sp, F.Id("pi"), Sp, Parenthesized(Seq(F.Id("Function"), Dot, Sp, F.Id("const"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("gaussianReal"), Sp, F.Id("m"), Sp, F.Id("v")))))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Gaussian.gaussian_mv_log_integrable satisfies the displayed statement."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("cdy-samplecovariancebernoulliorders-gaussian-gaussian-noisefamily-log-order"),
                DeclarationHandle.Create(Module + ".gaussian_noiseFamily_log_order"),
                H("Gaussian.gaussian_noiseFamily_log_order"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Seq(OpenBrace, Sp, Seq(F.Id("n"), Sp, F.Id("N"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N")))), Sp, CloseBrace), Sp, Parenthesized(Seq(F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Parenthesized(Seq(F.Id("v"), Sp, Colon, Sp, Q("NNReal"))), Sp, Parenthesized(Seq(F.Id("q"), Sp, Colon, Sp, F.Id("Fin"), Sp, Parenthesized(Seq(F.Id("N"), Plus, Sp, D(1))), Sp, To, Sp, F.Id("MvPolynomial"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("n"), Sp, Seq(To, Underscore, Grp(D(0))), Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, F.Id("v"), Sp, Neq, Sp, D(0), Sp, To, Sp, Parenthesized(Seq(F.Id("q"), Sp, D(0))), Dot, Sp, F.Id("coeff"), Sp, F.Id("d"), Sp, Neq, Sp, D(0), Sp, To, Sp, F.Id("Tendsto"), Sp, Parenthesized(Seq(F.Id("fun"), Sp, Varepsilon, Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Sp, Mapsto, Sp, Minus, Sp, Parenthesized(Seq(Int, Sp, F.Id("x"), Comma, Sp, F.Id("Real"), Dot, Sp, F.Id("log"), Sp, Vert, Sp, new Formula.Power(Parenthesized(Seq(Varepsilon, Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), F.Id("k")), Sp, Star, Sp, F.Id("MvPolynomial"), Dot, Sp, F.Id("eval"), Sp, Parenthesized(Seq(F.Id("fun"), Sp, F.Id("i"), Sp, Mapsto, Sp, Parenthesized(Seq(F.Id("x"), Sp, F.Id("i"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Sp, Parenthesized(Seq(F.Id("noiseFamily"), Sp, F.Id("q"), Sp, Varepsilon)), Vert, Sp, Q("d"), Sp, F.Id("Measure"), Dot, Sp, F.Id("pi"), Sp, Parenthesized(Seq(F.Id("Function"), Dot, Sp, F.Id("const"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("gaussianReal"), Sp, F.Id("m"), Sp, F.Id("v"))))))), Sp, Slash, Sp, F.Id("Real"), Dot, Sp, F.Id("log"), Sp, Parenthesized(Seq(D(1), Slash, Sp, Varepsilon)))), Sp, Parenthesized(Seq(Seq(Mathcal, Grp(F.Id("N"))), Sp, Seq(OpenBracket, Sp, Seq(Gt, Sp), Sp, CloseBracket), Sp, D(0))), Sp, Parenthesized(Seq(Seq(Mathcal, Grp(F.Id("N"))), Sp, Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R")))))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Gaussian.gaussian_noiseFamily_log_order satisfies the displayed statement."))), DescribeRole.Lemma))));

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

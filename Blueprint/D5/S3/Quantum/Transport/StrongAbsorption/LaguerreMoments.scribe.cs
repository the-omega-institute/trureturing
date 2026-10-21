using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Transport.StrongAbsorption;

internal sealed class LaguerreMomentsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "LaguerreMoments for the strong-absorption cumulant expansion.",
        H("LaguerreMoments"),
        Blocks(
            Paragraph(Text("Natural-number subtraction is truncated. Unmarked integrals use volume; real-number powers and division use the real field.")),
            Describe.Lean(DescribeId.Create("deltasq"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.deltaSq"),
                H("deltaSq"), StatementSource.FromAuthor(Disp(F0())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The squared Vandermonde product."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("deltapoly"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.deltaPoly"),
                H("deltaPoly"), StatementSource.FromAuthor(Disp(F1())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed definition is used in the moment and density expansions."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("expjet"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.expJet"),
                H("expJet"), StatementSource.FromAuthor(Disp(F3())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed definition is used in the moment and density expansions."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("correctionjet"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.correctionJet"),
                H("correctionJet"), StatementSource.FromAuthor(Disp(F4())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed definition is used in the moment and density expansions."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("exp-deriv-near"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.exp_deriv_near"),
                H("exp_deriv_near"), StatementSource.FromAuthor(Disp(F5())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("laguerreweight"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.laguerreWeight"),
                H("laguerreWeight"), StatementSource.FromAuthor(Disp(F6())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed definition is used in the moment and density expansions."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("deltapoly-eval"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.deltaPoly_eval"),
                H("deltaPoly_eval"), StatementSource.FromAuthor(Disp(F7())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("deltasq-nonneg"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.deltaSq_nonneg"),
                H("deltaSq_nonneg"), StatementSource.FromAuthor(Disp(F8())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exp-jet-recurrence"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.exp_jet_recurrence"),
                H("exp_jet_recurrence"), StatementSource.FromAuthor(Disp(F9())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gammacgf-analytic"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.gammaCGF_analytic"),
                H("gammaCGF_analytic"), StatementSource.FromAuthor(Disp(F10())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("correctioncgf-analytic"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.correctionCGF_analytic"),
                H("correctionCGF_analytic"), StatementSource.FromAuthor(Disp(F11())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("firstorder-congr-eventually"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.congr_eventually"),
                H("FirstOrder.congr_eventually"), StatementSource.FromAuthor(Disp(F12())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("partition"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.partition"),
                H("partition"), StatementSource.FromAuthor(Disp(F13())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The integral of the Laguerre weight on the nonnegative orthant."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("laguerreweight-integrable"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.laguerreWeight_integrable"),
                H("laguerreWeight_integrable"), StatementSource.FromAuthor(Disp(F14())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("laguerreweight-nonneg"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.laguerreWeight_nonneg"),
                H("laguerreWeight_nonneg"), StatementSource.FromAuthor(Disp(F15())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("laguerrepolynomial-integrable"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.laguerrePolynomial_integrable"),
                H("laguerrePolynomial_integrable"), StatementSource.FromAuthor(Disp(F16())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("singlewpoly-eval"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.singleWPoly_eval"),
                H("singleWPoly_eval"), StatementSource.FromAuthor(Disp(F17())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("correction-jet-recurrence"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.correction_jet_recurrence"),
                H("correction_jet_recurrence"), StatementSource.FromAuthor(Disp(F18())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("partition-pos"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.partition_pos"),
                H("partition_pos"), StatementSource.FromAuthor(Disp(F19())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("laguerremoment"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.laguerreMoment"),
                H("laguerreMoment"), StatementSource.FromAuthor(Disp(F20())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed definition is used in the moment and density expansions."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("laguerreweightedmeasure"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.laguerreWeightedMeasure"),
                H("laguerreWeightedMeasure"), StatementSource.FromAuthor(Disp(F21())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed definition is used in the moment and density expansions."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("singlewpoly-nonneg"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.singleWPoly_nonneg"),
                H("singleWPoly_nonneg"), StatementSource.FromAuthor(Disp(F22())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("laguerreh"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.laguerreH"),
                H("laguerreH"), StatementSource.FromAuthor(Disp(F23())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed definition is used in the moment and density expansions."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("laguerrehw"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.laguerreHw"),
                H("laguerreHw"), StatementSource.FromAuthor(Disp(F24())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed definition is used in the moment and density expansions."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cumulant-expansion-of-moments"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.cumulant_expansion_of_moments"),
                H("cumulant_expansion_of_moments"), StatementSource.FromAuthor(Disp(F25())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("laguerreweighted-mgf-derivative"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.laguerreWeighted_mgf_derivative"),
                H("laguerreWeighted_mgf_derivative"), StatementSource.FromAuthor(Disp(F26())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("laguerre-p1"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.laguerre_p1"),
                H("laguerre_p1"), StatementSource.FromAuthor(Disp(F27())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("laguerreh-near"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.laguerreH_near"),
                H("laguerreH_near"), StatementSource.FromAuthor(Disp(F28())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("laguerreh-iterated"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.laguerreH_iterated"),
                H("laguerreH_iterated"), StatementSource.FromAuthor(Disp(F29())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("laguerrehw-near"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.laguerreHw_near"),
                H("laguerreHw_near"), StatementSource.FromAuthor(Disp(F30())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("published-derivation-product-eigen"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.derivation_product_eigen"),
                H("derivation_product_eigen"), StatementSource.FromAuthor(Disp(Published0())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed formula relates the polynomial integrals and the normalized finite-channel measure."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("published-orthant-measure"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.orthant_measure"),
                H("orthant_measure"), StatementSource.FromAuthor(Disp(Published2())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed formula relates the polynomial integrals and the normalized finite-channel measure."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("published-polynomial-exp-integrable-single"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.polynomial_exp_integrable_single"),
                H("polynomial_exp_integrable_single"), StatementSource.FromAuthor(Disp(Published3())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed formula relates the polynomial integrals and the normalized finite-channel measure."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("published-polyintegral"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.polyIntegral"),
                H("polyIntegral"), StatementSource.FromAuthor(Disp(Published4())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed formula relates the polynomial integrals and the normalized finite-channel measure."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("published-polyintegral-add"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.polyIntegral_add"),
                H("polyIntegral_add"), StatementSource.FromAuthor(Disp(Published5())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed formula relates the polynomial integrals and the normalized finite-channel measure."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("published-polyintegral-sum"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.polyIntegral_sum"),
                H("polyIntegral_sum"), StatementSource.FromAuthor(Disp(Published6())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed formula relates the polynomial integrals and the normalized finite-channel measure."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("published-polyintegral-x-sq"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.polyIntegral_X_sq"),
                H("polyIntegral_X_sq"), StatementSource.FromAuthor(Disp(Published7())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed formula relates the polynomial integrals and the normalized finite-channel measure."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("published-laguerre-p2"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.laguerre_p2"),
                H("laguerre_p2"), StatementSource.FromAuthor(Disp(Published8())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed formula relates the polynomial integrals and the normalized finite-channel measure."))), DescribeRole.Theorem)
        )));

    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Qualified(params string[] names)
    {
        var items = new List<Formula>();
        foreach (var name in names)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(Seq(Operatorname, Grp(V(name))));
        }
        return Seq([.. items]);
    }
    private static Formula Sup(Formula value) => Seq(Caret, Grp(value));

    private static Formula PolynomialSquareMean() =>
        Seq(Qualified("Finset", "expect"), Sp, Qualified("Finset", "univ"), Sp,
            Parenthesized(Seq(V("fun"), Sp, V("i"), Sp, Colon, Sp, V("Fin"), Sp, V("M"), Sp, Mapsto, Sp,
                Parenthesized(Seq(new Formula.Power(Parenthesized(Seq(V("X"), Sp, V("i"))), D(2)), Sp, Colon, Sp,
                    V("MvPolynomial"), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, Seq(Mathbb, Grp(V("R"))))))));

    private static Formula F0() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("x"), Sp, Colon, Sp, V("Fin"), Sp, V("M"), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, V("deltaSq"), Sp, V("M"), Sp, V("x"), Sp, Eq, Sp, Parenthesized(Seq(Prod, Sp, V("i"), Sp, Comma, Sp, Prod, Sp, V("j"), Sp, Comma, Sp, V("if"), Sp, V("i"), Sp, Lt, Sp, V("j"), Sp, V("then"), Sp, Sp, new Formula.Power(Parenthesized(Seq(V("x"), Sp, V("i"), Sp, Minus, Sp, V("x"), Sp, V("j"))), D(2)), Sp, V("else"), Sp, D(1))));

    private static Formula F1() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, V("deltaPoly"), Sp, V("M"), Sp, Eq, Sp, Parenthesized(Seq(Prod, Sp, V("i"), Sp, Comma, Sp, Prod, Sp, V("j"), Sp, Comma, Sp, V("if"), Sp, V("i"), Sp, Lt, Sp, V("j"), Sp, V("then"), Sp, Sp, new Formula.Power(Parenthesized(Seq(Qualified("MvPolynomial","X"), Sp, V("i"), Sp, Minus, Sp, Qualified("MvPolynomial","X"), Sp, V("j"))), D(2)), Sp, V("else"), Sp, D(1))));

    private static Formula F3() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("K"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("r"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, V("expJet"), Sp, V("K"), Sp, V("r"), Sp, Eq, Sp, Parenthesized(Seq(V("iteratedDeriv"), Sp, V("r"), Sp, Parenthesized(Seq(V("fun"), Sp, V("t"), Sp, Mapsto, Sp, Qualified("Real","exp"), Sp, Parenthesized(Seq(V("K"), Sp, V("t"))))), Sp, D(0))));

    private static Formula F4() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("K"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("B"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("r"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, V("correctionJet"), Sp, V("K"), Sp, V("B"), Sp, V("r"), Sp, Eq, Sp, Parenthesized(Seq(V("iteratedDeriv"), Sp, V("r"), Sp, Parenthesized(Seq(V("fun"), Sp, V("t"), Sp, Mapsto, Sp, Qualified("Real","exp"), Sp, Parenthesized(Seq(V("K"), Sp, V("t"))), Sp, Cdot, Sp, V("B"), Sp, V("t"))), Sp, D(0))));

    private static Formula F5() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("K"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Parenthesized(Seq(V("AnalyticAt"), Sp, Seq(Mathbb, Grp(V("R"))), Sp, V("K"), Sp, D(0))), Sp, To, Sp, V("deriv"), Sp, Parenthesized(Seq(V("fun"), Sp, V("t"), Sp, Mapsto, Sp, Qualified("Real","exp"), Sp, Parenthesized(Seq(V("K"), Sp, V("t"))))), Sp, Seq(Eq, Sup(V("f"))), Sp, Seq(OpenBracket, Seq(V("nhds"), Sp, D(0)), CloseBracket), Sp, Parenthesized(Seq(V("fun"), Sp, V("t"), Sp, Mapsto, Sp, V("deriv"), Sp, V("K"), Sp, V("t"), Sp, Cdot, Sp, Qualified("Real","exp"), Sp, Parenthesized(Seq(V("K"), Sp, V("t"))))));

    private static Formula F6() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("a"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("x"), Sp, Colon, Sp, V("Fin"), Sp, V("M"), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, V("laguerreWeight"), Sp, V("M"), Sp, V("a"), Sp, V("x"), Sp, Eq, Sp, Parenthesized(Seq(V("if"), Sp, Forall, Sp, V("i"), Sp, Comma, Sp, D(0), Sp, Le, Sp, V("x"), Sp, V("i"), Sp, V("then"), Sp, Qualified("Real","exp"), Sp, Parenthesized(Seq(Minus, Sp, V("a"), Sp, Cdot, Sp, Sum, Sp, V("i"), Sp, Comma, Sp, V("x"), Sp, V("i"))), Sp, Cdot, Sp, V("deltaSq"), Sp, V("M"), Sp, V("x"), Sp, V("else"), Sp, D(0))));

    private static Formula F7() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("x"), Sp, Colon, Sp, V("Fin"), Sp, V("M"), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Qualified("MvPolynomial","eval"), Sp, V("x"), Sp, Parenthesized(Seq(V("deltaPoly"), Sp, V("M"))), Sp, Eq, Sp, V("deltaSq"), Sp, V("M"), Sp, V("x"));

    private static Formula F8() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("x"), Sp, Colon, Sp, V("Fin"), Sp, V("M"), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, D(0), Sp, Le, Sp, V("deltaSq"), Sp, V("M"), Sp, V("x"));

    private static Formula F9() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("K"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Parenthesized(Seq(V("AnalyticAt"), Sp, Seq(Mathbb, Grp(V("R"))), Sp, V("K"), Sp, D(0))), Sp, To, Sp, Parenthesized(Seq(V("K"), Sp, D(0), Sp, Eq, Sp, D(0))), Sp, To, Sp, V("iteratedDeriv"), Sp, Parenthesized(Seq(V("n"), Sp, Plus, Sp, D(1))), Sp, V("K"), Sp, D(0), Sp, Eq, Sp, V("expJet"), Sp, V("K"), Sp, Parenthesized(Seq(V("n"), Sp, Plus, Sp, D(1))), Sp, Minus, Sp, Sum, Sp, V("i"), Sp, InMacro, Sp, V("range"), Sp, V("n"), Sp, Comma, Sp, Parenthesized(Seq(Qualified("n","choose"), Sp, V("i"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Cdot, Sp, V("iteratedDeriv"), Sp, Parenthesized(Seq(V("i"), Sp, Plus, Sp, D(1))), Sp, V("K"), Sp, D(0), Sp, Cdot, Sp, V("expJet"), Sp, V("K"), Sp, Parenthesized(Seq(V("n"), Sp, Minus, Sp, V("i"))));

    private static Formula F10() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, V("AnalyticAt"), Sp, Seq(Mathbb, Grp(V("R"))), Sp, Parenthesized(Seq(V("gammaCGF"), Sp, V("d"))), Sp, D(0));

    private static Formula F11() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, V("AnalyticAt"), Sp, Seq(Mathbb, Grp(V("R"))), Sp, Parenthesized(Seq(V("correctionCGF"), Sp, V("d"))), Sp, D(0));

    private static Formula F12() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("f"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("g"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("a"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("b"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Parenthesized(Seq(V("FirstOrder"), Sp, V("f"), Sp, V("a"), Sp, V("b"))), Sp, To, Sp, Parenthesized(Seq(V("f"), Sp, Seq(Eq, Sup(V("f"))), Sp, Seq(OpenBracket, V("atTop"), CloseBracket), Sp, V("g"))), Sp, To, Sp, V("FirstOrder"), Sp, V("g"), Sp, V("a"), Sp, V("b"));

    private static Formula F13() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("a"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, V("partition"), Sp, V("M"), Sp, V("a"), Sp, Eq, Sp, Parenthesized(Seq(Int, Sp, V("x"), Sp, Comma, Sp, V("laguerreWeight"), Sp, V("M"), Sp, V("a"), Sp, V("x"))));

    private static Formula F14() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("a"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Parenthesized(Seq(D(0), Sp, Lt, Sp, V("a"))), Sp, To, Sp, V("Integrable"), Sp, Parenthesized(Seq(V("laguerreWeight"), Sp, V("M"), Sp, V("a"))));

    private static Formula F15() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("a"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("x"), Sp, Colon, Sp, V("Fin"), Sp, V("M"), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, D(0), Sp, Le, Sp, V("laguerreWeight"), Sp, V("M"), Sp, V("a"), Sp, V("x"));

    private static Formula F16() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("a"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("P"), Sp, Colon, Sp, V("MvPolynomial"), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Parenthesized(Seq(D(0), Sp, Lt, Sp, V("a"))), Sp, To, Sp, V("Integrable"), Sp, Parenthesized(Seq(V("fun"), Sp, V("x"), Sp, Mapsto, Sp, V("laguerreWeight"), Sp, V("M"), Sp, V("a"), Sp, V("x"), Sp, Cdot, Sp, V("eval"), Sp, V("x"), Sp, V("P"))));

    private static Formula F17() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("x"), Sp, Colon, Sp, V("Fin"), Sp, V("M"), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, V("eval"), Sp, V("x"), Sp, Parenthesized(PolynomialSquareMean()), Sp, Eq, Sp, Parenthesized(Seq(Qualified("Finset","expect"), Sp, Qualified("Finset","univ"), Sp, Parenthesized(Seq(V("fun"), Sp, V("i"), Sp, Mapsto, Sp, Sp, new Formula.Power(Parenthesized(Seq(V("x"), Sp, V("i"))), D(2)))))));

    private static Formula F18() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("K"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("B"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Parenthesized(Seq(V("AnalyticAt"), Sp, Seq(Mathbb, Grp(V("R"))), Sp, V("K"), Sp, D(0))), Sp, To, Sp, Parenthesized(Seq(V("AnalyticAt"), Sp, Seq(Mathbb, Grp(V("R"))), Sp, V("B"), Sp, D(0))), Sp, To, Sp, Parenthesized(Seq(V("K"), Sp, D(0), Sp, Eq, Sp, D(0))), Sp, To, Sp, Parenthesized(Seq(V("B"), Sp, D(0), Sp, Eq, Sp, D(0))), Sp, To, Sp, V("iteratedDeriv"), Sp, Parenthesized(Seq(V("n"), Sp, Plus, Sp, D(1))), Sp, V("B"), Sp, D(0), Sp, Eq, Sp, V("correctionJet"), Sp, V("K"), Sp, V("B"), Sp, Parenthesized(Seq(V("n"), Sp, Plus, Sp, D(1))), Sp, Minus, Sp, Sum, Sp, V("i"), Sp, InMacro, Sp, V("range"), Sp, V("n"), Sp, Comma, Sp, Parenthesized(Seq(Qualified("n","choose"), Sp, V("i"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Cdot, Sp, Parenthesized(Seq(V("iteratedDeriv"), Sp, Parenthesized(Seq(V("i"), Sp, Plus, Sp, D(1))), Sp, V("K"), Sp, D(0), Sp, Cdot, Sp, V("correctionJet"), Sp, V("K"), Sp, V("B"), Sp, Parenthesized(Seq(V("n"), Sp, Minus, Sp, V("i"))), Sp, Plus, Sp, V("iteratedDeriv"), Sp, Parenthesized(Seq(V("i"), Sp, Plus, Sp, D(1))), Sp, V("B"), Sp, D(0), Sp, Cdot, Sp, V("expJet"), Sp, V("K"), Sp, Parenthesized(Seq(V("n"), Sp, Minus, Sp, V("i"))))));

    private static Formula F19() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("a"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Parenthesized(Seq(D(0), Sp, Lt, Sp, V("a"))), Sp, To, Sp, D(0), Sp, Lt, Sp, V("partition"), Sp, V("M"), Sp, V("a"));

    private static Formula F20() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("r"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("a"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, V("laguerreMoment"), Sp, V("M"), Sp, V("r"), Sp, V("a"), Sp, Eq, Sp, Parenthesized(Seq(Parenthesized(Seq(Int, Sp, V("x"), Sp, Comma, Sp, Parenthesized(Seq(Sum, Sp, V("i"), Sp, Colon, Sp, V("Fin"), Sp, V("M"), Sp, Comma, Sp, Sp, new Formula.Power(Parenthesized(Seq(V("x"), Sp, V("i"))), V("r")))), Sp, Cdot, Sp, V("laguerreWeight"), Sp, V("M"), Sp, V("a"), Sp, V("x"))), Sp, Slash, Sp, V("partition"), Sp, V("M"), Sp, V("a"))));

    private static Formula F21() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("Q"), Sp, Colon, Sp, V("MvPolynomial"), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, V("laguerreWeightedMeasure"), Sp, V("M"), Sp, V("Q"), Sp, Eq, Sp, Parenthesized(Seq(new Formula.Power(Parenthesized(Seq(Qualified("ENNReal","ofReal"), Sp, Parenthesized(Seq(V("partition"), Sp, V("M"), Sp, V("M"))))), Seq(Minus, D(1))), Sp, Cdot, Sp, Qualified("volume","withDensity"), Sp, Parenthesized(Seq(V("fun"), Sp, V("x"), Sp, Mapsto, Sp, Qualified("ENNReal","ofReal"), Sp, Parenthesized(Seq(V("laguerreWeight"), Sp, V("M"), Sp, V("M"), Sp, V("x"), Sp, Cdot, Sp, V("eval"), Sp, V("x"), Sp, V("Q"))))))));

    private static Formula F22() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("x"), Sp, Colon, Sp, V("Fin"), Sp, V("M"), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, D(0), Sp, Le, Sp, V("eval"), Sp, V("x"), Sp, Parenthesized(PolynomialSquareMean()));

    private static Formula F23() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, V("laguerreH"), Sp, V("M"), Sp, Eq, Sp, Parenthesized(Seq(V("mgf"), Sp, Parenthesized(Parenthesized(Seq(V("fun"), Sp, V("x"), Sp, Colon, Sp, V("Fin"), Sp, V("M"), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))), Sp, Mapsto, Sp, Qualified("Finset","expect"), Sp, Qualified("Finset","univ"), Sp, V("x")))), Sp, Parenthesized(Seq(V("laguerreWeightedMeasure"), Sp, V("M"), Sp, D(1))))));

    private static Formula F24() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, V("laguerreHw"), Sp, V("M"), Sp, Eq, Sp, Parenthesized(Seq(V("mgf"), Sp, Parenthesized(Parenthesized(Seq(V("fun"), Sp, V("x"), Sp, Colon, Sp, V("Fin"), Sp, V("M"), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))), Sp, Mapsto, Sp, Qualified("Finset","expect"), Sp, Qualified("Finset","univ"), Sp, V("x")))), Sp, Parenthesized(Seq(V("laguerreWeightedMeasure"), Sp, V("M"), Sp, Parenthesized(PolynomialSquareMean()))))));

    private static Formula F25() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("a"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("b"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("c"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Parenthesized(Seq(Forall, Sp, V("r"), Sp, Comma, Sp, V("FirstOrder"), Sp, Parenthesized(Seq(V("m"), Sp, V("r"))), Sp, Parenthesized(Seq(V("a"), Sp, V("r"))), Sp, Parenthesized(Seq(V("b"), Sp, V("r"))))), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, GammaLower, Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))), Sp, Comma, Sp, D(0), Sp, Lt, Sp, GammaLower, Sp, To, Sp, Forall, Sp, V("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))), Sp, Comma, Sp, V("k"), Sp, Parenthesized(Seq(V("n"), Sp, Plus, Sp, D(1))), Sp, GammaLower, Sp, Eq, Sp, V("m"), Sp, Parenthesized(Seq(V("n"), Sp, Plus, Sp, D(1))), Sp, GammaLower, Sp, Minus, Sp, Sum, Sp, V("i"), Sp, InMacro, Sp, V("range"), Sp, V("n"), Sp, Comma, Sp, Parenthesized(Seq(Qualified("n","choose"), Sp, V("i"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Cdot, Sp, V("k"), Sp, Parenthesized(Seq(V("i"), Sp, Plus, Sp, D(1))), Sp, GammaLower, Sp, Cdot, Sp, V("m"), Sp, Parenthesized(Seq(V("n"), Sp, Minus, Sp, V("i"))), Sp, GammaLower)), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, V("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))), Sp, Comma, Sp, V("c"), Sp, Parenthesized(Seq(V("n"), Sp, Plus, Sp, D(1))), Sp, Eq, Sp, V("a"), Sp, Parenthesized(Seq(V("n"), Sp, Plus, Sp, D(1))), Sp, Minus, Sp, Sum, Sp, V("i"), Sp, InMacro, Sp, V("range"), Sp, V("n"), Sp, Comma, Sp, Parenthesized(Seq(Qualified("n","choose"), Sp, V("i"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Cdot, Sp, V("c"), Sp, Parenthesized(Seq(V("i"), Sp, Plus, Sp, D(1))), Sp, Cdot, Sp, V("a"), Sp, Parenthesized(Seq(V("n"), Sp, Minus, Sp, V("i"))))), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, V("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))), Sp, Comma, Sp, V("d"), Sp, Parenthesized(Seq(V("n"), Sp, Plus, Sp, D(1))), Sp, Eq, Sp, V("b"), Sp, Parenthesized(Seq(V("n"), Sp, Plus, Sp, D(1))), Sp, Minus, Sp, Sum, Sp, V("i"), Sp, InMacro, Sp, V("range"), Sp, V("n"), Sp, Comma, Sp, Parenthesized(Seq(Qualified("n","choose"), Sp, V("i"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Cdot, Sp, Parenthesized(Seq(V("c"), Sp, Parenthesized(Seq(V("i"), Sp, Plus, Sp, D(1))), Sp, Cdot, Sp, V("b"), Sp, Parenthesized(Seq(V("n"), Sp, Minus, Sp, V("i"))), Sp, Plus, Sp, V("d"), Sp, Parenthesized(Seq(V("i"), Sp, Plus, Sp, D(1))), Sp, Cdot, Sp, V("a"), Sp, Parenthesized(Seq(V("n"), Sp, Minus, Sp, V("i"))))))), Sp, To, Sp, Forall, Sp, V("r"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))), Sp, Comma, Sp, D(1), Sp, Le, Sp, V("r"), Sp, To, Sp, V("FirstOrder"), Sp, Parenthesized(Seq(V("k"), Sp, V("r"))), Sp, Parenthesized(Seq(V("c"), Sp, V("r"))), Sp, Parenthesized(Seq(V("d"), Sp, V("r"))));

    private static Formula F26() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("Q"), Sp, Colon, Sp, V("MvPolynomial"), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("r"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Parenthesized(Seq(D(1), Sp, Le, Sp, V("M"))), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, V("x"), Sp, Comma, Sp, D(0), Sp, Le, Sp, V("eval"), Sp, V("x"), Sp, V("Q"))), Sp, To, Sp, V("iteratedDeriv"), Sp, V("r"), Sp, Parenthesized(Seq(V("mgf"), Sp, Parenthesized(Parenthesized(Seq(V("fun"), Sp, V("x"), Sp, Colon, Sp, V("Fin"), Sp, V("M"), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))), Sp, Mapsto, Sp, Qualified("Finset","expect"), Sp, Qualified("Finset","univ"), Sp, V("x")))), Sp, Parenthesized(Seq(V("laguerreWeightedMeasure"), Sp, V("M"), Sp, V("Q"))))), Sp, D(0), Sp, Eq, Sp, Parenthesized(Seq(Int, Sp, V("x"), Sp, Comma, Sp, V("laguerreWeight"), Sp, V("M"), Sp, V("M"), Sp, V("x"), Sp, Cdot, Sp, V("eval"), Sp, V("x"), Sp, V("Q"), Sp, Cdot, Sp, Sp, new Formula.Power(Parenthesized(Seq(Qualified("Finset","expect"), Sp, Qualified("Finset","univ"), Sp, V("x"))), V("r")))), Sp, Slash, Sp, V("partition"), Sp, V("M"), Sp, V("M"));

    private static Formula F27() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("a"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Parenthesized(Seq(D(0), Sp, Lt, Sp, V("a"))), Sp, To, Sp, V("laguerreMoment"), Sp, V("M"), Sp, D(1), Sp, V("a"), Sp, Eq, Sp, Sp, new Formula.Power(Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), D(2)), Sp, Slash, Sp, V("a"));

    private static Formula F28() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Parenthesized(Seq(D(1), Sp, Le, Sp, V("M"))), Sp, To, Sp, V("laguerreH"), Sp, V("M"), Sp, Seq(Eq, Sup(V("f"))), Sp, Seq(OpenBracket, Seq(V("nhds"), Sp, D(0)), CloseBracket), Sp, Parenthesized(Seq(V("fun"), Sp, V("t"), Sp, Mapsto, Sp, Qualified("Real","exp"), Sp, Parenthesized(Seq(V("gammaCGF"), Sp, Parenthesized(new Formula.Power(Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), D(2))), Sp, V("t"))))));

    private static Formula F29() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("r"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Parenthesized(Seq(D(1), Sp, Le, Sp, V("M"))), Sp, To, Sp, Parenthesized(Seq(Int, Sp, V("x"), Sp, Comma, Sp, V("laguerreWeight"), Sp, V("M"), Sp, V("M"), Sp, V("x"), Sp, Cdot, Sp, Sp, new Formula.Power(Parenthesized(Seq(Qualified("Finset","expect"), Sp, Qualified("Finset","univ"), Sp, V("x"))), V("r")))), Sp, Slash, Sp, V("partition"), Sp, V("M"), Sp, V("M"), Sp, Eq, Sp, V("expJet"), Sp, Parenthesized(Seq(V("gammaCGF"), Sp, Parenthesized(new Formula.Power(Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), D(2))))), Sp, V("r"));

    private static Formula F30() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Parenthesized(Seq(D(1), Sp, Le, Sp, V("M"))), Sp, To, Sp, V("laguerreHw"), Sp, V("M"), Sp, Seq(Eq, Sup(V("f"))), Sp, Seq(OpenBracket, Seq(V("nhds"), Sp, D(0)), CloseBracket), Sp, Parenthesized(Seq(V("fun"), Sp, V("t"), Sp, Mapsto, Sp, D(2), Sp, Cdot, Sp, Qualified("Real","exp"), Sp, Parenthesized(Seq(V("gammaCGF"), Sp, Parenthesized(new Formula.Power(Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), D(2))), Sp, V("t"))), Sp, Cdot, Sp, Sp, new Formula.Power(Parenthesized(Seq(V("inverseSlope"), Sp, Parenthesized(new Formula.Power(Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), D(2))), Sp, V("t"))), D(2)))));

    private static Formula Published0() =>
        Seq(Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("N"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(SigmaLower, Sp, Colon, Sp, Parenthesized(Seq(V("Type"), Star))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Parenthesized(Seq(OpenBracket, Seq(V("DecidableEq"), Sp, SigmaLower), CloseBracket)), Sp, To, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(V("D"), Sp, Colon, Sp, Parenthesized(Seq(V("Derivation"), Sp, Seq(Mathbb, Grp(V("R"))), Sp, Parenthesized(Seq(V("MvPolynomial"), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Parenthesized(Seq(V("MvPolynomial"), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, Seq(Mathbb, Grp(V("R")))))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(V("s"), Sp, Colon, Sp, Parenthesized(Seq(V("Finset"), Sp, SigmaLower))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(V("f"), Sp, Colon, Sp, Parenthesized(Seq(Parenthesized(SigmaLower), Sp, To, Sp, Parenthesized(Seq(V("MvPolynomial"), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, Seq(Mathbb, Grp(V("R")))))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(V("g"), Sp, Colon, Sp, Parenthesized(Seq(Parenthesized(SigmaLower), Sp, To, Sp, Parenthesized(Seq(V("MvPolynomial"), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, Seq(Mathbb, Grp(V("R")))))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, V("i"), Sp, InMacro, Sp, V("s")), Sp, Comma, Sp, Parenthesized(Seq(V("D"), Sp, Parenthesized(Seq(V("f"), Sp, V("i"))), Sp, Eq, Sp, V("g"), Sp, V("i"), Sp, Cdot, Sp, V("f"), Sp, V("i")))))), Sp, To, Sp, Parenthesized(Parenthesized(Seq(V("D"), Sp, Parenthesized(Seq(Prod, Sp, V("i"), Sp, InMacro, Sp, V("s"), Sp, Comma, Sp, V("f"), Sp, V("i"))), Sp, Eq, Sp, Parenthesized(Seq(Sum, Sp, V("i"), Sp, InMacro, Sp, V("s"), Sp, Comma, Sp, V("g"), Sp, V("i"))), Sp, Cdot, Sp, Prod, Sp, V("i"), Sp, InMacro, Sp, V("s"), Sp, Comma, Sp, V("f"), Sp, V("i"))))))))))))))))))))))))));

    private static Formula Published2() =>
        Seq(Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("N"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Parenthesized(Seq(V("volume"), Sp, Colon, Sp, Parenthesized(Seq(V("Measure"), Sp, Parenthesized(Seq(Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, To, Sp, Parenthesized(Seq(Mathbb, Grp(V("R")))))))))), Sp, Dot, Sp, V("restrict"), Sp, Parenthesized(Parenthesized(Seq(Qualified("Set","Ici"), Sp, Parenthesized(Seq(D(0), Sp, Colon, Sp, Parenthesized(Seq(Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, To, Sp, Parenthesized(Seq(Mathbb, Grp(V("R"))))))))))), Sp, Eq, Sp, V("orthantMeasure"), Sp, V("M")))));

    private static Formula Published3() =>
        Seq(Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("N"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(V("a"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("R"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Parenthesized(Parenthesized(Seq(D(0), Sp, Lt, Sp, V("a")))), Sp, To, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(V("P"), Sp, Colon, Sp, Parenthesized(Seq(V("MvPolynomial"), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, Seq(Mathbb, Grp(V("R")))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(V("Integrable"), Sp, Parenthesized(Seq(Seq(V("fun"), Sp, V("x")), Sp, Mapsto, Sp, Parenthesized(Seq(Qualified("Real","exp"), Sp, Parenthesized(Seq(Minus, Sp, V("a"), Sp, Cdot, Sp, Sum, Sp, V("i"), Sp, Comma, Sp, V("x"), Sp, V("i"))), Sp, Cdot, Sp, Qualified("MvPolynomial","eval"), Sp, V("x"), Sp, V("P"))))), Sp, Parenthesized(Seq(V("orthantMeasure"), Sp, V("M"))))))))))))))));

    private static Formula Published4() =>
        Seq(Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("N"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(V("a"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("R"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(V("P"), Sp, Colon, Sp, Parenthesized(Seq(V("MvPolynomial"), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, Seq(Mathbb, Grp(V("R")))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(V("polyIntegral"), Sp, V("a"), Sp, V("P"), Sp, Eq, Sp, Parenthesized(Seq(Int, Sp, V("x"), Sp, Comma, Sp, Qualified("Real","exp"), Sp, Parenthesized(Seq(Minus, Sp, V("a"), Sp, Cdot, Sp, Sum, Sp, V("i"), Sp, Comma, Sp, V("x"), Sp, V("i"))), Sp, Cdot, Sp, Qualified("MvPolynomial","eval"), Sp, V("x"), Sp, V("P"), Sp, Seq(Thin, V("d")), Sp, V("orthantMeasure"), Sp, V("M")))))))))))));

    private static Formula Published5() =>
        Seq(Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("N"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(V("a"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("R"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Parenthesized(Parenthesized(Seq(D(0), Sp, Lt, Sp, V("a")))), Sp, To, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(V("P"), Sp, Colon, Sp, Parenthesized(Seq(V("MvPolynomial"), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, Seq(Mathbb, Grp(V("R")))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(V("Q"), Sp, Colon, Sp, Parenthesized(Seq(V("MvPolynomial"), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, Seq(Mathbb, Grp(V("R")))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(V("polyIntegral"), Sp, V("a"), Sp, Parenthesized(Seq(V("P"), Sp, Plus, Sp, V("Q"))), Sp, Eq, Sp, V("polyIntegral"), Sp, V("a"), Sp, V("P"), Sp, Plus, Sp, V("polyIntegral"), Sp, V("a"), Sp, V("Q")))))))))))))))));

    private static Formula Published6() =>
        Seq(Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("N"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(V("a"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("R"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Parenthesized(Parenthesized(Seq(D(0), Sp, Lt, Sp, V("a")))), Sp, To, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(SigmaLower, Sp, Colon, Sp, Parenthesized(Seq(V("Type"), Star))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(V("s"), Sp, Colon, Sp, Parenthesized(Seq(V("Finset"), Sp, SigmaLower))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(V("P"), Sp, Colon, Sp, Parenthesized(Seq(Parenthesized(SigmaLower), Sp, To, Sp, Parenthesized(Seq(V("MvPolynomial"), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, Seq(Mathbb, Grp(V("R")))))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(V("polyIntegral"), Sp, V("a"), Sp, Parenthesized(Seq(Sum, Sp, V("i"), Sp, InMacro, Sp, V("s"), Sp, Comma, Sp, V("P"), Sp, V("i"))), Sp, Eq, Sp, Sum, Sp, V("i"), Sp, InMacro, Sp, V("s"), Sp, Comma, Sp, V("polyIntegral"), Sp, V("a"), Sp, Parenthesized(Seq(V("P"), Sp, V("i"))))))))))))))))))))));

    private static Formula Published7() =>
        Seq(Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("N"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(V("a"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("R"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Parenthesized(Parenthesized(Seq(D(0), Sp, Lt, Sp, V("a")))), Sp, To, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(V("i"), Sp, Colon, Sp, Parenthesized(Seq(V("Fin"), Sp, V("M")))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(V("P"), Sp, Colon, Sp, Parenthesized(Seq(V("MvPolynomial"), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, Seq(Mathbb, Grp(V("R")))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(V("a"), Sp, Cdot, Sp, V("polyIntegral"), Sp, V("a"), Sp, Parenthesized(Seq(new Formula.Power(Parenthesized(Parenthesized(Seq(V("X"), Sp, V("i")))), D(2)), Sp, Cdot, Sp, V("P"))), Sp, Eq, Sp, D(2), Sp, Cdot, Sp, V("polyIntegral"), Sp, V("a"), Sp, Parenthesized(Seq(V("X"), Sp, V("i"), Sp, Cdot, Sp, V("P"))), Sp, Plus, Sp, V("polyIntegral"), Sp, V("a"), Sp, Parenthesized(Seq(new Formula.Power(Parenthesized(Parenthesized(Seq(V("X"), Sp, V("i")))), D(2)), Sp, Cdot, Sp, Qualified("MvPolynomial","pderiv"), Sp, V("i"), Sp, V("P")))))))))))))))))));

    private static Formula Published8() =>
        Seq(Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("N"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(V("a"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("R"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Parenthesized(Parenthesized(Seq(D(0), Sp, Lt, Sp, V("a")))), Sp, To, Sp, Parenthesized(Parenthesized(Seq(V("laguerreMoment"), Sp, V("M"), Sp, D(2), Sp, V("a"), Sp, Eq, Sp, D(2), Sp, Cdot, Sp, new Formula.Power(Parenthesized(Parenthesized(Seq(V("M"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("R"))))))), D(3)), Sp, Slash, Sp, new Formula.Power(Parenthesized(V("a")), D(2))))))))))));
}

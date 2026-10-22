using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Transport.StrongAbsorption;

internal sealed class DensityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Density for the strong-absorption cumulant expansion.",
        H("Density"),
        Blocks(
            Paragraph(Text("Natural-number subtraction is truncated. Unmarked integrals use volume; real-number powers and division use the real field.")),
            Describe.Lean(DescribeId.Create("crossproduct"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Density.crossProduct"),
                H("crossProduct"), StatementSource.FromAuthor(Disp(F0())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed definition is used in the moment and density expansions."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("tailset"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Density.tailSet"),
                H("tailSet"), StatementSource.FromAuthor(Disp(F1())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed definition is used in the moment and density expansions."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("lineardensitypoly"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Density.linearDensityPoly"),
                H("linearDensityPoly"), StatementSource.FromAuthor(Disp(F2())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed definition is used in the moment and density expansions."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("measurableset-tailset"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Density.measurableSet_tailSet"),
                H("measurableSet_tailSet"), StatementSource.FromAuthor(Disp(F3())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("lineardensitypoly-eval"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Density.linearDensityPoly_eval"),
                H("linearDensityPoly_eval"), StatementSource.FromAuthor(Disp(F4())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("firstorder-affine"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Density.affine"),
                H("FirstOrder.affine"), StatementSource.FromAuthor(Disp(F5())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("baseweight"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Density.baseWeight"),
                H("baseWeight"), StatementSource.FromAuthor(Disp(F6())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed definition is used in the moment and density expansions."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("baseweight-mass"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Density.baseWeight_mass"),
                H("baseWeight_mass"), StatementSource.FromAuthor(Disp(F7())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("lineardensityintegral-zero"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Density.linearDensityIntegral_zero"),
                H("linearDensityIntegral_zero"), StatementSource.FromAuthor(Disp(F8())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("basepolynomial-integrable"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Density.basePolynomial_integrable"),
                H("basePolynomial_integrable"), StatementSource.FromAuthor(Disp(F9())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("weight-scaled-cutoff"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Density.weight_scaled_cutoff"),
                H("weight_scaled_cutoff"), StatementSource.FromAuthor(Disp(F10())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("crossintegrand-integrable"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Density.crossIntegrand_integrable"),
                H("crossIntegrand_integrable"), StatementSource.FromAuthor(Disp(F11())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("law-polynomial-firstorder"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Density.law_polynomial_firstOrder"),
                H("law_polynomial_firstOrder"), StatementSource.FromAuthor(Disp(F12())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("published-crossproduct-firstorder"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Density.crossProduct_firstOrder"),
                H("crossProduct_firstOrder"), StatementSource.FromAuthor(Disp(Published0())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed formula relates the polynomial integrals and the normalized finite-channel measure."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("published-jointsum"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Density.jointSum"),
                H("jointSum"), StatementSource.FromAuthor(Disp(Published1())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed formula relates the polynomial integrals and the normalized finite-channel measure."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("published-crossproduct-abs-bound"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Density.crossProduct_abs_bound"),
                H("crossProduct_abs_bound"), StatementSource.FromAuthor(Disp(Published2())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed formula relates the polynomial integrals and the normalized finite-channel measure."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("published-budgetpoly"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Density.budgetPoly"),
                H("budgetPoly"), StatementSource.FromAuthor(Disp(Published3())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed formula relates the polynomial integrals and the normalized finite-channel measure."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("published-budgetpoly-eval"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Density.budgetPoly_eval"),
                H("budgetPoly_eval"), StatementSource.FromAuthor(Disp(Published4())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed formula relates the polynomial integrals and the normalized finite-channel measure."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("published-baseweight-nonneg"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Density.baseWeight_nonneg"),
                H("baseWeight_nonneg"), StatementSource.FromAuthor(Disp(Published5())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed formula relates the polynomial integrals and the normalized finite-channel measure."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("published-budgetpoly-nonneg"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Density.budgetPoly_nonneg"),
                H("budgetPoly_nonneg"), StatementSource.FromAuthor(Disp(Published6())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed formula relates the polynomial integrals and the normalized finite-channel measure."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("published-crossintegral"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Density.crossIntegral"),
                H("crossIntegral"), StatementSource.FromAuthor(Disp(Published7())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed formula relates the polynomial integrals and the normalized finite-channel measure."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("published-cutoffintegral"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Density.cutoffIntegral"),
                H("cutoffIntegral"), StatementSource.FromAuthor(Disp(Published8())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed formula relates the polynomial integrals and the normalized finite-channel measure."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("published-baseweight-eq-zero-off-orthant"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Density.baseWeight_eq_zero_off_orthant"),
                H("baseWeight_eq_zero_off_orthant"), StatementSource.FromAuthor(Disp(Published9())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed formula relates the polynomial integrals and the normalized finite-channel measure."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("published-tail-family-exponential-bound"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Density.tail_family_exponential_bound"),
                H("tail_family_exponential_bound"), StatementSource.FromAuthor(Disp(Published10())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed formula relates the polynomial integrals and the normalized finite-channel measure."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("published-law-polynomial-ratio"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Density.law_polynomial_ratio"),
                H("law_polynomial_ratio"), StatementSource.FromAuthor(Disp(Published11())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed formula relates the polynomial integrals and the normalized finite-channel measure."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("published-cutoffintegral-eq-sub"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Density.cutoffIntegral_eq_sub"),
                H("cutoffIntegral_eq_sub"), StatementSource.FromAuthor(Disp(Published12())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed formula relates the polynomial integrals and the normalized finite-channel measure."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("published-cutoffintegral-firstorder"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Density.cutoffIntegral_firstOrder"),
                H("cutoffIntegral_firstOrder"), StatementSource.FromAuthor(Disp(Published13())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed formula relates the polynomial integrals and the normalized finite-channel measure."))), DescribeRole.Theorem)
        )));

    private static Formula CastM() => Parenthesized(Seq(V("M"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("R"))))));
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

    private static Formula F0() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(Varepsilon, Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("x"), Sp, Colon, Sp, V("Fin"), Sp, V("M"), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("y"), Sp, Colon, Sp, V("Fin"), Sp, V("M"), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, V("crossProduct"), Sp, V("M"), Sp, Varepsilon, Sp, V("x"), Sp, V("y"), Sp, Eq, Sp, Parenthesized(Seq(Prod, Sp, V("i"), Sp, Comma, Sp, Prod, Sp, V("j"), Sp, Comma, Sp, Parenthesized(Seq(D(1), Sp, Plus, Sp, Varepsilon, Sp, Cdot, Sp, Parenthesized(Seq(V("x"), Sp, V("i"), Sp, Minus, Sp, V("y"), Sp, V("j"))))))));

    private static Formula F1() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(GammaLower, Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, V("tailSet"), Sp, V("M"), Sp, GammaLower, Sp, Eq, Sp, Parenthesized(Seq(OpenBrace, Seq(V("p"), Sp, Bar, Sp, Exists, Sp, V("j"), Sp, Comma, Sp, GammaLower, Sp, Lt, Sp, V("p"), Sp, Dot, Sp, D(2), Sp, V("j")), CloseBrace)));

    private static Formula F2() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, V("linearDensityPoly"), Sp, V("M"), Sp, Eq, Sp, Parenthesized(Seq(V("C"), Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Cdot, Sp, Parenthesized(Seq(Parenthesized(Seq(Sum, Sp, V("i"), Sp, Colon, Sp, V("Fin"), Sp, V("M"), Sp, Comma, Sp, V("X"), Sp, Parenthesized(Seq(Qualified("Sum","inl"), Sp, V("i"))))), Sp, Minus, Sp, Parenthesized(Seq(Sum, Sp, V("j"), Sp, Colon, Sp, V("Fin"), Sp, V("M"), Sp, Comma, Sp, V("X"), Sp, Parenthesized(Seq(Qualified("Sum","inr"), Sp, V("j"))))))))));

    private static Formula F3() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(GammaLower, Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, V("MeasurableSet"), Sp, Parenthesized(Seq(V("tailSet"), Sp, V("M"), Sp, GammaLower)));

    private static Formula F4() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("p"), Sp, Colon, Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Times, Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))))), Sp, Comma, Sp, V("eval"), Sp, Parenthesized(Seq(Qualified("Sum","elim"), Sp, V("p"), Sp, Dot, Sp, D(1), Sp, V("p"), Sp, Dot, Sp, D(2))), Sp, Parenthesized(Seq(V("linearDensityPoly"), Sp, V("M"))), Sp, Eq, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Cdot, Sp, Parenthesized(Seq(Parenthesized(Seq(Sum, Sp, V("i"), Sp, Comma, Sp, V("p"), Sp, Dot, Sp, D(1), Sp, V("i"))), Sp, Minus, Sp, Parenthesized(Seq(Sum, Sp, V("j"), Sp, Comma, Sp, V("p"), Sp, Dot, Sp, D(2), Sp, V("j"))))));

    private static Formula F5() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("a"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("b"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, V("FirstOrder"), Sp, Parenthesized(Seq(V("fun"), Sp, GammaLower, Sp, Mapsto, Sp, V("a"), Sp, Plus, Sp, V("b"), Sp, Cdot, Sp, new Formula.Power(GammaLower, Seq(Minus, D(1))))), Sp, V("a"), Sp, V("b"));

    private static Formula F6() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("a"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("p"), Sp, Colon, Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Times, Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))))), Sp, Comma, Sp, V("baseWeight"), Sp, V("M"), Sp, V("a"), Sp, V("p"), Sp, Eq, Sp, Parenthesized(Seq(V("laguerreWeight"), Sp, V("M"), Sp, V("a"), Sp, V("p"), Sp, Dot, Sp, D(1), Sp, Cdot, Sp, V("laguerreWeight"), Sp, V("M"), Sp, V("a"), Sp, V("p"), Sp, Dot, Sp, D(2))));

    private static Formula F7() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("a"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Parenthesized(Seq(Int, Sp, V("p"), Sp, Comma, Sp, V("baseWeight"), Sp, V("M"), Sp, V("a"), Sp, V("p"))), Sp, Eq, Sp, Sp, new Formula.Power(Parenthesized(Seq(V("partition"), Sp, V("M"), Sp, V("a"))), D(2)));

    private static Formula F8() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("a"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Parenthesized(Seq(Int, Sp, V("p"), Sp, Comma, Sp, V("baseWeight"), Sp, V("M"), Sp, V("a"), Sp, V("p"), Sp, Cdot, Sp, V("eval"), Sp, Parenthesized(Seq(Qualified("Sum","elim"), Sp, V("p"), Sp, Dot, Sp, D(1), Sp, V("p"), Sp, Dot, Sp, D(2))), Sp, Parenthesized(Seq(V("linearDensityPoly"), Sp, V("M"))))), Sp, Eq, Sp, D(0));

    private static Formula F9() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("a"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("P"), Sp, Colon, Sp, V("MvPolynomial"), Sp, Parenthesized(Seq(V("Sum"), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))))), Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Parenthesized(Seq(D(0), Sp, Lt, Sp, V("a"))), Sp, To, Sp, V("Integrable"), Sp, Parenthesized(Seq(V("fun"), Sp, V("p"), Sp, Mapsto, Sp, V("baseWeight"), Sp, V("M"), Sp, V("a"), Sp, V("p"), Sp, Cdot, Sp, V("eval"), Sp, Parenthesized(Seq(Qualified("Sum","elim"), Sp, V("p"), Sp, Dot, Sp, D(1), Sp, V("p"), Sp, Dot, Sp, D(2))), Sp, V("P"))));

    private static Formula F10() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(GammaLower, Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("p"), Sp, Colon, Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Times, Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))))), Sp, Comma, Sp, Parenthesized(Seq(D(0), Sp, Lt, Sp, GammaLower)), Sp, To, Sp, V("weight"), Sp, V("M"), Sp, GammaLower, Sp, V("p"), Sp, Eq, Sp, Sp, new Formula.Power(GammaLower, new Formula.Power(V("M"), D(2))), Sp, Cdot, Sp, Parenthesized(Seq(V("tailSet"), Sp, V("M"), Sp, GammaLower)), Sp, Sup(V("c")), Sp, Dot, Sp, V("indicator"), Sp, Parenthesized(Seq(V("fun"), Sp, V("p"), Sp, Mapsto, Sp, V("baseWeight"), Sp, V("M"), Sp, V("M"), Sp, V("p"), Sp, Cdot, Sp, V("crossProduct"), Sp, V("M"), Sp, new Formula.Power(GammaLower, Seq(Minus, D(1))), Sp, V("p"), Sp, Dot, Sp, D(1), Sp, V("p"), Sp, Dot, Sp, D(2))), Sp, V("p"));

    private static Formula F11() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("a"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(Varepsilon, Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("P"), Sp, Colon, Sp, V("MvPolynomial"), Sp, Parenthesized(Seq(V("Sum"), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))))), Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Parenthesized(Seq(D(0), Sp, Lt, Sp, V("a"))), Sp, To, Sp, V("Integrable"), Sp, Parenthesized(Seq(V("fun"), Sp, V("p"), Sp, Mapsto, Sp, V("baseWeight"), Sp, V("M"), Sp, V("a"), Sp, V("p"), Sp, Cdot, Sp, V("eval"), Sp, Parenthesized(Seq(Qualified("Sum","elim"), Sp, V("p"), Sp, Dot, Sp, D(1), Sp, V("p"), Sp, Dot, Sp, D(2))), Sp, V("P"), Sp, Cdot, Sp, V("crossProduct"), Sp, V("M"), Sp, Varepsilon, Sp, V("p"), Sp, Dot, Sp, D(1), Sp, V("p"), Sp, Dot, Sp, D(2))));

    private static Formula F12() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("P"), Sp, Colon, Sp, V("MvPolynomial"), Sp, Parenthesized(Seq(V("Sum"), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))))), Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Parenthesized(Seq(D(1), Sp, Le, Sp, V("M"))), Sp, To, Sp, V("FirstOrder"), Sp, Parenthesized(Seq(V("fun"), Sp, GammaLower, Sp, Mapsto, Sp, Int, Sp, V("p"), Sp, Comma, Sp, V("eval"), Sp, Parenthesized(Seq(Qualified("Sum","elim"), Sp, V("p"), Sp, Dot, Sp, D(1), Sp, V("p"), Sp, Dot, Sp, D(2))), Sp, V("P"), Sp, V("d"), Sp, V("law"), Sp, V("M"), Sp, GammaLower)), Sp, Parenthesized(Seq(Parenthesized(Seq(Int, Sp, V("p"), Sp, Comma, Sp, V("baseWeight"), Sp, V("M"), Sp, V("M"), Sp, V("p"), Sp, Cdot, Sp, V("eval"), Sp, Parenthesized(Seq(Qualified("Sum","elim"), Sp, V("p"), Sp, Dot, Sp, D(1), Sp, V("p"), Sp, Dot, Sp, D(2))), Sp, V("P"))), Sp, Slash, Sp, Sp, new Formula.Power(Parenthesized(Seq(V("partition"), Sp, V("M"), Sp, V("M"))), D(2)))), Sp, Parenthesized(Seq(Parenthesized(Seq(Int, Sp, V("p"), Sp, Comma, Sp, V("baseWeight"), Sp, V("M"), Sp, V("M"), Sp, V("p"), Sp, Cdot, Sp, V("eval"), Sp, Parenthesized(Seq(Qualified("Sum","elim"), Sp, V("p"), Sp, Dot, Sp, D(1), Sp, V("p"), Sp, Dot, Sp, D(2))), Sp, Parenthesized(Seq(V("P"), Sp, Cdot, Sp, V("linearDensityPoly"), Sp, V("M"))))), Sp, Slash, Sp, Sp, new Formula.Power(Parenthesized(Seq(V("partition"), Sp, V("M"), Sp, V("M"))), D(2)))));

    private static Formula Published0() =>
        Seq(Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("N"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(V("x"), Sp, Colon, Sp, Parenthesized(Seq(Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, To, Sp, Parenthesized(Seq(Mathbb, Grp(V("R"))))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(V("y"), Sp, Colon, Sp, Parenthesized(Seq(Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, To, Sp, Parenthesized(Seq(Mathbb, Grp(V("R"))))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Parenthesized(Seq(Sum, Sp, V("p"), Sp, Colon, Sp, V("Fin"), Sp, V("M"), Sp, Times, Sp, V("Fin"), Sp, V("M"), Sp, Comma, Sp, Parenthesized(Seq(V("x"), Sp, V("p"), Sp, Dot, Sp, D(1), Sp, Minus, Sp, V("y"), Sp, V("p"), Sp, Dot, Sp, D(2))))), Sp, Eq, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("R")))))), Sp, Cdot, Sp, Parenthesized(Seq(Parenthesized(Seq(Sum, Sp, V("i"), Sp, Comma, Sp, V("x"), Sp, V("i"))), Sp, Minus, Sp, Parenthesized(Seq(Sum, Sp, V("j"), Sp, Comma, Sp, V("y"), Sp, V("j")))))))))))))));

    private static Formula Published1() =>
        Seq(Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("N"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(V("p"), Sp, Colon, Sp, Parenthesized(Seq(Parenthesized(Seq(Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, To, Sp, Parenthesized(Seq(Mathbb, Grp(V("R")))))), Sp, Times, Sp, Parenthesized(Seq(Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, To, Sp, Parenthesized(Seq(Mathbb, Grp(V("R"))))))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(V("jointSum"), Sp, V("M"), Sp, V("p"), Sp, Eq, Sp, Parenthesized(Seq(Parenthesized(Seq(Sum, Sp, V("i"), Sp, Comma, Sp, V("p"), Sp, Dot, Sp, D(1), Sp, V("i"))), Sp, Plus, Sp, Parenthesized(Seq(Sum, Sp, V("j"), Sp, Comma, Sp, V("p"), Sp, Dot, Sp, D(2), Sp, V("j"))))))))))));

    private static Formula Published2() =>
        Seq(Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("N"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(Varepsilon, Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("R"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Parenthesized(Parenthesized(Seq(D(0), Sp, Le, Sp, Varepsilon))), Sp, To, Sp, Parenthesized(Parenthesized(Seq(Parenthesized(Parenthesized(Seq(Varepsilon, Sp, Le, Sp, D(1)))), Sp, To, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(V("x"), Sp, Colon, Sp, Parenthesized(Seq(Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, To, Sp, Parenthesized(Seq(Mathbb, Grp(V("R"))))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(V("y"), Sp, Colon, Sp, Parenthesized(Seq(Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, To, Sp, Parenthesized(Seq(Mathbb, Grp(V("R"))))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, V("i")), Sp, Comma, Sp, Parenthesized(Seq(D(0), Sp, Le, Sp, V("x"), Sp, V("i")))))), Sp, To, Sp, Parenthesized(Parenthesized(Seq(Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, V("j")), Sp, Comma, Sp, Parenthesized(Seq(D(0), Sp, Le, Sp, V("y"), Sp, V("j")))))), Sp, To, Sp, Parenthesized(Parenthesized(Seq(Bar, Sp, V("crossProduct"), Sp, V("M"), Sp, Varepsilon, Sp, V("x"), Sp, V("y"), Sp, Bar, Sp, Le, Sp, new Formula.Power(Parenthesized(Parenthesized(Seq(D(1), Sp, Plus, Sp, Parenthesized(Seq(Sum, Sp, V("i"), Sp, Comma, Sp, V("x"), Sp, V("i"))), Sp, Plus, Sp, Parenthesized(Seq(Sum, Sp, V("j"), Sp, Comma, Sp, V("y"), Sp, V("j")))))), new Formula.Power(Parenthesized(V("M")), D(2))))))))))))))))))))))))))));

    private static Formula Published3() =>
        Seq(Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("N"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(V("budgetPoly"), Sp, V("M"), Sp, Eq, Sp, Parenthesized(new Formula.Power(Parenthesized(Parenthesized(Seq(D(1), Sp, Plus, Sp, Parenthesized(Seq(Qualified("MvPolynomial","psum"), Sp, Parenthesized(Seq(V("Sum"), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))))), Sp, Seq(Mathbb, Grp(V("R"))), Sp, D(1)))))), new Formula.Power(Parenthesized(V("M")), D(2))))))));

    private static Formula Published4() =>
        Seq(Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("N"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(V("p"), Sp, Colon, Sp, Parenthesized(Seq(Parenthesized(Seq(Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, To, Sp, Parenthesized(Seq(Mathbb, Grp(V("R")))))), Sp, Times, Sp, Parenthesized(Seq(Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, To, Sp, Parenthesized(Seq(Mathbb, Grp(V("R"))))))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(V("eval"), Sp, Parenthesized(Seq(Qualified("Sum","elim"), Sp, V("p"), Sp, Dot, Sp, D(1), Sp, V("p"), Sp, Dot, Sp, D(2))), Sp, Parenthesized(Seq(V("budgetPoly"), Sp, V("M"))), Sp, Eq, Sp, new Formula.Power(Parenthesized(Parenthesized(Seq(D(1), Sp, Plus, Sp, V("jointSum"), Sp, V("M"), Sp, V("p")))), new Formula.Power(Parenthesized(V("M")), D(2))))))))));

    private static Formula Published5() =>
        Seq(Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("N"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(V("a"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("R"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(V("p"), Sp, Colon, Sp, Parenthesized(Seq(Parenthesized(Seq(Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, To, Sp, Parenthesized(Seq(Mathbb, Grp(V("R")))))), Sp, Times, Sp, Parenthesized(Seq(Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, To, Sp, Parenthesized(Seq(Mathbb, Grp(V("R"))))))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(D(0), Sp, Le, Sp, V("baseWeight"), Sp, V("M"), Sp, V("a"), Sp, V("p")))))))))));

    private static Formula Published6() =>
        Seq(Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("N"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(V("p"), Sp, Colon, Sp, Parenthesized(Seq(Parenthesized(Seq(Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, To, Sp, Parenthesized(Seq(Mathbb, Grp(V("R")))))), Sp, Times, Sp, Parenthesized(Seq(Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, To, Sp, Parenthesized(Seq(Mathbb, Grp(V("R"))))))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Parenthesized(Parenthesized(Seq(V("p"), Sp, InMacro, Sp, Parenthesized(Seq(Qualified("Set","Ici"), Sp, Parenthesized(Seq(D(0), Sp, Colon, Sp, Parenthesized(Seq(Parenthesized(Seq(Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, To, Sp, Parenthesized(Seq(Mathbb, Grp(V("R")))))), Sp, Times, Sp, Parenthesized(Seq(Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, To, Sp, Parenthesized(Seq(Mathbb, Grp(V("R"))))))))))))))), Sp, To, Sp, Parenthesized(Parenthesized(Seq(D(0), Sp, Le, Sp, V("eval"), Sp, Parenthesized(Seq(Qualified("Sum","elim"), Sp, V("p"), Sp, Dot, Sp, D(1), Sp, V("p"), Sp, Dot, Sp, D(2))), Sp, Parenthesized(Seq(V("budgetPoly"), Sp, V("M")))))))))))));

    private static Formula Published7() =>
        Seq(Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("N"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(V("a"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("R"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(Varepsilon, Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("R"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(V("P"), Sp, Colon, Sp, Parenthesized(Seq(V("MvPolynomial"), Sp, Parenthesized(Seq(V("Sum"), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))))), Sp, Seq(Mathbb, Grp(V("R")))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(V("crossIntegral"), Sp, V("M"), Sp, V("a"), Sp, Varepsilon, Sp, V("P"), Sp, Eq, Sp, Parenthesized(Seq(Int, Sp, V("p"), Sp, Comma, Sp, V("baseWeight"), Sp, V("M"), Sp, V("a"), Sp, V("p"), Sp, Cdot, Sp, V("eval"), Sp, Parenthesized(Seq(Qualified("Sum","elim"), Sp, V("p"), Sp, Dot, Sp, D(1), Sp, V("p"), Sp, Dot, Sp, D(2))), Sp, V("P"), Sp, Cdot, Sp, V("crossProduct"), Sp, V("M"), Sp, Varepsilon, Sp, V("p"), Sp, Dot, Sp, D(1), Sp, V("p"), Sp, Dot, Sp, D(2))))))))))))))));

    private static Formula Published8() =>
        Seq(Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("N"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(V("a"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("R"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(GammaLower, Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("R"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(V("P"), Sp, Colon, Sp, Parenthesized(Seq(V("MvPolynomial"), Sp, Parenthesized(Seq(V("Sum"), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))))), Sp, Seq(Mathbb, Grp(V("R")))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(V("cutoffIntegral"), Sp, V("M"), Sp, V("a"), Sp, GammaLower, Sp, V("P"), Sp, Eq, Sp, Parenthesized(Seq(Int, Sp, V("p"), Sp, Comma, Sp, new Formula.Power(Parenthesized(Parenthesized(Seq(V("tailSet"), Sp, V("M"), Sp, GammaLower))), V("c")), Sp, Dot, Sp, V("indicator"), Sp, Parenthesized(Seq(Seq(V("fun"), Sp, V("p")), Sp, Mapsto, Sp, Parenthesized(Seq(V("baseWeight"), Sp, V("M"), Sp, V("a"), Sp, V("p"), Sp, Cdot, Sp, V("eval"), Sp, Parenthesized(Seq(Qualified("Sum","elim"), Sp, V("p"), Sp, Dot, Sp, D(1), Sp, V("p"), Sp, Dot, Sp, D(2))), Sp, V("P"), Sp, Cdot, Sp, V("crossProduct"), Sp, V("M"), Sp, new Formula.Power(Parenthesized(GammaLower), Seq(Minus, D(1))), Sp, V("p"), Sp, Dot, Sp, D(1), Sp, V("p"), Sp, Dot, Sp, D(2))))), Sp, V("p"))))))))))))))));

    private static Formula Published9() =>
        Seq(Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("N"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(V("a"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("R"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(V("p"), Sp, Colon, Sp, Parenthesized(Seq(Parenthesized(Seq(Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, To, Sp, Parenthesized(Seq(Mathbb, Grp(V("R")))))), Sp, Times, Sp, Parenthesized(Seq(Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, To, Sp, Parenthesized(Seq(Mathbb, Grp(V("R"))))))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Parenthesized(Parenthesized(Seq(V("p"), Sp, Seq(Neg, Sp, InMacro), Sp, Parenthesized(Seq(Qualified("Set","Ici"), Sp, Parenthesized(Seq(D(0), Sp, Colon, Sp, Parenthesized(Seq(Parenthesized(Seq(Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, To, Sp, Parenthesized(Seq(Mathbb, Grp(V("R")))))), Sp, Times, Sp, Parenthesized(Seq(Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, To, Sp, Parenthesized(Seq(Mathbb, Grp(V("R"))))))))))))))), Sp, To, Sp, Parenthesized(Parenthesized(Seq(V("baseWeight"), Sp, V("M"), Sp, V("a"), Sp, V("p"), Sp, Eq, Sp, D(0))))))))))))));

    private static Formula Published10() =>
        Seq(Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("N"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(V("a"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("R"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Parenthesized(Parenthesized(Seq(D(0), Sp, Lt, Sp, V("a")))), Sp, To, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(GammaLower, Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("R"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(V("P"), Sp, Colon, Sp, Parenthesized(Seq(V("MvPolynomial"), Sp, Parenthesized(Seq(V("Sum"), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))))), Sp, Seq(Mathbb, Grp(V("R")))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(V("f"), Sp, Colon, Sp, Parenthesized(Seq(Parenthesized(Seq(Parenthesized(Seq(Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, To, Sp, Parenthesized(Seq(Mathbb, Grp(V("R")))))), Sp, Times, Sp, Parenthesized(Seq(Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, To, Sp, Parenthesized(Seq(Mathbb, Grp(V("R")))))))), Sp, To, Sp, Parenthesized(Seq(Mathbb, Grp(V("R"))))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, V("p")), Sp, Comma, Sp, Parenthesized(Seq(Bar, Sp, V("f"), Sp, V("p"), Sp, Bar, Sp, Le, Sp, V("baseWeight"), Sp, V("M"), Sp, V("a"), Sp, V("p"), Sp, Cdot, Sp, Bar, Sp, V("eval"), Sp, Parenthesized(Seq(Qualified("Sum","elim"), Sp, V("p"), Sp, Dot, Sp, D(1), Sp, V("p"), Sp, Dot, Sp, D(2))), Sp, V("P"), Sp, Bar))))), Sp, To, Sp, Parenthesized(Parenthesized(Seq(Bar, Sp, Int, Sp, V("p"), Sp, V("in"), Sp, V("tailSet"), Sp, V("M"), Sp, GammaLower, Sp, Comma, Sp, V("f"), Sp, V("p"), Sp, Bar, Sp, Le, Sp, Qualified("Real","exp"), Sp, Parenthesized(Seq(Minus, Sp, Parenthesized(Seq(V("a"), Sp, Cdot, Sp, GammaLower)), Sp, Slash, Sp, D(2))), Sp, Cdot, Sp, Int, Sp, V("p"), Sp, Comma, Sp, V("baseWeight"), Sp, V("M"), Sp, Parenthesized(Seq(V("a"), Sp, Slash, Sp, D(2))), Sp, V("p"), Sp, Cdot, Sp, Bar, Sp, V("eval"), Sp, Parenthesized(Seq(Qualified("Sum","elim"), Sp, V("p"), Sp, Dot, Sp, D(1), Sp, V("p"), Sp, Dot, Sp, D(2))), Sp, V("P"), Sp, Bar))))))))))))))))))))));

    private static Formula Published11() =>
        Seq(Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("N"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Parenthesized(Parenthesized(Seq(D(1), Sp, Le, Sp, V("M")))), Sp, To, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(GammaLower, Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("R"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Parenthesized(Parenthesized(Seq(D(0), Sp, Lt, Sp, GammaLower))), Sp, To, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(V("P"), Sp, Colon, Sp, Parenthesized(Seq(V("MvPolynomial"), Sp, Parenthesized(Seq(V("Sum"), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))))), Sp, Seq(Mathbb, Grp(V("R")))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Parenthesized(Seq(Int, Sp, V("p"), Sp, Comma, Sp, V("eval"), Sp, Parenthesized(Seq(Qualified("Sum","elim"), Sp, V("p"), Sp, Dot, Sp, D(1), Sp, V("p"), Sp, Dot, Sp, D(2))), Sp, V("P"), Sp, Seq(Thin, V("d")), Sp, V("law"), Sp, V("M"), Sp, GammaLower)), Sp, Eq, Sp, V("cutoffIntegral"), Sp, V("M"), Sp, CastM(), Sp, GammaLower, Sp, V("P"), Sp, Slash, Sp, V("cutoffIntegral"), Sp, V("M"), Sp, CastM(), Sp, GammaLower, Sp, D(1)))))))))))))))));

    private static Formula Published12() =>
        Seq(Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("N"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(V("a"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("R"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Parenthesized(Parenthesized(Seq(D(0), Sp, Lt, Sp, V("a")))), Sp, To, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(GammaLower, Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("R"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(V("P"), Sp, Colon, Sp, Parenthesized(Seq(V("MvPolynomial"), Sp, Parenthesized(Seq(V("Sum"), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))))), Sp, Seq(Mathbb, Grp(V("R")))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(V("cutoffIntegral"), Sp, V("M"), Sp, V("a"), Sp, GammaLower, Sp, V("P"), Sp, Eq, Sp, V("crossIntegral"), Sp, V("M"), Sp, V("a"), Sp, new Formula.Power(Parenthesized(GammaLower), Seq(Minus, D(1))), Sp, V("P"), Sp, Minus, Sp, Int, Sp, V("p"), Sp, V("in"), Sp, V("tailSet"), Sp, V("M"), Sp, GammaLower, Sp, Comma, Sp, V("baseWeight"), Sp, V("M"), Sp, V("a"), Sp, V("p"), Sp, Cdot, Sp, V("eval"), Sp, Parenthesized(Seq(Qualified("Sum","elim"), Sp, V("p"), Sp, Dot, Sp, D(1), Sp, V("p"), Sp, Dot, Sp, D(2))), Sp, V("P"), Sp, Cdot, Sp, V("crossProduct"), Sp, V("M"), Sp, new Formula.Power(Parenthesized(GammaLower), Seq(Minus, D(1))), Sp, V("p"), Sp, Dot, Sp, D(1), Sp, V("p"), Sp, Dot, Sp, D(2)))))))))))))))));

    private static Formula Published13() =>
        Seq(Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("N"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(V("a"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("R"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Parenthesized(Parenthesized(Seq(D(0), Sp, Lt, Sp, V("a")))), Sp, To, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(V("P"), Sp, Colon, Sp, Parenthesized(Seq(V("MvPolynomial"), Sp, Parenthesized(Seq(V("Sum"), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))))), Sp, Seq(Mathbb, Grp(V("R")))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(V("FirstOrder"), Sp, Parenthesized(Seq(Seq(V("fun"), Sp, GammaLower), Sp, Mapsto, Sp, Parenthesized(Seq(V("cutoffIntegral"), Sp, V("M"), Sp, V("a"), Sp, GammaLower, Sp, V("P"))))), Sp, Parenthesized(Seq(Int, Sp, V("p"), Sp, Comma, Sp, V("baseWeight"), Sp, V("M"), Sp, V("a"), Sp, V("p"), Sp, Cdot, Sp, V("eval"), Sp, Parenthesized(Seq(Qualified("Sum","elim"), Sp, V("p"), Sp, Dot, Sp, D(1), Sp, V("p"), Sp, Dot, Sp, D(2))), Sp, V("P"))), Sp, Parenthesized(Seq(Int, Sp, V("p"), Sp, Comma, Sp, V("baseWeight"), Sp, V("M"), Sp, V("a"), Sp, V("p"), Sp, Cdot, Sp, V("eval"), Sp, Parenthesized(Seq(Qualified("Sum","elim"), Sp, V("p"), Sp, Dot, Sp, D(1), Sp, V("p"), Sp, Dot, Sp, D(2))), Sp, Parenthesized(Seq(V("P"), Sp, Cdot, Sp, V("linearDensityPoly"), Sp, V("M"))))))))))))))))));
}

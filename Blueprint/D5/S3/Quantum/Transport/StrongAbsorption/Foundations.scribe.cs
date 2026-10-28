using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Transport.StrongAbsorption;

internal sealed class FoundationsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Foundations for the strong-absorption cumulant expansion.",
        H("Foundations"),
        Blocks(
            Paragraph(Text("Natural-number subtraction is truncated. Unmarked integrals use volume; real-number powers and division use the real field.")),
            Describe.Lean(DescribeId.Create("exp-sum-prod"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Foundations.exp_sum_prod"),
                H("exp_sum_prod"), StatementSource.FromAuthor(Disp(ExpSumProd())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exponential of the sum of both coordinate families factors as the product of their exponentials."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("weight"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Foundations.weight"),
                H("weight"), StatementSource.FromAuthor(Disp(F0())),
                AssessedProvenance.FromLiterature(Note()),
                Blocks(Paragraph(Text("The unnormalized joint weight of inverse delay rates and auxiliary eigenvalues at β = 2, as diagonalized in Grabsch, Eqs. (3)–(4)."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("tauw"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Foundations.tauW"),
                H("tauW"), StatementSource.FromAuthor(Disp(F1())),
                AssessedProvenance.FromLiterature(Note()),
                Blocks(Paragraph(Text("Novaes, Section 1: “τW = (1/M) Tr(Q) is called the Wigner time delay”. The inverse delay rates are γ + xᵢ, and times are in dwell-time units."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("integrable-power-exp"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Foundations.integrable_power_exp"),
                H("integrable_power_exp"), StatementSource.FromAuthor(Disp(F2())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("power-exp-integral"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Foundations.power_exp_integral"),
                H("power_exp_integral"), StatementSource.FromAuthor(Disp(F3())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rawweight"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Foundations.rawWeight"),
                H("rawWeight"), StatementSource.FromAuthor(Disp(F4())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed definition is used in the moment and density expansions."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("supportset"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Foundations.supportSet"),
                H("supportSet"), StatementSource.FromAuthor(Disp(F5())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed definition is used in the moment and density expansions."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("strictsupportset"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Foundations.strictSupportSet"),
                H("strictSupportSet"), StatementSource.FromAuthor(Disp(F6())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed definition is used in the moment and density expansions."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("center"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Foundations.center"),
                H("center"), StatementSource.FromAuthor(Disp(F7())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed definition is used in the moment and density expansions."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("orthantmeasure"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Foundations.orthantMeasure"),
                H("orthantMeasure"), StatementSource.FromAuthor(Disp(F8())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed definition is used in the moment and density expansions."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("powersum"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Foundations.powerSum"),
                H("powerSum"), StatementSource.FromAuthor(Disp(F10())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed definition is used in the moment and density expansions."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("firstorder"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Foundations.FirstOrder"),
                H("FirstOrder"), StatementSource.FromAuthor(Disp(F12())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A first-order expansion at positive infinity with a remainder of order γ⁻²."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gammacgf"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Foundations.gammaCGF"),
                H("gammaCGF"), StatementSource.FromAuthor(Disp(F13())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed definition is used in the moment and density expansions."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("correctioncgf"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Foundations.correctionCGF"),
                H("correctionCGF"), StatementSource.FromAuthor(Disp(F14())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed definition is used in the moment and density expansions."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("inverseslope"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Foundations.inverseSlope"),
                H("inverseSlope"), StatementSource.FromAuthor(Disp(F15())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed definition is used in the moment and density expansions."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("law"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Foundations.law"),
                H("law"), StatementSource.FromAuthor(Disp(F16())),
                AssessedProvenance.FromLiterature(Note()),
                Blocks(Paragraph(Text("The joint weight normalized by its total mass."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("supportset-membership"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Foundations.supportSet_membership"),
                H("supportSet_membership"), StatementSource.FromAuthor(Disp(F17())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("weight-nonneg"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Foundations.weight_nonneg"),
                H("weight_nonneg"), StatementSource.FromAuthor(Disp(F18())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("strictsupportset-membership"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Foundations.strictSupportSet_membership"),
                H("strictSupportSet_membership"), StatementSource.FromAuthor(Disp(F19())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("orthant-restrict"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Foundations.orthant_restrict"),
                H("orthant_restrict"), StatementSource.FromAuthor(Disp(F20())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("polynomial-exp-integrable"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Foundations.polynomial_exp_integrable"),
                H("polynomial_exp_integrable"), StatementSource.FromAuthor(Disp(F21())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rescaledobservable"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Foundations.rescaledObservable"),
                H("rescaledObservable"), StatementSource.FromAuthor(Disp(F22())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed definition is used in the moment and density expansions."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("firstorder-tendsto"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Foundations.tendsto"),
                H("FirstOrder.tendsto"), StatementSource.FromAuthor(Disp(F25())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("firstorder-const"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Foundations.const"),
                H("FirstOrder.const"), StatementSource.FromAuthor(Disp(F26())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("firstorder-add"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Foundations.add"),
                H("FirstOrder.add"), StatementSource.FromAuthor(Disp(F27())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("firstorder-const-mul"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Foundations.const_mul"),
                H("FirstOrder.const_mul"), StatementSource.FromAuthor(Disp(F28())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("firstorder-sum"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Foundations.sum"),
                H("FirstOrder.sum"), StatementSource.FromAuthor(Disp(F29())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("firstorder-eventual-bound"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Foundations.eventual_bound"),
                H("FirstOrder.eventual_bound"), StatementSource.FromAuthor(Disp(F30())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gammacgf-deriv"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Foundations.gammaCGF_deriv"),
                H("gammaCGF_deriv"), StatementSource.FromAuthor(Disp(F31())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("kappa"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Foundations.kappa"),
                H("kappa"), StatementSource.FromAuthor(Disp(F32())),
                AssessedProvenance.FromLiterature(Note()),
                Blocks(Paragraph(Text("The n-th cumulant is the n-th derivative at zero of the cumulant generating function of tauW under law."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("center-properties"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Foundations.center_properties"),
                H("center_properties"), StatementSource.FromAuthor(Disp(F33())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rescaledobservable-eq-u"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Foundations.rescaledObservable_eq_u"),
                H("rescaledObservable_eq_u"), StatementSource.FromAuthor(Disp(F34())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("firstorder-mul"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Foundations.mul"),
                H("FirstOrder.mul"), StatementSource.FromAuthor(Disp(F35())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("measurable-weight"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Foundations.measurable_weight"),
                H("measurable_weight"), StatementSource.FromAuthor(Disp(F36())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("observable-power-remainder"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Foundations.observable_power_remainder"),
                H("observable_power_remainder"), StatementSource.FromAuthor(Disp(F37())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("observable-power-one"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Foundations.observable_power_one"),
                H("observable_power_one"), StatementSource.FromAuthor(Disp(F38())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("firstorder-sub"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Foundations.sub"),
                H("FirstOrder.sub"), StatementSource.FromAuthor(Disp(F39())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gammacgf-iterated"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Foundations.gammaCGF_iterated"),
                H("gammaCGF_iterated"), StatementSource.FromAuthor(Disp(F40())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("mass-pos"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Foundations.mass_pos"),
                H("mass_pos"), StatementSource.FromAuthor(Disp(F41())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("law-ae-support"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Foundations.law_ae_support"),
                H("law_ae_support"), StatementSource.FromAuthor(Disp(F42())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("law-integral"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Foundations.law_integral"),
                H("law_integral"), StatementSource.FromAuthor(Disp(F43())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("correctioncgf-iterated"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Foundations.correctionCGF_iterated"),
                H("correctionCGF_iterated"), StatementSource.FromAuthor(Disp(F44())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("law-isprobability"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Foundations.law_isProbability"),
                H("law_isProbability"), StatementSource.FromAuthor(Disp(F45())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rescaledobservable-integrable-exp"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Foundations.rescaledObservable_integrable_exp"),
                H("rescaledObservable_integrable_exp"), StatementSource.FromAuthor(Disp(F46())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("kappa-rescaled"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Foundations.kappa_rescaled"),
                H("kappa_rescaled"), StatementSource.FromAuthor(Disp(F47())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rescaled-moment-cumulant"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Foundations.rescaled_moment_cumulant"),
                H("rescaled_moment_cumulant"), StatementSource.FromAuthor(Disp(F48())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity or estimate is used in the moment and density expansions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("published-inverseslope-deriv"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/Foundations.inverseSlope_deriv"),
                H("inverseSlope_deriv"), StatementSource.FromAuthor(Disp(Published0())),
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
    private static LibraryNoteRef Note() => LibraryNoteRef.Create("D5/L/StatisticalMechanics/novaes2023absorption");

    private static Formula ExpSumProd() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp,
            Forall, Sp, Parenthesized(Seq(V("a"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp,
            Forall, Sp, Parenthesized(Seq(V("p"), Sp, Colon, Sp,
                Parenthesized(Seq(V("Fin"), Sp, V("M"), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Times, Sp,
                Parenthesized(Seq(V("Fin"), Sp, V("M"), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))))), Sp, Comma, Sp,
            Qualified("Real", "exp"), Sp, Parenthesized(Seq(Minus, V("a"), Sp, Cdot, Sp,
                Parenthesized(Seq(Parenthesized(Seq(Sum, Sp, V("i"), Sp, Comma, Sp, V("p"), Dot, D(1), Sp, V("i"))), Sp, Plus, Sp,
                    Sum, Sp, V("j"), Sp, Comma, Sp, V("p"), Dot, D(2), Sp, V("j"))))), Sp, Eq, Sp,
            Parenthesized(Seq(Prod, Sp, V("i"), Sp, Comma, Sp, Qualified("Real", "exp"), Sp,
                Parenthesized(Seq(Minus, Parenthesized(Seq(V("a"), Sp, Cdot, Sp, V("p"), Dot, D(1), Sp, V("i"))))))), Sp, Cdot, Sp,
            Prod, Sp, V("j"), Sp, Comma, Sp, Qualified("Real", "exp"), Sp,
                Parenthesized(Seq(Minus, Parenthesized(Seq(V("a"), Sp, Cdot, Sp, V("p"), Dot, D(2), Sp, V("j"))))));

    private static Formula F0() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(GammaLower, Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("p"), Sp, Colon, Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Times, Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))))), Sp, Comma, Sp, V("weight"), Sp, V("M"), Sp, GammaLower, Sp, V("p"), Sp, Eq, Sp, Parenthesized(Seq(V("if"), Sp, Parenthesized(Seq(Forall, Sp, V("i"), Sp, Comma, Sp, D(0), Sp, Le, Sp, V("p"), Sp, Dot, Sp, D(1), Sp, V("i"))), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, V("j"), Sp, Comma, Sp, D(0), Sp, Le, Sp, V("p"), Sp, Dot, Sp, D(2), Sp, V("j"), Sp, Land, Sp, V("p"), Sp, Dot, Sp, D(2), Sp, V("j"), Sp, Le, Sp, GammaLower)), Sp, V("then"), Sp, Qualified("Real","exp"), Sp, Parenthesized(Seq(Minus, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Cdot, Sp, Parenthesized(Seq(Sum, Sp, V("i"), Sp, Comma, Sp, V("p"), Sp, Dot, Sp, D(1), Sp, V("i"), Sp, Plus, Sp, Sum, Sp, V("j"), Sp, Comma, Sp, V("p"), Sp, Dot, Sp, D(2), Sp, V("j"))))), Sp, Cdot, Sp, Parenthesized(Seq(Prod, Sp, V("i"), Sp, Comma, Sp, Prod, Sp, V("j"), Sp, Comma, Sp, V("if"), Sp, V("i"), Sp, Lt, Sp, V("j"), Sp, V("then"), Sp, Sp, new Formula.Power(Parenthesized(Seq(V("p"), Sp, Dot, Sp, D(1), Sp, V("i"), Sp, Minus, Sp, V("p"), Sp, Dot, Sp, D(1), Sp, V("j"))), D(2)), Sp, Cdot, Sp, Sp, new Formula.Power(Parenthesized(Seq(V("p"), Sp, Dot, Sp, D(2), Sp, V("i"), Sp, Minus, Sp, V("p"), Sp, Dot, Sp, D(2), Sp, V("j"))), D(2)), Sp, V("else"), Sp, D(1))), Sp, Cdot, Sp, Prod, Sp, V("i"), Sp, Comma, Sp, Prod, Sp, V("j"), Sp, Comma, Sp, Parenthesized(Seq(GammaLower, Sp, Plus, Sp, V("p"), Sp, Dot, Sp, D(1), Sp, V("i"), Sp, Minus, Sp, V("p"), Sp, Dot, Sp, D(2), Sp, V("j"))), Sp, V("else"), Sp, D(0))));

    private static Formula F1() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(GammaLower, Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("p"), Sp, Colon, Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Times, Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))))), Sp, Comma, Sp, V("tauW"), Sp, V("M"), Sp, GammaLower, Sp, V("p"), Sp, Eq, Sp, Parenthesized(Seq(new Formula.Power(Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Seq(Minus, D(1))), Sp, Cdot, Sp, Sum, Sp, V("i"), Sp, Comma, Sp, D(1), Sp, Slash, Sp, Parenthesized(Seq(GammaLower, Sp, Plus, Sp, V("p"), Sp, Dot, Sp, D(1), Sp, V("i"))))));

    private static Formula F2() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("a"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Parenthesized(Seq(D(0), Sp, Lt, Sp, V("a"))), Sp, To, Sp, V("IntegrableOn"), Sp, Parenthesized(Seq(V("fun"), Sp, V("x"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))), Sp, Mapsto, Sp, Sp, new Formula.Power(V("x"), V("k")), Sp, Cdot, Sp, Qualified("Real","exp"), Sp, Parenthesized(Seq(Minus, Sp, Parenthesized(Seq(V("a"), Sp, Cdot, Sp, V("x"))))))), Sp, Parenthesized(Seq(V("Ici"), Sp, D(0))));

    private static Formula F3() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("a"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Parenthesized(Seq(D(0), Sp, Lt, Sp, V("a"))), Sp, To, Sp, Parenthesized(Seq(Int, Sp, V("x"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))), Sp, V("in"), Sp, V("Ici"), Sp, D(0), Sp, Comma, Sp, Sp, new Formula.Power(V("x"), V("k")), Sp, Cdot, Sp, Qualified("Real","exp"), Sp, Parenthesized(Seq(Minus, Sp, Parenthesized(Seq(V("a"), Sp, Cdot, Sp, V("x"))))))), Sp, Eq, Sp, Parenthesized(Seq(Qualified("k","factorial"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Slash, Sp, Sp, new Formula.Power(V("a"), Seq(V("k"), Sp, Plus, Sp, D(1))));

    private static Formula F4() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(GammaLower, Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("p"), Sp, Colon, Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Times, Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))))), Sp, Comma, Sp, V("rawWeight"), Sp, V("M"), Sp, GammaLower, Sp, V("p"), Sp, Eq, Sp, Parenthesized(Seq(Qualified("Real","exp"), Sp, Parenthesized(Seq(Minus, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Cdot, Sp, Parenthesized(Seq(Parenthesized(Seq(Sum, Sp, V("i"), Sp, Comma, Sp, V("p"), Sp, Dot, Sp, D(1), Sp, V("i"))), Sp, Plus, Sp, Sum, Sp, V("j"), Sp, Comma, Sp, V("p"), Sp, Dot, Sp, D(2), Sp, V("j"))))), Sp, Cdot, Sp, Parenthesized(Seq(Prod, Sp, V("i"), Sp, Comma, Sp, Prod, Sp, V("j"), Sp, Comma, Sp, V("if"), Sp, V("i"), Sp, Lt, Sp, V("j"), Sp, V("then"), Sp, Sp, new Formula.Power(Parenthesized(Seq(V("p"), Sp, Dot, Sp, D(1), Sp, V("i"), Sp, Minus, Sp, V("p"), Sp, Dot, Sp, D(1), Sp, V("j"))), D(2)), Sp, Cdot, Sp, Sp, new Formula.Power(Parenthesized(Seq(V("p"), Sp, Dot, Sp, D(2), Sp, V("i"), Sp, Minus, Sp, V("p"), Sp, Dot, Sp, D(2), Sp, V("j"))), D(2)), Sp, V("else"), Sp, D(1))), Sp, Cdot, Sp, Prod, Sp, V("i"), Sp, Comma, Sp, Prod, Sp, V("j"), Sp, Comma, Sp, Parenthesized(Seq(GammaLower, Sp, Plus, Sp, V("p"), Sp, Dot, Sp, D(1), Sp, V("i"), Sp, Minus, Sp, V("p"), Sp, Dot, Sp, D(2), Sp, V("j"))))));

    private static Formula F5() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(GammaLower, Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, V("supportSet"), Sp, V("M"), Sp, GammaLower, Sp, Eq, Sp, Parenthesized(Seq(Parenthesized(Seq(Qualified("Set","univ","pi"), Sp, Parenthesized(Seq(Qualified("Function","const"), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, Parenthesized(Seq(Qualified("Set","Ici"), Sp, D(0))))))), Sp, Seq(Times, Sup(V("s"))), Sp, Parenthesized(Seq(Qualified("Set","univ","pi"), Sp, Parenthesized(Seq(Qualified("Function","const"), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, Parenthesized(Seq(Qualified("Set","Icc"), Sp, D(0), Sp, GammaLower)))))))));

    private static Formula F6() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(GammaLower, Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, V("strictSupportSet"), Sp, V("M"), Sp, GammaLower, Sp, Eq, Sp, Parenthesized(Seq(Parenthesized(Seq(Qualified("Set","univ","pi"), Sp, Parenthesized(Seq(Qualified("Function","const"), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, Parenthesized(Seq(Qualified("Set","Ioi"), Sp, D(0))))))), Sp, Seq(Times, Sup(V("s"))), Sp, Parenthesized(Seq(Qualified("Set","univ","pi"), Sp, Parenthesized(Seq(Qualified("Function","const"), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, Parenthesized(Seq(Qualified("Set","Ioo"), Sp, D(0), Sp, GammaLower)))))))));

    private static Formula F7() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(GammaLower, Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, V("center"), Sp, V("M"), Sp, GammaLower, Sp, Eq, Sp, Parenthesized(Parenthesized(Seq(V("fun"), Sp, V("i"), Sp, Mapsto, Sp, Parenthesized(Seq(Call("val", V("i")), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Plus, Sp, D(1), Sp, Comma, Sp, V("fun"), Sp, V("i"), Sp, Mapsto, Sp, GammaLower, Sp, Cdot, Sp, Parenthesized(Seq(Parenthesized(Seq(Call("val", V("i")), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Plus, Sp, D(1))), Sp, Slash, Sp, Parenthesized(Seq(Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Plus, Sp, D(1)))))));

    private static Formula F8() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, V("orthantMeasure"), Sp, V("M"), Sp, Eq, Sp, Parenthesized(Seq(Qualified("Measure","pi"), Sp, Parenthesized(Seq(Qualified("Function","const"), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, Parenthesized(Seq(Parenthesized(Seq(V("volume"), Sp, Colon, Sp, V("Measure"), Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Dot, Sp, V("restrict"), Sp, Parenthesized(Seq(V("Ici"), Sp, D(0))))))))));


    private static Formula F10() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("r"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("x"), Sp, Colon, Sp, V("Fin"), Sp, V("M"), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, V("powerSum"), Sp, V("M"), Sp, V("r"), Sp, V("x"), Sp, Eq, Sp, Parenthesized(Seq(Sum, Sp, V("i"), Sp, Comma, Sp, Sp, new Formula.Power(Parenthesized(Seq(V("x"), Sp, V("i"))), V("r")))));


    private static Formula F12() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("f"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("a"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("b"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, V("FirstOrder"), Sp, V("f"), Sp, V("a"), Sp, V("b"), Sp, Eq, Sp, Parenthesized(Seq(Parenthesized(Seq(V("fun"), Sp, GammaLower, Sp, Mapsto, Sp, V("f"), Sp, GammaLower, Sp, Minus, Sp, V("a"), Sp, Minus, Sp, V("b"), Sp, Cdot, Sp, new Formula.Power(GammaLower, Seq(Minus, D(1))))), Sp, Seq(Eq, V("O")), Sp, Seq(OpenBracket, V("atTop"), CloseBracket), Sp, Parenthesized(Seq(V("fun"), Sp, GammaLower, Sp, Mapsto, Sp, Sp, new Formula.Power(new Formula.Power(GammaLower, Seq(Minus, D(1))), D(2)))))));

    private static Formula F13() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("t"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, V("gammaCGF"), Sp, V("d"), Sp, V("t"), Sp, Eq, Sp, Parenthesized(Seq(Minus, Sp, V("d"), Sp, Cdot, Sp, Qualified("Real","log"), Sp, Parenthesized(Seq(D(1), Sp, Minus, Sp, V("t"), Sp, Slash, Sp, V("d"))))));

    private static Formula F14() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("t"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, V("correctionCGF"), Sp, V("d"), Sp, V("t"), Sp, Eq, Sp, Parenthesized(Seq(V("t"), Sp, Slash, Sp, Parenthesized(Seq(D(1), Sp, Minus, Sp, V("t"), Sp, Slash, Sp, V("d"))), Sp, Minus, Sp, D(2), Sp, Cdot, Sp, V("t"), Sp, Slash, Sp, Sp, new Formula.Power(Parenthesized(Seq(D(1), Sp, Minus, Sp, V("t"), Sp, Slash, Sp, V("d"))), D(2)))));

    private static Formula F15() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("t"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, V("inverseSlope"), Sp, V("d"), Sp, V("t"), Sp, Eq, Sp, Parenthesized(new Formula.Power(Parenthesized(Seq(D(1), Sp, Minus, Sp, V("t"), Sp, Slash, Sp, V("d"))), Seq(Minus, D(1)))));

    private static Formula F16() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(GammaLower, Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, V("law"), Sp, V("M"), Sp, GammaLower, Sp, Eq, Sp, Parenthesized(Seq(V("let"), Sp, Mu, Sp, Seq(Colon, Eq), Sp, Qualified("volume","withDensity"), Sp, Parenthesized(Seq(V("fun"), Sp, V("p"), Sp, Mapsto, Sp, Qualified("ENNReal","ofReal"), Sp, Parenthesized(Seq(V("weight"), Sp, V("M"), Sp, GammaLower, Sp, V("p"))))), Sp, Semi, Sp, new Formula.Power(Parenthesized(Seq(Mu, Sp, Qualified("Set","univ"))), Seq(Minus, D(1))), Sp, Cdot, Sp, Mu)));

    private static Formula F17() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(GammaLower, Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("p"), Sp, Colon, Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Times, Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))))), Sp, Comma, Sp, V("p"), Sp, InMacro, Sp, V("supportSet"), Sp, V("M"), Sp, GammaLower, Sp, Leftrightarrow, Sp, Parenthesized(Seq(Forall, Sp, V("i"), Sp, Comma, Sp, D(0), Sp, Le, Sp, V("p"), Sp, Dot, Sp, D(1), Sp, V("i"))), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, V("j"), Sp, Comma, Sp, D(0), Sp, Le, Sp, V("p"), Sp, Dot, Sp, D(2), Sp, V("j"), Sp, Land, Sp, V("p"), Sp, Dot, Sp, D(2), Sp, V("j"), Sp, Le, Sp, GammaLower)));

    private static Formula F18() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(GammaLower, Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("p"), Sp, Colon, Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Times, Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))))), Sp, Comma, Sp, D(0), Sp, Le, Sp, V("weight"), Sp, V("M"), Sp, GammaLower, Sp, V("p"));

    private static Formula F19() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(GammaLower, Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("p"), Sp, Colon, Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Times, Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))))), Sp, Comma, Sp, V("p"), Sp, InMacro, Sp, V("strictSupportSet"), Sp, V("M"), Sp, GammaLower, Sp, Leftrightarrow, Sp, Parenthesized(Seq(Forall, Sp, V("i"), Sp, Comma, Sp, D(0), Sp, Lt, Sp, V("p"), Sp, Dot, Sp, D(1), Sp, V("i"))), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, V("j"), Sp, Comma, Sp, D(0), Sp, Lt, Sp, V("p"), Sp, Dot, Sp, D(2), Sp, V("j"), Sp, Land, Sp, V("p"), Sp, Dot, Sp, D(2), Sp, V("j"), Sp, Lt, Sp, GammaLower)));

    private static Formula F20() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Parenthesized(Seq(V("volume"), Sp, Colon, Sp, V("Measure"), Sp, Parenthesized(Seq(Parenthesized(Seq(V("Fin"), Sp, V("M"), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Times, Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))))))), Sp, Dot, Sp, V("restrict"), Sp, Parenthesized(Parenthesized(Seq(Qualified("Set","Ici"), Sp, Parenthesized(Seq(D(0), Sp, Colon, Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Times, Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"), Sp, To, Sp, Seq(Mathbb, Grp(V("R")))))))))), Sp, Eq, Sp, Parenthesized(Seq(V("orthantMeasure"), Sp, V("M"))), Sp, Dot, Sp, V("prod"), Sp, Parenthesized(Seq(V("orthantMeasure"), Sp, V("M"))));

    private static Formula F21() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("a"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("P"), Sp, Colon, Sp, V("MvPolynomial"), Sp, Parenthesized(Seq(V("Sum"), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))))), Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Parenthesized(Seq(D(0), Sp, Lt, Sp, V("a"))), Sp, To, Sp, V("Integrable"), Sp, Parenthesized(Seq(V("fun"), Sp, V("p"), Sp, Colon, Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Times, Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Mapsto, Sp, Qualified("Real","exp"), Sp, Parenthesized(Seq(Minus, Sp, V("a"), Sp, Cdot, Sp, Parenthesized(Seq(Parenthesized(Seq(Sum, Sp, V("i"), Sp, Comma, Sp, V("p"), Sp, Dot, Sp, D(1), Sp, V("i"))), Sp, Plus, Sp, Sum, Sp, V("j"), Sp, Comma, Sp, V("p"), Sp, Dot, Sp, D(2), Sp, V("j"))))), Sp, Cdot, Sp, Qualified("MvPolynomial","eval"), Sp, Parenthesized(Seq(Qualified("Sum","elim"), Sp, V("p"), Sp, Dot, Sp, D(1), Sp, V("p"), Sp, Dot, Sp, D(2))), Sp, V("P"))), Sp, Parenthesized(Seq(Parenthesized(Seq(V("orthantMeasure"), Sp, V("M"))), Sp, Dot, Sp, V("prod"), Sp, Parenthesized(Seq(V("orthantMeasure"), Sp, V("M"))))));

    private static Formula F22() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(GammaLower, Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("p"), Sp, Colon, Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Times, Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))))), Sp, Comma, Sp, V("rescaledObservable"), Sp, V("M"), Sp, GammaLower, Sp, V("p"), Sp, Eq, Sp, Parenthesized(Seq(new Formula.Power(GammaLower, D(2)), Sp, Cdot, Sp, Parenthesized(Seq(new Formula.Power(GammaLower, Seq(Minus, D(1))), Sp, Minus, Sp, V("tauW"), Sp, V("M"), Sp, GammaLower, Sp, V("p"))))));



    private static Formula F25() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("f"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("a"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("b"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Parenthesized(Seq(V("FirstOrder"), Sp, V("f"), Sp, V("a"), Sp, V("b"))), Sp, To, Sp, V("Tendsto"), Sp, V("f"), Sp, V("atTop"), Sp, Parenthesized(Seq(V("nhds"), Sp, V("a"))));

    private static Formula F26() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("a"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, V("FirstOrder"), Sp, Parenthesized(Seq(Qualified("Function","const"), Sp, Seq(Mathbb, Grp(V("R"))), Sp, V("a"))), Sp, V("a"), Sp, D(0));

    private static Formula F27() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("f"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("g"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("a"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("b"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("c"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Parenthesized(Seq(V("FirstOrder"), Sp, V("f"), Sp, V("a"), Sp, V("b"))), Sp, To, Sp, Parenthesized(Seq(V("FirstOrder"), Sp, V("g"), Sp, V("c"), Sp, V("d"))), Sp, To, Sp, V("FirstOrder"), Sp, Parenthesized(Seq(V("fun"), Sp, GammaLower, Sp, Mapsto, Sp, V("f"), Sp, GammaLower, Sp, Plus, Sp, V("g"), Sp, GammaLower)), Sp, Parenthesized(Seq(V("a"), Sp, Plus, Sp, V("c"))), Sp, Parenthesized(Seq(V("b"), Sp, Plus, Sp, V("d"))));

    private static Formula F28() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("f"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("a"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("b"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("c"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Parenthesized(Seq(V("FirstOrder"), Sp, V("f"), Sp, V("a"), Sp, V("b"))), Sp, To, Sp, V("FirstOrder"), Sp, Parenthesized(Seq(V("fun"), Sp, GammaLower, Sp, Mapsto, Sp, V("c"), Sp, Cdot, Sp, V("f"), Sp, GammaLower)), Sp, Parenthesized(Seq(V("c"), Sp, Cdot, Sp, V("a"))), Sp, Parenthesized(Seq(V("c"), Sp, Cdot, Sp, V("b"))));

    private static Formula F29() =>
        Seq(Forall, Sp, Parenthesized(Seq(SigmaLower, Sp, Colon, Sp, V("Type"))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("s"), Sp, Colon, Sp, V("Finset"), Sp, SigmaLower)), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("f"), Sp, Colon, Sp, SigmaLower, Sp, To, Sp, Seq(Mathbb, Grp(V("R"))), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("a"), Sp, Colon, Sp, SigmaLower, Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("b"), Sp, Colon, Sp, SigmaLower, Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Parenthesized(Seq(Forall, Sp, V("i"), Sp, InMacro, Sp, V("s"), Sp, Comma, Sp, V("FirstOrder"), Sp, Parenthesized(Seq(V("f"), Sp, V("i"))), Sp, Parenthesized(Seq(V("a"), Sp, V("i"))), Sp, Parenthesized(Seq(V("b"), Sp, V("i"))))), Sp, To, Sp, V("FirstOrder"), Sp, Parenthesized(Seq(V("fun"), Sp, GammaLower, Sp, Mapsto, Sp, Sum, Sp, V("i"), Sp, InMacro, Sp, V("s"), Sp, Comma, Sp, V("f"), Sp, V("i"), Sp, GammaLower)), Sp, Parenthesized(Seq(Sum, Sp, V("i"), Sp, InMacro, Sp, V("s"), Sp, Comma, Sp, V("a"), Sp, V("i"))), Sp, Parenthesized(Seq(Sum, Sp, V("i"), Sp, InMacro, Sp, V("s"), Sp, Comma, Sp, V("b"), Sp, V("i"))));

    private static Formula F30() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("f"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("a"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("b"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Parenthesized(Seq(V("FirstOrder"), Sp, V("f"), Sp, V("a"), Sp, V("b"))), Sp, To, Sp, Exists, Sp, V("C"), Sp, new Formula.Subscript(GammaLower, D(0)), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))), Sp, Comma, Sp, D(0), Sp, Lt, Sp, new Formula.Subscript(GammaLower, D(0)), Sp, Land, Sp, Forall, Sp, GammaLower, Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))), Sp, Comma, Sp, new Formula.Subscript(GammaLower, D(0)), Sp, Le, Sp, GammaLower, Sp, To, Sp, Bar, Sp, V("f"), Sp, GammaLower, Sp, Minus, Sp, V("a"), Sp, Minus, Sp, V("b"), Sp, Slash, Sp, GammaLower, Sp, Bar, Sp, Le, Sp, V("C"), Sp, Slash, Sp, Sp, new Formula.Power(GammaLower, D(2)));

    private static Formula F31() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Parenthesized(Seq(V("d"), Sp, Neq, Sp, D(0))), Sp, To, Sp, V("deriv"), Sp, Parenthesized(Seq(V("gammaCGF"), Sp, V("d"))), Sp, Eq, Sp, V("inverseSlope"), Sp, V("d"));

    private static Formula F32() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(GammaLower, Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, V("kappa"), Sp, V("M"), Sp, V("n"), Sp, GammaLower, Sp, Eq, Sp, Parenthesized(Seq(V("iteratedDeriv"), Sp, V("n"), Sp, Parenthesized(Seq(V("cgf"), Sp, Parenthesized(Seq(V("tauW"), Sp, V("M"), Sp, GammaLower)), Sp, Parenthesized(Seq(V("law"), Sp, V("M"), Sp, GammaLower)))), Sp, D(0))));

    private static Formula F33() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(GammaLower, Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Parenthesized(Seq(D(0), Sp, Lt, Sp, GammaLower)), Sp, To, Sp, V("center"), Sp, V("M"), Sp, GammaLower, Sp, InMacro, Sp, V("strictSupportSet"), Sp, V("M"), Sp, GammaLower, Sp, Land, Sp, Qualified("Function","Injective"), Sp, Parenthesized(Seq(Parenthesized(Seq(V("center"), Sp, V("M"), Sp, GammaLower)), Sp, Dot, Sp, D(1))), Sp, Land, Sp, Qualified("Function","Injective"), Sp, Parenthesized(Seq(Parenthesized(Seq(V("center"), Sp, V("M"), Sp, GammaLower)), Sp, Dot, Sp, D(2))));

    private static Formula F34() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(GammaLower, Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("p"), Sp, Colon, Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Times, Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))))), Sp, Comma, Sp, Parenthesized(Seq(D(1), Sp, Le, Sp, V("M"))), Sp, To, Sp, Parenthesized(Seq(D(0), Sp, Lt, Sp, GammaLower)), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, V("i"), Sp, Comma, Sp, D(0), Sp, Le, Sp, V("p"), Sp, Dot, Sp, D(1), Sp, V("i"))), Sp, To, Sp, V("rescaledObservable"), Sp, V("M"), Sp, GammaLower, Sp, V("p"), Sp, Eq, Sp, Parenthesized(Seq(Qualified("Finset","expect"), Sp, Qualified("Finset","univ"), Sp, Parenthesized(Seq(V("fun"), Sp, V("i"), Sp, Mapsto, Sp, V("p"), Sp, Dot, Sp, D(1), Sp, V("i"), Sp, Slash, Sp, Parenthesized(Seq(D(1), Sp, Plus, Sp, new Formula.Power(GammaLower, Seq(Minus, D(1))), Sp, Cdot, Sp, V("p"), Sp, Dot, Sp, D(1), Sp, V("i"))))))));

    private static Formula F35() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("f"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("g"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("a"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("b"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("c"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Parenthesized(Seq(V("FirstOrder"), Sp, V("f"), Sp, V("a"), Sp, V("b"))), Sp, To, Sp, Parenthesized(Seq(V("FirstOrder"), Sp, V("g"), Sp, V("c"), Sp, V("d"))), Sp, To, Sp, V("FirstOrder"), Sp, Parenthesized(Seq(V("fun"), Sp, GammaLower, Sp, Mapsto, Sp, V("f"), Sp, GammaLower, Sp, Cdot, Sp, V("g"), Sp, GammaLower)), Sp, Parenthesized(Seq(V("a"), Sp, Cdot, Sp, V("c"))), Sp, Parenthesized(Seq(V("a"), Sp, Cdot, Sp, V("d"), Sp, Plus, Sp, V("b"), Sp, Cdot, Sp, V("c"))));

    private static Formula F36() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(GammaLower, Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, V("Measurable"), Sp, Parenthesized(Seq(V("weight"), Sp, V("M"), Sp, GammaLower)));

    private static Formula F37() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(Varepsilon, Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("x"), Sp, Colon, Sp, V("Fin"), Sp, V("M"), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Parenthesized(Seq(D(0), Sp, Le, Sp, Varepsilon)), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, V("i"), Sp, Comma, Sp, D(0), Sp, Le, Sp, V("x"), Sp, V("i"))), Sp, To, Sp, Bar, Sp, Sp, new Formula.Power(Parenthesized(Seq(Qualified("Finset","expect"), Sp, Qualified("Finset","univ"), Sp, Parenthesized(Seq(V("fun"), Sp, V("i"), Sp, Mapsto, Sp, V("x"), Sp, V("i"), Sp, Slash, Sp, Parenthesized(Seq(D(1), Sp, Plus, Sp, Varepsilon, Sp, Cdot, Sp, V("x"), Sp, V("i"))))))), Seq(V("k"), Sp, Plus, Sp, D(2))), Sp, Minus, Sp, Sp, new Formula.Power(Parenthesized(Seq(Qualified("Finset","expect"), Sp, Qualified("Finset","univ"), Sp, V("x"))), Seq(V("k"), Sp, Plus, Sp, D(2))), Sp, Plus, Sp, Varepsilon, Sp, Cdot, Sp, Parenthesized(Seq(V("k"), Sp, Plus, Sp, D(2), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Cdot, Sp, Parenthesized(Seq(Qualified("Finset","expect"), Sp, Qualified("Finset","univ"), Sp, Parenthesized(Seq(V("fun"), Sp, V("i"), Sp, Mapsto, Sp, Sp, new Formula.Power(Parenthesized(Seq(V("x"), Sp, V("i"))), D(2)))))), Sp, Cdot, Sp, Sp, new Formula.Power(Parenthesized(Seq(Qualified("Finset","expect"), Sp, Qualified("Finset","univ"), Sp, V("x"))), Seq(V("k"), Sp, Plus, Sp, D(1))), Sp, Bar, Sp, Le, Sp, Sp, new Formula.Power(Varepsilon, D(2)), Sp, Cdot, Sp, Parenthesized(Seq(Parenthesized(Seq(Parenthesized(Seq(V("k"), Sp, Plus, Sp, D(2), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Cdot, Sp, Parenthesized(Seq(V("k"), Sp, Plus, Sp, D(1))), Sp, Slash, Sp, D(2))), Sp, Cdot, Sp, Sp, new Formula.Power(Parenthesized(Parenthesized(Seq(Qualified("Finset","expect"), Sp, Qualified("Finset","univ"), Sp, Parenthesized(Seq(V("fun"), Sp, V("i"), Sp, Mapsto, Sp, Sp, new Formula.Power(Parenthesized(Seq(V("x"), Sp, V("i"))), D(2))))))), D(2)), Sp, Cdot, Sp, Sp, new Formula.Power(Parenthesized(Seq(Qualified("Finset","expect"), Sp, Qualified("Finset","univ"), Sp, V("x"))), V("k")), Sp, Plus, Sp, Parenthesized(Seq(V("k"), Sp, Plus, Sp, D(2), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Cdot, Sp, Parenthesized(Seq(new Formula.Power(Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Seq(Minus, D(1))), Sp, Cdot, Sp, V("powerSum"), Sp, V("M"), Sp, D(3), Sp, V("x"))), Sp, Cdot, Sp, Sp, new Formula.Power(Parenthesized(Seq(Qualified("Finset","expect"), Sp, Qualified("Finset","univ"), Sp, V("x"))), Seq(V("k"), Sp, Plus, Sp, D(1))))));

    private static Formula F38() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(Varepsilon, Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("x"), Sp, Colon, Sp, V("Fin"), Sp, V("M"), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Parenthesized(Seq(D(0), Sp, Le, Sp, Varepsilon)), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, V("i"), Sp, Comma, Sp, D(0), Sp, Le, Sp, V("x"), Sp, V("i"))), Sp, To, Sp, Bar, Sp, Parenthesized(Seq(Qualified("Finset","expect"), Sp, Qualified("Finset","univ"), Sp, Parenthesized(Seq(V("fun"), Sp, V("i"), Sp, Mapsto, Sp, V("x"), Sp, V("i"), Sp, Slash, Sp, Parenthesized(Seq(D(1), Sp, Plus, Sp, Varepsilon, Sp, Cdot, Sp, V("x"), Sp, V("i"))))))), Sp, Minus, Sp, Parenthesized(Seq(Qualified("Finset","expect"), Sp, Qualified("Finset","univ"), Sp, V("x"))), Sp, Plus, Sp, Varepsilon, Sp, Cdot, Sp, Parenthesized(Seq(Qualified("Finset","expect"), Sp, Qualified("Finset","univ"), Sp, Parenthesized(Seq(V("fun"), Sp, V("i"), Sp, Mapsto, Sp, Sp, new Formula.Power(Parenthesized(Seq(V("x"), Sp, V("i"))), D(2)))))), Sp, Bar, Sp, Le, Sp, Sp, new Formula.Power(Varepsilon, D(2)), Sp, Cdot, Sp, Parenthesized(Seq(new Formula.Power(Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Seq(Minus, D(1))), Sp, Cdot, Sp, V("powerSum"), Sp, V("M"), Sp, D(3), Sp, V("x"))));

    private static Formula F39() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("f"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("g"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("a"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("b"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("c"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Parenthesized(Seq(V("FirstOrder"), Sp, V("f"), Sp, V("a"), Sp, V("b"))), Sp, To, Sp, Parenthesized(Seq(V("FirstOrder"), Sp, V("g"), Sp, V("c"), Sp, V("d"))), Sp, To, Sp, V("FirstOrder"), Sp, Parenthesized(Seq(V("fun"), Sp, GammaLower, Sp, Mapsto, Sp, V("f"), Sp, GammaLower, Sp, Minus, Sp, V("g"), Sp, GammaLower)), Sp, Parenthesized(Seq(V("a"), Sp, Minus, Sp, V("c"))), Sp, Parenthesized(Seq(V("b"), Sp, Minus, Sp, V("d"))));

    private static Formula F40() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Parenthesized(Seq(V("d"), Sp, Neq, Sp, D(0))), Sp, To, Sp, V("iteratedDeriv"), Sp, Parenthesized(Seq(V("n"), Sp, Plus, Sp, D(1))), Sp, Parenthesized(Seq(V("gammaCGF"), Sp, V("d"))), Sp, D(0), Sp, Eq, Sp, Parenthesized(Seq(Qualified("n","factorial"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Slash, Sp, Sp, new Formula.Power(V("d"), V("n")));

    private static Formula F41() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(GammaLower, Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Parenthesized(Seq(D(0), Sp, Lt, Sp, GammaLower)), Sp, To, Sp, D(0), Sp, Lt, Sp, Parenthesized(Seq(Qualified("volume","withDensity"), Sp, Parenthesized(Seq(V("fun"), Sp, V("p"), Sp, Mapsto, Sp, Qualified("ENNReal","ofReal"), Sp, Parenthesized(Seq(V("weight"), Sp, V("M"), Sp, GammaLower, Sp, V("p"))))))), Sp, Qualified("Set","univ"));

    private static Formula F42() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(GammaLower, Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Sup(V("m")), Sp, V("p"), Sp, V("d"), Sp, V("law"), Sp, V("M"), Sp, GammaLower, Sp, Comma, Sp, V("p"), Sp, InMacro, Sp, V("supportSet"), Sp, V("M"), Sp, GammaLower);

    private static Formula F43() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(GammaLower, Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("f"), Sp, Colon, Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Times, Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, To, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Parenthesized(Seq(D(1), Sp, Le, Sp, V("M"))), Sp, To, Sp, Parenthesized(Seq(Int, Sp, V("p"), Sp, Comma, Sp, V("f"), Sp, V("p"), Sp, V("d"), Sp, V("law"), Sp, V("M"), Sp, GammaLower)), Sp, Eq, Sp, Parenthesized(Seq(Int, Sp, V("p"), Sp, Comma, Sp, V("weight"), Sp, V("M"), Sp, GammaLower, Sp, V("p"), Sp, Cdot, Sp, V("f"), Sp, V("p"))), Sp, Slash, Sp, Parenthesized(Seq(Int, Sp, V("p"), Sp, Comma, Sp, V("weight"), Sp, V("M"), Sp, GammaLower, Sp, V("p"))));

    private static Formula F44() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Parenthesized(Seq(V("d"), Sp, Neq, Sp, D(0))), Sp, To, Sp, Parenthesized(Seq(D(1), Sp, Le, Sp, V("n"))), Sp, To, Sp, V("iteratedDeriv"), Sp, V("n"), Sp, Parenthesized(Seq(V("correctionCGF"), Sp, V("d"))), Sp, D(0), Sp, Eq, Sp, Minus, Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, V("n"), Sp, Minus, Sp, D(1))), Sp, Cdot, Sp, Parenthesized(Seq(Qualified("n","factorial"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Slash, Sp, Sp, new Formula.Power(V("d"), Seq(V("n"), Sp, Minus, Sp, D(1))));

    private static Formula F45() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(GammaLower, Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Parenthesized(Seq(D(1), Sp, Le, Sp, V("M"))), Sp, To, Sp, Parenthesized(Seq(D(0), Sp, Lt, Sp, GammaLower)), Sp, To, Sp, V("IsProbabilityMeasure"), Sp, Parenthesized(Seq(V("law"), Sp, V("M"), Sp, GammaLower)));

    private static Formula F46() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(GammaLower, Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("t"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Parenthesized(Seq(D(1), Sp, Le, Sp, V("M"))), Sp, To, Sp, Parenthesized(Seq(D(0), Sp, Lt, Sp, GammaLower)), Sp, To, Sp, V("Integrable"), Sp, Parenthesized(Seq(V("fun"), Sp, V("p"), Sp, Mapsto, Sp, Qualified("Real","exp"), Sp, Parenthesized(Seq(V("t"), Sp, Cdot, Sp, V("rescaledObservable"), Sp, V("M"), Sp, GammaLower, Sp, V("p"))))), Sp, Parenthesized(Seq(V("law"), Sp, V("M"), Sp, GammaLower)));

    private static Formula F47() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(GammaLower, Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Parenthesized(Seq(D(1), Sp, Le, Sp, V("M"))), Sp, To, Sp, Parenthesized(Seq(D(2), Sp, Le, Sp, V("n"))), Sp, To, Sp, Parenthesized(Seq(D(0), Sp, Lt, Sp, GammaLower)), Sp, To, Sp, V("kappa"), Sp, V("M"), Sp, V("n"), Sp, GammaLower, Sp, Eq, Sp, Sp, new Formula.Power(Parenthesized(Seq(Minus, Sp, Sp, new Formula.Power(new Formula.Power(GammaLower, Seq(Minus, D(1))), D(2)))), V("n")), Sp, Cdot, Sp, V("iteratedDeriv"), Sp, V("n"), Sp, Parenthesized(Seq(V("cgf"), Sp, Parenthesized(Seq(V("rescaledObservable"), Sp, V("M"), Sp, GammaLower)), Sp, Parenthesized(Seq(V("law"), Sp, V("M"), Sp, GammaLower)))), Sp, D(0));

    private static Formula F48() =>
        Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(GammaLower, Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(V("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Parenthesized(Seq(D(1), Sp, Le, Sp, V("M"))), Sp, To, Sp, Parenthesized(Seq(D(0), Sp, Lt, Sp, GammaLower)), Sp, To, Sp, V("iteratedDeriv"), Sp, Parenthesized(Seq(V("n"), Sp, Plus, Sp, D(1))), Sp, Parenthesized(Seq(V("cgf"), Sp, Parenthesized(Seq(V("rescaledObservable"), Sp, V("M"), Sp, GammaLower)), Sp, Parenthesized(Seq(V("law"), Sp, V("M"), Sp, GammaLower)))), Sp, D(0), Sp, Eq, Sp, Parenthesized(Seq(Int, Sp, V("p"), Sp, Comma, Sp, Sp, new Formula.Power(Parenthesized(Seq(V("rescaledObservable"), Sp, V("M"), Sp, GammaLower, Sp, V("p"))), Seq(V("n"), Sp, Plus, Sp, D(1))), Sp, V("d"), Sp, V("law"), Sp, V("M"), Sp, GammaLower)), Sp, Minus, Sp, Sum, Sp, V("i"), Sp, InMacro, Sp, V("range"), Sp, V("n"), Sp, Comma, Sp, Parenthesized(Seq(Qualified("n","choose"), Sp, V("i"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Sp, Cdot, Sp, V("iteratedDeriv"), Sp, Parenthesized(Seq(V("i"), Sp, Plus, Sp, D(1))), Sp, Parenthesized(Seq(V("cgf"), Sp, Parenthesized(Seq(V("rescaledObservable"), Sp, V("M"), Sp, GammaLower)), Sp, Parenthesized(Seq(V("law"), Sp, V("M"), Sp, GammaLower)))), Sp, D(0), Sp, Cdot, Sp, Parenthesized(Seq(Int, Sp, V("p"), Sp, Comma, Sp, Sp, new Formula.Power(Parenthesized(Seq(V("rescaledObservable"), Sp, V("M"), Sp, GammaLower, Sp, V("p"))), Seq(V("n"), Sp, Minus, Sp, V("i"))), Sp, V("d"), Sp, V("law"), Sp, V("M"), Sp, GammaLower)));

    private static Formula Published0() =>
        Seq(Seq(Forall, Sp, Parenthesized(Seq(V("d"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("R"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(V("deriv"), Sp, Parenthesized(Seq(V("inverseSlope"), Sp, V("d"))), Sp, Eq, Sp, V("fun"), Sp, V("t"), Sp, Mapsto, Sp, new Formula.Power(Parenthesized(V("d")), Seq(Minus, D(1))), Sp, Cdot, Sp, new Formula.Power(Parenthesized(Parenthesized(Seq(V("inverseSlope"), Sp, V("d"), Sp, V("t")))), D(2))))));
}

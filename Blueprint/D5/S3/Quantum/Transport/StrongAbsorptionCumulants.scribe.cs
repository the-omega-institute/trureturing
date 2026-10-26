using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Transport;

internal sealed class StrongAbsorptionCumulantsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "StrongAbsorptionCumulants for the strong-absorption cumulant expansion.",
        H("StrongAbsorptionCumulants"),
        Blocks(
            Paragraph(Text("Natural-number subtraction is truncated. Unmarked integrals use volume; real-number powers and division use the real field.")),
            Describe.Lean(DescribeId.Create("claim"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorptionCumulants.claim"),
                H("claim"), StatementSource.FromAuthor(Disp(Seq(V("claim"), Sp, Eq, Sp, Parenthesized(ClaimBody())))),
                AssessedProvenance.FromLiterature(Note()),
                Blocks(Paragraph(Text("Novaes, Section 5, p. 7: “we conjecture that, for n > 1,” followed by Eq. (58). Natural n ≥ 2 expresses n > 1. The two coefficients and the absolute remainder bound refer to every M ≥ 1. The constants may depend on M and n."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorptionCumulants.result"),
                H("result"), StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Note()),
                Blocks(Paragraph(Text("For every positive channel number and every cumulant order at least two, the normalized law has the two strong-absorption coefficients of Novaes, Eq. (58)."))), DescribeRole.Theorem, new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("novaes-2023-strong-absorption-cumulants"),
                    ResolutionKind.Proved)),
            Describe.Lean(DescribeId.Create("published-baseexpectation"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorptionCumulants.baseExpectation"),
                H("baseExpectation"), StatementSource.FromAuthor(Disp(Published0())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed formula relates the polynomial integrals and the normalized finite-channel measure."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("published-singlewmoment"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorptionCumulants.singleWMoment"),
                H("singleWMoment"), StatementSource.FromAuthor(Disp(Published1())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed formula relates the polynomial integrals and the normalized finite-channel measure."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("published-baseexpectation-add"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorptionCumulants.baseExpectation_add"),
                H("baseExpectation_add"), StatementSource.FromAuthor(Disp(Published2())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed formula relates the polynomial integrals and the normalized finite-channel measure."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("published-law-polynomial-integrable"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorptionCumulants.law_polynomial_integrable"),
                H("law_polynomial_integrable"), StatementSource.FromAuthor(Disp(Published3())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed formula relates the polynomial integrals and the normalized finite-channel measure."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("published-rescaled-pow-integrable"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorptionCumulants.rescaled_pow_integrable"),
                H("rescaled_pow_integrable"), StatementSource.FromAuthor(Disp(Published4())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed formula relates the polynomial integrals and the normalized finite-channel measure."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("published-singlewmoment-derivative"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorptionCumulants.singleWMoment_derivative"),
                H("singleWMoment_derivative"), StatementSource.FromAuthor(Disp(Published5())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed formula relates the polynomial integrals and the normalized finite-channel measure."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("published-rescaledmomentexpansion"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorptionCumulants.rescaledMomentExpansion"),
                H("rescaledMomentExpansion"), StatementSource.FromAuthor(Disp(Published6())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed formula relates the polynomial integrals and the normalized finite-channel measure."))), DescribeRole.Theorem)
        )));

    private static Formula CastM() => Parenthesized(Seq(V("M"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("R"))))));
    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static LibraryNoteRef Note() => LibraryNoteRef.Create("D5/L/StatisticalMechanics/novaes2023absorption");

    private static Formula ClaimBody() =>
        Seq(Forall, Sp, V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))), Sp, Comma, Sp, D(1), Sp, Le, Sp, V("M"), Sp, To, Sp, Forall, Sp, V("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("N"))), Sp, Comma, Sp, D(2), Sp, Le, Sp, V("n"), Sp, To, Sp, Exists, Sp, V("C"), Sp, new Formula.Subscript(GammaLower, D(0)), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))), Sp, Comma, Sp, D(0), Sp, Lt, Sp, new Formula.Subscript(GammaLower, D(0)), Sp, Land, Sp, Forall, Sp, GammaLower, Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))), Sp, Comma, Sp, new Formula.Subscript(GammaLower, D(0)), Sp, Le, Sp, GammaLower, Sp, To, Sp, Bar, Sp, Sp, new Formula.Power(Parenthesized(Seq(Minus, Sp, D(1), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), V("n")), Sp, Cdot, Sp, V("kappa"), Sp, V("M"), Sp, V("n"), Sp, GammaLower, Sp, Minus, Sp, Parenthesized(Seq(Parenthesized(Seq(V("n"), Sp, Minus, Sp, D(1))), Sp, Dot, Sp, V("factorial"), Sp, Slash, Sp, Parenthesized(Seq(new Formula.Power(Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Seq(D(2), Sp, Cdot, Sp, V("n"), Sp, Minus, Sp, D(2))), Sp, Cdot, Sp, Sp, new Formula.Power(GammaLower, Seq(D(2), Sp, Cdot, Sp, V("n"))))), Sp, Minus, Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, V("n"), Sp, Minus, Sp, D(1))), Sp, Cdot, Sp, V("n"), Sp, Cdot, Sp, Parenthesized(Seq(V("n"), Sp, Minus, Sp, D(1))), Sp, Dot, Sp, V("factorial"), Sp, Slash, Sp, Parenthesized(Seq(new Formula.Power(Parenthesized(Seq(V("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(V("R"))))), Seq(D(2), Sp, Cdot, Sp, V("n"), Sp, Minus, Sp, D(2))), Sp, Cdot, Sp, Sp, new Formula.Power(GammaLower, Seq(D(2), Sp, Cdot, Sp, V("n"), Sp, Plus, Sp, D(1))))))), Sp, Bar, Sp, Le, Sp, V("C"), Sp, Slash, Sp, Sp, new Formula.Power(GammaLower, Seq(D(2), Sp, Cdot, Sp, V("n"), Sp, Plus, Sp, D(2))));
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

    private static Formula Published0() =>
        Seq(Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("N"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(V("P"), Sp, Colon, Sp, Parenthesized(Seq(V("MvPolynomial"), Sp, Parenthesized(Seq(V("Sum"), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))))), Sp, Seq(Mathbb, Grp(V("R")))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(V("baseExpectation"), Sp, V("M"), Sp, V("P"), Sp, Eq, Sp, Parenthesized(Seq(Parenthesized(Seq(Int, Sp, V("p"), Sp, Comma, Sp, V("baseWeight"), Sp, V("M"), Sp, CastM(), Sp, V("p"), Sp, Cdot, Sp, V("eval"), Sp, Parenthesized(Seq(Qualified("Sum","elim"), Sp, V("p"), Sp, Dot, Sp, D(1), Sp, V("p"), Sp, Dot, Sp, D(2))), Sp, V("P"))), Sp, Slash, Sp, new Formula.Power(Parenthesized(Parenthesized(Seq(V("partition"), Sp, V("M"), Sp, CastM()))), D(2)))))))))));

    private static Formula Published1() =>
        Seq(Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("N"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(V("r"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("N"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(V("singleWMoment"), Sp, V("M"), Sp, V("r"), Sp, Eq, Sp, Parenthesized(Seq(Parenthesized(Seq(Int, Sp, V("x"), Sp, Comma, Sp, V("laguerreWeight"), Sp, V("M"), Sp, CastM(), Sp, V("x"), Sp, Cdot, Sp, Parenthesized(Seq(Qualified("Finset","univ","expect"), Sp, Parenthesized(Seq(Seq(V("fun"), Sp, V("i")), Sp, Mapsto, Sp, Parenthesized(new Formula.Power(Parenthesized(Seq(V("x"), Sp, V("i"))), D(2))))))), Sp, Cdot, Sp, new Formula.Power(Parenthesized(Parenthesized(Seq(Qualified("Finset","univ","expect"), Sp, V("x")))), V("r")))), Sp, Slash, Sp, V("partition"), Sp, V("M"), Sp, CastM())))))))));

    private static Formula Published2() =>
        Seq(Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("N"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Parenthesized(Parenthesized(Seq(D(1), Sp, Le, Sp, V("M")))), Sp, To, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(V("P"), Sp, Colon, Sp, Parenthesized(Seq(V("MvPolynomial"), Sp, Parenthesized(Seq(V("Sum"), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))))), Sp, Seq(Mathbb, Grp(V("R")))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(V("Q"), Sp, Colon, Sp, Parenthesized(Seq(V("MvPolynomial"), Sp, Parenthesized(Seq(V("Sum"), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))))), Sp, Seq(Mathbb, Grp(V("R")))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(V("baseExpectation"), Sp, V("M"), Sp, Parenthesized(Seq(V("P"), Sp, Plus, Sp, V("Q"))), Sp, Eq, Sp, V("baseExpectation"), Sp, V("M"), Sp, V("P"), Sp, Plus, Sp, V("baseExpectation"), Sp, V("M"), Sp, V("Q"))))))))))))));

    private static Formula Published3() =>
        Seq(Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("N"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Parenthesized(Parenthesized(Seq(D(1), Sp, Le, Sp, V("M")))), Sp, To, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(GammaLower, Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("R"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Parenthesized(Parenthesized(Seq(D(0), Sp, Lt, Sp, GammaLower))), Sp, To, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(V("P"), Sp, Colon, Sp, Parenthesized(Seq(V("MvPolynomial"), Sp, Parenthesized(Seq(V("Sum"), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))))), Sp, Seq(Mathbb, Grp(V("R")))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(V("Integrable"), Sp, Parenthesized(Seq(Seq(V("fun"), Sp, V("p")), Sp, Mapsto, Sp, Parenthesized(Seq(V("eval"), Sp, Parenthesized(Seq(Qualified("Sum","elim"), Sp, V("p"), Sp, Dot, Sp, D(1), Sp, V("p"), Sp, Dot, Sp, D(2))), Sp, V("P"))))), Sp, Parenthesized(Seq(V("law"), Sp, V("M"), Sp, GammaLower))))))))))))))))));

    private static Formula Published4() =>
        Seq(Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("N"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Parenthesized(Parenthesized(Seq(D(1), Sp, Le, Sp, V("M")))), Sp, To, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(GammaLower, Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("R"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Parenthesized(Parenthesized(Seq(D(0), Sp, Lt, Sp, GammaLower))), Sp, To, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(V("r"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("N"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(V("Integrable"), Sp, Parenthesized(Seq(Seq(V("fun"), Sp, V("p")), Sp, Mapsto, Sp, Parenthesized(new Formula.Power(Parenthesized(Seq(V("rescaledObservable"), Sp, V("M"), Sp, GammaLower, Sp, V("p"))), V("r"))))), Sp, Parenthesized(Seq(V("law"), Sp, V("M"), Sp, GammaLower))))))))))))))))));

    private static Formula Published5() =>
        Seq(Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("N"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Parenthesized(Parenthesized(Seq(D(1), Sp, Le, Sp, V("M")))), Sp, To, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(V("r"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("N"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(V("singleWMoment"), Sp, V("M"), Sp, V("r"), Sp, Eq, Sp, V("iteratedDeriv"), Sp, V("r"), Sp, Parenthesized(Seq(V("laguerreHw"), Sp, V("M"))), Sp, D(0)))))))))));

    private static Formula Published6() =>
        Seq(Seq(Seq(Forall, Sp, V("M")), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Parenthesized(Seq(Parenthesized(Seq(D(1), Sp, Le, Sp, V("M"))), Sp, To, Sp, Parenthesized(Seq(Seq(Seq(Forall, Sp, V("r")), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("N"))))), Sp, Comma, Sp, Parenthesized(Seq(V("FirstOrder"), Sp, Parenthesized(Parenthesized(Seq(Seq(V("fun"), Sp, GammaLower), Sp, Mapsto, Sp, Parenthesized(Seq(Qualified("ProbabilityTheory","moment"), Sp, Parenthesized(Seq(V("rescaledObservable"), Sp, V("M"), Sp, GammaLower)), Sp, V("r"), Sp, Parenthesized(Seq(V("law"), Sp, V("M"), Sp, GammaLower))))))), Sp, Parenthesized(Seq(V("expJet"), Sp, Parenthesized(Seq(V("gammaCGF"), Sp, Parenthesized(new Formula.Power(Parenthesized(Parenthesized(Seq(V("M"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("R"))))))), D(2))))), Sp, V("r"))), Sp, Parenthesized(Seq(V("correctionJet"), Sp, Parenthesized(Seq(V("gammaCGF"), Sp, Parenthesized(new Formula.Power(Parenthesized(Parenthesized(Seq(V("M"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("R"))))))), D(2))))), Sp, Parenthesized(Seq(V("correctionCGF"), Sp, Parenthesized(new Formula.Power(Parenthesized(Parenthesized(Seq(V("M"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("R"))))))), D(2))))), Sp, V("r"))))))))));
}

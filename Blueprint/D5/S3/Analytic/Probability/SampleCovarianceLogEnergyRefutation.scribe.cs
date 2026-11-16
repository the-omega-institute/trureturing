using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Probability;

internal sealed class SampleCovarianceLogEnergyRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Analytic/Probability/SampleCovarianceLogEnergyRefutation";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/chafaidadounyoussef2024logenergy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "SampleCovarianceLogEnergyRefutation mathematical statements.",
        H("Sample Covariance Log Energy Refutation"),
        Blocks(
            Describe.Lean(DescribeId.Create("cdy-samplecovariancelogenergyrefutation-claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("claim"),
                StatementSource.FromAuthor(Disp(Seq(F.Id("claim"), Sp, Iff, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Mu, Sp, Colon, Sp, F.Id("Measure"), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Comma, Sp, F.Id("EntryLaw"), Sp, Mu, Sp, To, Sp, Parenthesized(Seq(Forall, Sp, F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, F.Id("penalizedEnergy"), Sp, Parenthesized(Seq(F.Id("meanSpectralMeasure"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Plus, Sp, D(2))), Sp, Parenthesized(Seq(F.Id("by"), Sp, F.Id("omega"))), Sp, Mu)), Sp, Leq, Sp, F.Id("penalizedEnergy"), Sp, Parenthesized(Seq(F.Id("meanSpectralMeasure"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Plus, Sp, D(1))), Sp, Parenthesized(Seq(F.Id("by"), Sp, F.Id("omega"))), Sp, Mu)))), Sp, Land, Sp, F.Id("Tendsto"), Sp, Parenthesized(Seq(F.Id("fun"), Sp, F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, Mapsto, Sp, F.Id("penalizedEnergy"), Sp, Parenthesized(Seq(F.Id("meanSpectralMeasure"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Plus, Sp, D(1))), Sp, Parenthesized(Seq(F.Id("by"), Sp, F.Id("omega"))), Sp, Mu)))), Sp, F.Id("atTop"), Sp, Parenthesized(Seq(F.Id("nhds"), Sp, Parenthesized(Seq(F.Id("penalizedEnergy"), Sp, F.Id("marchenkoPastur")))))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Let Xₙ ≔ (ξᵢⱼ)₁≤ᵢ,ⱼ≤ₙ be an n×n random matrix whose entries are i.i.d. centered complex random variables of unit variance, and let μₙ ≔ "), Math(new Formula.Subscript(Mu, Seq(new Formula.Fraction(D(1), F.Id("n")), new Formula.Subscript(F.Id("X"), F.Id("n")), new Formula.Power(new Formula.Subscript(F.Id("X"), F.Id("n")), Star)))), Text(" be the corresponding spectral distribution. Is it true that ℰ⁽¹⁾(𝔼μₙ) ↘ ℰ⁽¹⁾(μMP)? PDF p. 4. The law is a measure on Complex; n ranges over Nat and the positive dimensions are n+1 and n+2. The decreasing arrow denotes consecutive nonincrease and convergence. Eigenvalues are counted with multiplicity, and energy is evaluated after taking the mean measure."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cdy-samplecovariancelogenergyrefutation-result"),
                DeclarationHandle.Create(Module + ".result"),
                H("result"),
                StatementSource.FromAuthor(Disp(Seq(Neg, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Mu, Sp, Colon, Sp, F.Id("Measure"), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Comma, Sp, F.Id("EntryLaw"), Sp, Mu, Sp, To, Sp, Parenthesized(Seq(Forall, Sp, F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, F.Id("penalizedEnergy"), Sp, Parenthesized(Seq(F.Id("meanSpectralMeasure"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Plus, Sp, D(2))), Sp, Parenthesized(Seq(F.Id("by"), Sp, F.Id("omega"))), Sp, Mu)), Sp, Leq, Sp, F.Id("penalizedEnergy"), Sp, Parenthesized(Seq(F.Id("meanSpectralMeasure"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Plus, Sp, D(1))), Sp, Parenthesized(Seq(F.Id("by"), Sp, F.Id("omega"))), Sp, Mu)))), Sp, Land, Sp, F.Id("Tendsto"), Sp, Parenthesized(Seq(F.Id("fun"), Sp, F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, Mapsto, Sp, F.Id("penalizedEnergy"), Sp, Parenthesized(Seq(F.Id("meanSpectralMeasure"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Plus, Sp, D(1))), Sp, Parenthesized(Seq(F.Id("by"), Sp, F.Id("omega"))), Sp, Mu)))), Sp, F.Id("atTop"), Sp, Parenthesized(Seq(F.Id("nhds"), Sp, Parenthesized(Seq(F.Id("penalizedEnergy"), Sp, F.Id("marchenkoPastur")))))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("result satisfies the displayed statement."))), DescribeRole.Theorem, openProblemResolutionClaim: new OpenProblemResolutionClaim(ProblemSlugRef.Create("op-cdy2212q13"), ResolutionKind.Refuted)))));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}

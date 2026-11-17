using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.SpectralGap;

internal sealed class WeightedConvexPotentialRefutationDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Asymptotics/ahrami2026weightedgap");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted Dirichlet eigenvalues and a fixed affine spectral gap comparison.",
        H("WeightedConvexPotentialRefutation"), Blocks(
            Describe.Lean(DescribeId.Create("weightedconvexpotentialrefutation-def-fixedpotential"),
                DeclarationHandle.Create("D5/S3/Analytic/SpectralGap/WeightedConvexPotentialRefutation.fixedPotential"), H("fixedPotential"),
                StatementSource.FromAuthor(Disp(Statement0())), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The potential is the affine function with slope one over one hundred and zero intercept."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("weightedconvexpotentialrefutation-def-fixedweight"),
                DeclarationHandle.Create("D5/S3/Analytic/SpectralGap/WeightedConvexPotentialRefutation.fixedWeight"), H("fixedWeight"),
                StatementSource.FromAuthor(Disp(Statement1())), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The weight is affine with slope one over one hundred and equals one at the interval midpoint."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("weightedconvexpotentialrefutation-theorem-result"),
                DeclarationHandle.Create("D5/S3/Analytic/SpectralGap/WeightedConvexPotentialRefutation.result"), H("result"),
                StatementSource.FromAuthor(Disp(Statement2())), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Open Problem 3.3, page 10: “Let w be a positive concave weight on [0,π]. Does the constant potential minimzer the fundamental spectral gap over the class of convex potentials. Equivalently,” “Γ[V,w]≥Γ[0,w]” “for every convex potential V.” The index zero is λ₁ and index one is λ₂. Both spectra are asserted to exist; the comparison quantifies over their min-max values. If both specified min-max spectra exist, fixedPotential and fixedWeight force a negative gap difference. A uniform geometric coefficient estimate controls the shooting determinant, and zero separation identifies its first two min-max values."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("op-ahrami2605gap"),
                    ResolutionKind.Refuted)))));

    private static Formula Statement0() =>
        Seq(Forall, Sp, Parenthesized(Seq(FormulaDsl.Id("x"), Colon, Sp, Seq(Mathbb, Grp(FormulaDsl.Id("R"))))), Comma, Sp, Seq(Seq(FormulaDsl.Id("fixedPotential"), Sp, FormulaDsl.Id("x")), Sp, Eq, Sp, Parenthesized(Seq(FormulaDsl.Id("x"), Sp, Slash, Sp, D(1,0,0)))));

    private static Formula Statement1() =>
        Seq(Forall, Sp, Parenthesized(Seq(FormulaDsl.Id("x"), Colon, Sp, Seq(Mathbb, Grp(FormulaDsl.Id("R"))))), Comma, Sp, Seq(Seq(FormulaDsl.Id("fixedWeight"), Sp, FormulaDsl.Id("x")), Sp, Eq, Sp, Parenthesized(Seq(D(1), Sp, Plus, Sp, Parenthesized(Seq(FormulaDsl.Id("x"), Sp, Minus, Sp, FormulaDsl.Id("Real"), Sp, Dot, Sp, FormulaDsl.Id("pi"), Sp, Slash, Sp, D(2))), Sp, Slash, Sp, D(1,0,0)))));

    private static Formula Statement2() =>
        new Formula.Not(Parenthesized(ClaimBody()));

    private static Formula ClaimBody() =>
        Seq(Forall, Sp, Parenthesized(Seq(FormulaDsl.Id("M"), Sp, Colon, Sp, FormulaDsl.Id("WithTop"), Sp, Seq(Mathbb, Grp(FormulaDsl.Id("R"))))), Sp, Parenthesized(Seq(FormulaDsl.Id("Nlo"), Sp, FormulaDsl.Id("Nhi"), Sp, Colon, Sp, Seq(Mathbb, Grp(FormulaDsl.Id("R"))))), Sp, Parenthesized(Seq(FormulaDsl.Id("V"), Sp, FormulaDsl.Id("w"), Sp, Colon, Sp, Seq(Mathbb, Grp(FormulaDsl.Id("R"))), Sp, To, Sp, Seq(Mathbb, Grp(FormulaDsl.Id("R"))))), Sp, Comma, Sp, Parenthesized(Seq(D(1), Sp, Colon, Sp, FormulaDsl.Id("WithTop"), Sp, Seq(Mathbb, Grp(FormulaDsl.Id("R"))))), Sp, Lt, Sp, FormulaDsl.Id("M"), Sp, To, Sp, D(0), Sp, Lt, Sp, FormulaDsl.Id("Nlo"), Sp, To, Sp, D(0), Sp, Lt, Sp, FormulaDsl.Id("Nhi"), Sp, To, Sp, FormulaDsl.Id("potentialClass"), Sp, FormulaDsl.Id("M"), Sp, FormulaDsl.Id("V"), Sp, To, Sp, FormulaDsl.Id("weightClass"), Sp, FormulaDsl.Id("Nlo"), Sp, FormulaDsl.Id("Nhi"), Sp, FormulaDsl.Id("w"), Sp, To, Sp, Parenthesized(Seq(Parenthesized(Seq(Exists, Sp, FormulaDsl.Id("e"), Sp, Colon, Sp, Seq(Mathbb, Grp(FormulaDsl.Id("N"))), Sp, To, Sp, Seq(Mathbb, Grp(FormulaDsl.Id("R"))), Sp, Comma, Sp, FormulaDsl.Id("isSpectrum"), Sp, FormulaDsl.Id("V"), Sp, FormulaDsl.Id("w"), Sp, FormulaDsl.Id("e"))), Sp, Land, Sp, Parenthesized(Seq(Exists, Sp, FormulaDsl.Id("e0"), Sp, Colon, Sp, Seq(Mathbb, Grp(FormulaDsl.Id("N"))), Sp, To, Sp, Seq(Mathbb, Grp(FormulaDsl.Id("R"))), Sp, Comma, Sp, FormulaDsl.Id("isSpectrum"), Sp, Parenthesized(Seq(FormulaDsl.Id("Function"), Sp, Dot, Sp, FormulaDsl.Id("const"), Sp, Seq(Mathbb, Grp(FormulaDsl.Id("R"))), Sp, D(0))), Sp, FormulaDsl.Id("w"), Sp, FormulaDsl.Id("e0"))))), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(FormulaDsl.Id("e"), Sp, FormulaDsl.Id("e0"), Sp, Colon, Sp, Seq(Mathbb, Grp(FormulaDsl.Id("N"))), Sp, To, Sp, Seq(Mathbb, Grp(FormulaDsl.Id("R"))))), Sp, Comma, Sp, FormulaDsl.Id("isSpectrum"), Sp, FormulaDsl.Id("V"), Sp, FormulaDsl.Id("w"), Sp, FormulaDsl.Id("e"), Sp, To, Sp, FormulaDsl.Id("isSpectrum"), Sp, Parenthesized(Seq(FormulaDsl.Id("Function"), Sp, Dot, Sp, FormulaDsl.Id("const"), Sp, Seq(Mathbb, Grp(FormulaDsl.Id("R"))), Sp, D(0))), Sp, FormulaDsl.Id("w"), Sp, FormulaDsl.Id("e0"), Sp, To, Sp, FormulaDsl.Id("gap"), Sp, FormulaDsl.Id("e0"), Sp, Leq, Sp, FormulaDsl.Id("gap"), Sp, FormulaDsl.Id("e"))));

    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
}

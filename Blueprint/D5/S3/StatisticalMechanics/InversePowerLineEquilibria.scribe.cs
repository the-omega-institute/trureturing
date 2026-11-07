using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class InversePowerLineEquilibriaDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/StatisticalMechanics/InversePowerLineEquilibria";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Asymptotics/ferudun2026inversepowerline");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Inverse-power equilibrium rigidity on the real line.",
        H("Inverse-power line: Equilibria"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("claim"),
                StatementSource.FromAuthor(Disp(Parenthesized(Seq(Seq(Operatorname, Grp(F.Id("claim"))), Thin, Iff, Thin, Forall, Thin, F.Id("s"), Thin, Colon, Thin, Seq(Mathbb, Grp(F.Id("R"))), Thin, Comma, Thin, D(2), Thin, Lt, Thin, F.Id("s"), Thin, To, Thin, Parenthesized(Seq(Exists, Thin, F.Id("X"), Thin, Colon, Thin, Seq(Operatorname, Grp(F.Id("Set"))), Thin, Seq(Mathbb, Grp(F.Id("R"))), Thin, Comma, Thin, Seq(Operatorname, Grp(F.Id("IsSEquilibrium"))), Thin, F.Id("s"), Thin, F.Id("X"))), Thin, Land, Thin, Parenthesized(Seq(Forall, Thin, F.Id("X"), Thin, Colon, Thin, Seq(Operatorname, Grp(F.Id("Set"))), Thin, Seq(Mathbb, Grp(F.Id("R"))), Thin, Comma, Thin, Seq(Operatorname, Grp(F.Id("IsSEquilibrium"))), Thin, F.Id("s"), Thin, F.Id("X"), Thin, Iff, Thin, Exists, Thin, Alpha, Thin, Colon, Thin, Seq(Mathbb, Grp(F.Id("R"))), Thin, Comma, Thin, D(0), Thin, Lt, Thin, Alpha, Thin, Land, Thin, Parenthesized(Seq(Exists, Thin, Beta, Thin, Colon, Thin, Seq(Mathbb, Grp(F.Id("R"))), Thin, Comma, Thin, F.Id("X"), Thin, Eq, Thin, Seq(Operatorname, Grp(F.Id("arithmeticProgression"))), Thin, Alpha, Thin, Beta)))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Remark 5.3 (p. 8): “We make no claim for s > 2; whether the conclusion of Theorem 1.2 holds there remains open.” The proposition extends the whole classification to every real exponent s > 2, including existence and the converse for every set X. It assumes neither an upper gap bound nor a positive lower gap bound."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("result"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Thin, F.Id("s"), Thin, Colon, Thin, Seq(Mathbb, Grp(F.Id("R"))), Thin, Comma, Thin, D(2), Thin, Lt, Thin, F.Id("s"), Thin, To, Thin, Parenthesized(Seq(Exists, Thin, F.Id("X"), Thin, Colon, Thin, Seq(Operatorname, Grp(F.Id("Set"))), Thin, Seq(Mathbb, Grp(F.Id("R"))), Thin, Comma, Thin, Seq(Operatorname, Grp(F.Id("IsSEquilibrium"))), Thin, F.Id("s"), Thin, F.Id("X"))), Thin, Land, Thin, Parenthesized(Seq(Forall, Thin, F.Id("X"), Thin, Colon, Thin, Seq(Operatorname, Grp(F.Id("Set"))), Thin, Seq(Mathbb, Grp(F.Id("R"))), Thin, Comma, Thin, Seq(Operatorname, Grp(F.Id("IsSEquilibrium"))), Thin, F.Id("s"), Thin, F.Id("X"), Thin, Iff, Thin, Exists, Thin, Alpha, Thin, Colon, Thin, Seq(Mathbb, Grp(F.Id("R"))), Thin, Comma, Thin, D(0), Thin, Lt, Thin, Alpha, Thin, Land, Thin, Parenthesized(Seq(Exists, Thin, Beta, Thin, Colon, Thin, Seq(Mathbb, Grp(F.Id("R"))), Thin, Comma, Thin, F.Id("X"), Thin, Eq, Thin, Seq(Operatorname, Grp(F.Id("arithmeticProgression"))), Thin, Alpha, Thin, Beta))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every real s > 2, an equilibrium exists and its point set is exactly an affine image of the integers with positive scale. Reciprocal consecutive gaps are positive harmonic functions for the transformed conductances. On each proper positive sublevel, interval packing and second-moment estimates produce finitely supported functions of arbitrarily small induced energy. A strict exterior harmonic flux contradicts this energy bound unless the reciprocal gaps are constant. Constant gaps reconstruct the progression, and the absolutely convergent p-series gives the converse."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("op-ferudun2610s2"),
                    ResolutionKind.Proved)))));

    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
}

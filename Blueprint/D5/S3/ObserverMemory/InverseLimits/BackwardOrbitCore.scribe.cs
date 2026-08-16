using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.InverseLimits;

internal sealed class BackwardOrbitCoreDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Infinite backward trajectories of a finite self-map are exactly its periodic core.",
        H("Backward Orbit Core"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("backward-orbits-are-the-periodic-core"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/InverseLimits/BackwardOrbitCore."
                    + "backward_orbit_eval_zero_bijective"),
                H("Backward orbits are the periodic core"),
                StatementSource.FromAuthor(BackwardOrbitCoreFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let Y be a finite carrier and F a self-map. A backward orbit is a "
                            + "sequence x indexed by the natural numbers with F(x(n+1))=x(n). "
                            + "Its coordinate-zero evaluation lands in the positive-period "
                            + "points of F.")),
                    Paragraph(Text(
                        "Coordinate-zero evaluation is bijective. Surjectivity follows because "
                            + "F is a bijection on its periodic core, so every periodic point has "
                            + "a unique infinite chain of periodic predecessors. Injectivity uses "
                            + "a finite pigeonhole collision to show that every coordinate of any "
                            + "backward orbit is periodic, where F is injective.")),
                    Paragraph(Text(
                        "Pinned Mathlib and Loogle supplied Function.bijOn_periodicPts, "
                            + "Function.IsPeriodicPt.eq_of_apply_eq, and the finite pigeonhole "
                            + "theorem used by the proof. Pinned-Mathlib, repository, and GitHub "
                            + "Lean-source searches found no full inverse-limit equivalence. "
                            + "LeanSearch's API endpoint returned HTTP 404 and supplied no search "
                            + "conclusion."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula BackwardOrbits() =>
        Apply(F.Id("B"), F.Id("F"));

    private static Formula PeriodicCore() =>
        Apply(F.Id("P"), F.Id("F"));

    private static Formula BackwardOrbitCoreFormula()
    {
        Formula carrier = F.Id("Y");
        Formula evaluation = Seq(F.Id("ev"), Underscore, Grp(D(0)));
        Formula finite = Seq(
            OpenBracket, Operatorname, Grp(F.Id("Finite")), Sp, carrier, CloseBracket);
        Formula bijective = Seq(Operatorname, Grp(F.Id("Bijective")), Open,
            evaluation, Colon, Sp, BackwardOrbits(), Sp, To, Sp, PeriodicCore(), Close);
        return Disp(Seq(
            Forall, Sp, carrier, Comma, Sp, finite, Comma, Esc,
            F.Id("F"), Colon, Sp, carrier, Sp, To, Sp, carrier, Comma, Esc,
            bijective, Dot));
    }
}

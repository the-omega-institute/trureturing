using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class CompletedZetaMellinReconstructionDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef CoffeyXi =
        LibraryNoteRef.Create("D5/L/Zeros/coffey2007theta");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Analytic/CompletedZetaMellinReconstruction",
            "Completed zeta is reconstructed from its symmetric theta-tail Mellin integral."),
        H("Mellin Reconstruction of the Completed Zeta"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("completed-zeta-is-reconstructed-from-the-symmetric-theta-tail"),
                H("Completed zeta is reconstructed from the symmetric theta tail"),
                LeanTheorem(
                    "D5/S3/Analytic/CompletedZetaMellinReconstruction.completed_zeta_mellin_reconstruction"),
                Disp(Seq(F.Text, Grp(F.Id("Let"), Sp), Sp, Theta, Open, F.Id("t"), Close, Eq, Theta, Underscore, Grp(Mathrm, Grp(F.Id("even"))), Open, D(0), Comma, F.Id("t"), Close, Comma, Esc, Omega, Eq, Frac, Grp(Theta, Minus, D(1)), Grp(D(2)), Comma, Esc, F.Id("M"), Open, F.Id("s"), Close, Eq, Int, Underscore, Grp(D(1)), Caret, Grp(Infty), Omega, Open, F.Id("t"), Close, Thin, Left, Open, F.Id("t"), Caret, Grp(F.Id("s"), Slash, D(2)), Plus, F.Id("t"), Caret, Grp(Open, D(1), Minus, F.Id("s"), Close, Slash, D(2)), Right, Close, Thin, Frac, Grp(F.Id("dt")), Grp(F.Id("t")), Dot, Esc, F.Text, Grp(F.Id("Then"), Sp), Sp, Open, Forall, Sp, F.Id("s"), Comma, Esc, Re, Sp, F.Id("s"), Gt, D(1), Sp, Rightarrow, Sp, Lambda, Open, F.Id("s"), Close, Eq, Pi, Caret, Grp(Minus, F.Id("s"), Slash, D(2)), Thin, Gamma, Open, Frac, Grp(F.Id("s")), Grp(D(2)), Close, Thin, Zeta, Open, F.Id("s"), Close, Close, Sp, Land, Sp, Open, Forall, Sp, F.Id("s"), Comma, Esc, Lambda, Open, F.Id("s"), Close, Eq, F.Id("M"), Open, F.Id("s"), Close, Minus, Frac, Grp(D(1)), Grp(F.Id("s")), Minus, Frac, Grp(D(1)), Grp(D(1), Minus, F.Id("s")), Close, Sp, Land, Sp, Operatorname, Grp(F.Id("Differentiable")), Underscore, Grp(Mathbb, Grp(F.Id("C"))), Open, F.Id("M"), Close, Sp, Land, Sp, Open, Forall, Sp, F.Id("s"), Comma, Esc, F.Id("M"), Open, D(1), Minus, F.Id("s"), Close, Eq, F.Id("M"), Open, F.Id("s"), Close, Close, Sp, Land, Sp, Open, Forall, Sp, F.Id("s"), Comma, Esc, F.Id("s"), Neq, Sp, D(0), Sp, Land, Sp, F.Id("s"), Neq, Sp, D(1), Sp, Rightarrow, Sp, Operatorname, Grp(F.Id("DifferentiableAt")), Underscore, Grp(Mathbb, Grp(F.Id("C"))), Open, Lambda, Comma, F.Id("s"), Close, Close, Sp, Land, Sp, Lim, Underscore, Grp(F.Id("s"), To, Sp, D(0)), F.Id("s"), Thin, Lambda, Open, F.Id("s"), Close, Eq, Minus, D(1), Sp, Land, Sp, Lim, Underscore, Grp(F.Id("s"), To, Sp, D(1)), Open, F.Id("s"), Minus, D(1), Close, Thin, Lambda, Open, F.Id("s"), Close, Eq, D(1), Sp, Land, Sp, Open, Forall, Sp, F.Id("s"), Comma, Esc, Xi, Open, D(1), Minus, F.Id("s"), Close, Eq, Xi, Open, F.Id("s"), Close, Close)),
                DescribeProvenance.LiteratureAttested(CoffeyXi),
                Blocks(Paragraph(Text(
                    "With the theta kernel supplied by mathlib's even Hurwitz kernel at parameter zero, its "
                    + "halved tail omega, and the literal Mellin-type integral M over the ray beyond one, the "
                    + "theorem conjoins seven clauses: the Euler-factor identification of the completed reading "
                    + "on the convergence half-plane; the reconstruction identity expressing the completed "
                    + "reading as M minus the two simple pole terms at zero and one; entirety of M; the "
                    + "reflection symmetry of M under s to one minus s; differentiability of the completed "
                    + "reading away from the two exceptional points; the explicit residue ledger sending s "
                    + "times the completed reading to minus one at zero and s minus one times it to one at "
                    + "one; and the xi reflection equation. The integral M is stated as a genuine measure-"
                    + "theoretic integral rather than an alias of the pole-removed completion; the proof "
                    + "identifies it with that completion by splitting the modified weak-functional-equation "
                    + "profile at one and algebraizing the inversion substitution through the unconditional "
                    + "pointwise Mellin composition identities. The theorem introduces no public concept "
                    + "beyond its selector and supplies the reconstruction bridge between the theta tail and "
                    + "the pole ledger that the zero-symmetry route below O-6 consumes.")))
            )),
[
                    DocumentEdge.TruthAnchor.Create(
                        LeanDeclarationRef.Create("D5/S3/Analytic/CompletedZetaMellinReconstruction.completed_zeta_mellin_reconstruction")),
                    DocumentEdge.Dependency.Create(
                        GidRef.Create("D5/S3/Zeros/CompletedZeta")),
                ]));
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics.SymmetricHypercubeWalk;

internal sealed class WeakLimitsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/WeakLimits.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Hamming/ide2026scaling");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The fixed-order shifted moments determine convergence of probability laws on [0,1].",
        H("Shifted moments and weak convergence on the unit interval"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exists-weaklimit-iff-shiftedmoments-converge"),
                DeclarationHandle.Create(Prefix + "exists_weakLimit_iff_shiftedMoments_converge"),
                H("Existence of a weak limit"),
                StatementSource.FromAuthor(Disp(Seq(Open, Exists, Sp, Pi, Comma, Sp, Mu, Underscore, Grp(F.Id("i")), Sp, To, Sp, Pi, Close, Sp, Iff, Sp, Forall, Sp, F.Id("k"), Gt, D(0), Comma, Sp, Exists, Sp, F.Id("m"), Comma, Sp, F.Id("M"), Underscore, Grp(F.Id("k")), Open, Mu, Underscore, Grp(F.Id("i")), Close, Sp, To, Sp, F.Id("m")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For a family of probability measures on [0,1] along a filter, M_k is the integral of (1−2x)^k. Stone–Weierstrass gives density of polynomials in the shifted coordinate. The moment map into the product of real lines is a continuous closed embedding by compactness and moment separation. Along a nontrivial filter, coordinate convergence therefore gives a weak limit, and weak convergence gives convergence of each coordinate. Along the bottom filter, every convergence statement holds and a Dirac probability at 0 witnesses existence."))),
                DescribeRole.Theorem))));
}

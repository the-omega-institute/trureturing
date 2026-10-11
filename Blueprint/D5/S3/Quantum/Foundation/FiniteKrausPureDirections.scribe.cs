using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class FiniteKrausPureDirectionsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite pure channel histories lift to one nondegenerate linear orbit.",
        H("Kraus pure directions"),
        Blocks(
            Paragraph(Text(
                "For a nonzero complex vector v, directionState(v) is the pure density state "
                + "of v divided by the square root of the sum of the coordinate squared moduli. "
                + "Its matrix is the outer product of v and its conjugate, divided by that sum. "
                + "This normalization uses the Euclidean mass, independently of the default "
                + "norm on a function space. K denotes the canonical finite Kraus table of the channel.")),
            Describe.Lean(
                DescribeId.Create("map-direction-state"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Foundation/FiniteKrausPureDirections.map_directionState_of_collinear"),
                H("Exact normalized transition"),
                StatementSource.FromAuthor(Transition()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every dimension d, CPTP channel C, nonzero vectors v and w, and "
                    + "Kraus coefficient tuple mu, if every K(u)v equals mu(u)w, then C sends "
                    + "directionState(v) exactly to directionState(w). The input and output "
                    + "vectors need not have equal mass. Trace preservation determines the "
                    + "necessary scalar normalization."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("linear-lift-pure-prefix"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Foundation/FiniteKrausPureDirections.linear_lift_of_pure_prefix"),
                H("One linear map for the whole finite history"),
                StatementSource.FromAuthor(Lift()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For arbitrary d and N, let rho be a sequence of density states for "
                        + "a fixed CPTP channel C. Suppose rho(n+1)=C(rho(n)) for n<N, "
                        + "and rho(n) is pure for n at most N. There exist an endomorphism A "
                        + "and a nonzero x representing rho(0), such that A^n x is nonzero "
                        + "for n at most N and every Kraus image of A^n x is a scalar multiple "
                        + "of A^(n+1)x for n<N. A is one linear combination of the original Kraus table.")),
                    Paragraph(Text(
                        "A rectangular matrix with the Kraus images as columns has a rank-one "
                        + "Gram matrix. Compressing away the output direction and using Gram "
                        + "zero detection makes each column collinear with that direction. "
                        + "The normalized coefficient rows define finitely many nonzero linear "
                        + "functionals. The upstream simultaneous nonvanishing theorem chooses "
                        + "one coefficient vector for all of them; a finite induction then "
                        + "supplies the nonzero linear orbit.")),
                    Paragraph(Text(
                        "The finite-prefix lift does not assert that the linear orbit is "
                        + "nonzero or Kraus-collinear after N. Extending those relations requires "
                        + "the invariant tail, coefficient blocks, and word-space potential argument."))),
                DescribeRole.Theorem))));

    private static Formula Transition() => Disp(Seq(
        Forall, Sp, F.Id("dCvwm"), Comma, Sp,
        Call("CollinearKraus", F.Id("dCvwm")), Sp, Rightarrow, Sp,
        Call("mapState", F.Id("C"), Call("directionState", F.Id("v"))),
        Eq, Call("directionState", F.Id("w"))));

    private static Formula Lift() => Disp(Seq(
        Forall, Sp, F.Id("dNCr"), Comma, Sp,
        Call("PureHistory", F.Id("dNCr")), Sp, Rightarrow, Sp,
        Exists, Sp, F.Id("Ax"), Comma, Sp,
        Call("NonzeroKrausLift", F.Id("dNCrAx"))));
}

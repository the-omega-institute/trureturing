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

    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, type, Comma, Sp, body);

    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, F.Id(name), Colon, type, Comma, Sp, body);

    private static Formula NatType() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Vec() => Call("Vector", F.Id("d"));
    private static Formula State() => Call("DensityState", F.Id("d"));
    private static Formula Index() => Call("KrausIndex", F.Id("d"));
    private static Formula Arrow(Formula a, Formula b) => Seq(a, To, b);
    private static Formula P(Formula v) => Call("directionState", v);
    private static Formula R(Formula n) => Seq(F.Id("r"), Open, n, Close);
    private static Formula Orbit(Formula n) => Seq(F.Id("A"), Caret, Grp(n), F.Id("x"));
    private static Formula Nonzero(Formula x) => Seq(x, Neq, Sp, D(0));
    private static Formula And(params Formula[] items) => Join(Seq(Sp, Land, Sp), items);

    private static Formula Join(Formula separator, params Formula[] items)
    {
        var result = new System.Collections.Generic.List<Formula>();
        foreach (var item in items)
        {
            if (result.Count != 0) result.Add(separator);
            result.Add(item);
        }
        return Seq([.. result]);
    }

    private static Formula Transition()
    {
        Formula u = F.Id("u"), v = F.Id("v"), w = F.Id("w");
        return Disp(All("d", NatType(),
            All("C", Call("QuantumChannel", F.Id("d")),
            All("v", Vec(), All("w", Vec(),
            All("m", Arrow(Index(), Seq(Mathbb, Grp(F.Id("C")))), Seq(
                Open, And(Nonzero(v), Nonzero(w),
                    All("u", Index(), Seq(Call("Kraus", F.Id("C"), u), v,
                        Eq, F.Id("m"), Open, u, Close, w))), Close,
                Sp, Rightarrow, Sp,
                Call("mapState", F.Id("C"), P(v)), Eq, P(w))))))));
    }

    private static Formula Lift()
    {
        Formula n = F.Id("n"), u = F.Id("u"), x = F.Id("x");
        Formula successor = Seq(n, Plus, D(1));
        Formula nonzeroPrefix = All("n", NatType(), Seq(n, Le, F.Id("N"),
            Sp, Rightarrow, Sp, Nonzero(Orbit(n))));
        Formula collinearPrefix = All("n", NatType(), Seq(n, Lt, F.Id("N"),
            Sp, Rightarrow, Sp, Ex("m", Arrow(Index(), Seq(Mathbb, Grp(F.Id("C")))),
                All("u", Index(), Seq(Call("Kraus", F.Id("C"), u), Orbit(n),
                    Eq, F.Id("m"), Open, u, Close, Orbit(successor))))));
        return Disp(All("d", NatType(), All("N", NatType(),
            All("C", Call("QuantumChannel", F.Id("d")),
            All("r", Arrow(NatType(), State()), Seq(
                Open, And(
                    All("n", NatType(), Seq(n, Lt, F.Id("N"), Sp, Rightarrow, Sp,
                        R(successor), Eq, Call("mapState", F.Id("C"), R(n)))),
                    All("n", NatType(), Seq(n, Le, F.Id("N"), Sp, Rightarrow, Sp,
                        Call("IsPure", R(n))))), Close,
                Sp, Rightarrow, RowBreak, Grp(),
                Ex("A", Call("End", Vec()), Ex("x", Vec(),
                    And(Nonzero(x), Seq(P(x), Eq, R(D(0))), nonzeroPrefix, collinearPrefix))))))));
    }
}

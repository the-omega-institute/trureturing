using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class FinitePureOrbitExtensionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Purity of the first twice-dimension channel iterates forces purity for every later iterate.",
        H("Finite pure-direction orbit extension"),
        Blocks(
            Paragraph(Text(
                "Let K be any field, V a finite-dimensional K-vector space of dimension r, "
                + "and A an invertible K-linear map on V. Let S be a finite independent family "
                + "of nonzero subspaces, indexed by a set I with at least two elements. "
                + "Independence means that each subspace has zero intersection with the sum "
                + "of the other subspaces; orthogonality is not required.")),
            Paragraph(Text(
                "For a word w of length L over I, its word space C(w) consists of vectors "
                + "whose j-th iterate lies in S(w(j)) for every j less than L. "
                + "The potential Phi(L) is the sum of max(2 dim C(w)-1,0) over all words "
                + "of length L. Thus zero word spaces contribute zero.")),
            Describe.Lean(
                DescribeId.Create("pure-prefix-potential-stabilizes"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Dynamics/FinitePureOrbitExtension.pure_prefix_potential_stabilizes"),
                H("Finite prefix, stable potential, and infinite orbit"),
                StatementSource.FromAuthor(Formula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take a nonzero vector x. If A to the power j applied to x belongs "
                        + "to some S(i) for every j less than 2r-1, then the potential has "
                        + "equal consecutive values at a positive length strictly below 2r-1, "
                        + "and every later iterate of x belongs to the same union of subspaces.")),
                    Paragraph(Text(
                        "Appending a symbol intersects a parent word space with a pulled-back "
                        + "member of S. These child spaces are independent, so their dimensions "
                        + "sum to at most the parent dimension. If no child equals a nonzero "
                        + "parent, the sum of their potential contributions is strictly smaller. "
                        + "Initially the total is at most 2r-2; a surviving nonzero word space "
                        + "at length 2r-1 prevents strict descent at every preceding step.")),
                    Paragraph(Text(
                        "At equality of consecutive potentials, every nonzero word space "
                        + "has an extension equal to itself. Applying A shifts each extended "
                        + "word to its suffix, so the union at the stable length is forward invariant.")),
                    Paragraph(Text(
                        "The channel theorem below constructs the required invariant cyclic "
                        + "tail and its independent coefficient blocks from the finite pure history."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-pure-prefix-extension"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Dynamics/FinitePureOrbitExtension.finite_pure_prefix_extension"),
                H("Finite pure prefix forces an infinite pure orbit"),
                StatementSource.FromAuthor(ChannelFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural dimension d, every CPTP channel C on complex d-space, "
                        + "and every density state rho, suppose C iterated n times on rho is pure "
                        + "for n less than 2d. Then every iterate is pure. This includes the pure "
                        + "initial state and assumes neither unitality nor orthogonality nor periodicity. "
                        + "The zero-dimensional case has no density state.")),
                    Paragraph(Text(
                        "The finite Kraus pure-direction lift supplies one endomorphism A whose "
                        + "nonzero orbit represents the known history. The first dependence among "
                        + "Krylov vectors selects a transient length t and an invariant tail R. "
                        + "The first nonzero dependence coefficient gives an inverse on R, and "
                        + "its consecutive orbit basis has size r with t+r at most d.")),
                    Paragraph(Text(
                        "Equal Kraus coefficient tuples group the tail basis into nonzero "
                        + "independent subspaces. Coordinate uniqueness characterizes their union "
                        + "by simultaneous collinearity of all Kraus images with the next orbit vector. "
                        + "The singleton block case is immediate. Otherwise the known prefix supplies "
                        + "2r-1 memberships, and the word-space potential theorem extends them forever.")),
                    Paragraph(Text(
                        "Finally, trace preservation makes the channel action on each normalized "
                        + "orbit direction equal to the next normalized direction. Induction gives "
                        + "equality with the actual mapState iterates of the original channel and "
                        + "initial state. The finite-prefix lift and exact transition are imported "
                        + "from FiniteKrausPureDirections."))),
                DescribeRole.Theorem))));

    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, type, Comma, Sp, body);

    private static Formula ChannelFormula()
    {
        Formula nat = Seq(Mathbb, Grp(F.Id("N")));
        Formula pure = Call("IsPure", Call("iterate", F.Id("C"), F.Id("n"), F.Id("r")));
        return Disp(All("d", nat,
            All("C", Call("QuantumChannel", F.Id("d")),
            All("r", Call("DensityState", F.Id("d")), Seq(
                Open, All("n", nat, Seq(F.Id("n"), Lt, D(2), F.Id("d"),
                    Sp, Rightarrow, Sp, pure)), Close,
                Sp, Rightarrow, Sp, All("n", nat, pure))))));
    }

    private static Formula Formula()
    {
        Formula orbit(Formula n) => Seq(F.Id("A"), Caret, Grp(n), F.Id("x"));
        Formula member(Formula n) => Seq(Exists, Sp, F.Id("i"), InMacro, F.Id("I"), Comma, Sp,
            orbit(n), InMacro, F.Id("S"), Underscore, Grp(F.Id("i")));
        Formula bound = Seq(D(2), F.Id("r"), Minus, D(1));
        Formula phi(Formula n) => Call("Phi", n);
        Formula length = F.Id("L");
        Formula j = F.Id("j");
        Formula k = F.Id("k");
        Formula conclusion = Seq(
            Open, F.Id("x"), Neq, D(0), Sp, Land, Sp,
            Forall, Sp, j, Lt, bound, Comma, Sp, member(j), Close,
            Sp, Rightarrow, RowBreak, Grp(),
            Open, Exists, Sp, length, Comma, Sp, D(1), Le, length, Lt, bound, Sp, Land, Sp,
            phi(Seq(length, Plus, D(1))), Eq, phi(length), Close,
            Sp, Land, Sp, Forall, Sp, k, InMacro, Mathbb, Grp(F.Id("N")), Comma, Sp,
            member(k));
        Formula assumptions = Seq(Call("Independent", F.Id("S")), Sp, Land, Sp,
            Call("NonzeroMembers", F.Id("S")), Sp, Land, Sp,
            Call("card", F.Id("I")), Ge, D(2), Sp, Land, Sp,
            F.Id("r"), Eq, Call("dim", F.Id("K"), F.Id("V")));
        return Disp(All("K", Call("Field"),
            All("V", Call("FiniteDimensionalSpace", F.Id("K")),
            All("A", Call("LinearAutomorphism", F.Id("K"), F.Id("V")),
            All("I", Call("FiniteType"),
            All("S", Seq(F.Id("I"), To, Call("Submodule", F.Id("K"), F.Id("V"))),
            All("r", Seq(Mathbb, Grp(F.Id("N"))),
            All("x", F.Id("V"), Seq(Open, assumptions, Close,
                Sp, Rightarrow, Sp, conclusion)))))))));
    }
}

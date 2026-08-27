using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Scale.Descent;

internal sealed class GoldenVisibleHiddenTransportDocument
    : IScribeDocumentDefinition
{
    private const string Gid =
        "D5/S1/Scale/Descent/GoldenVisibleHiddenTransport."
            + "golden_visible_hidden_transport";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden inflation expands its visible projection while its conjugate residual contracts.",
        H("Golden Visible-Hidden Transport"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-visible-hidden-transport"),
            DeclarationHandle.Create(Gid),
            H("Golden inflation transports visible and hidden projections"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let J be a real-linear endomorphism whose square is five times the "
                        + "identity. The inflation operator and its visible and hidden "
                        + "projections are constructed explicitly from J and the square root "
                        + "of five. The two projections are therefore source objects rather "
                        + "than an assumed eigenspace decomposition.")),
                Paragraph(Text(
                    "The visible projection scales by the golden ratio, which is greater than "
                        + "one. The hidden projection scales by the negative golden conjugate. "
                        + "Its magnitude is exactly the reciprocal golden ratio, strictly less "
                        + "than one, so the intrinsic sequence epsilon n is that geometric "
                        + "power and converges to zero.")),
                Paragraph(Text(
                    "Current D5 and pinned-Mathlib searches found no exact theorem packaging "
                        + "this carrier, construction, and all transport clauses. Mathlib's "
                        + "golden-ratio identities and geometric-power convergence theorem are "
                        + "applied directly. The existing two-coordinate renormalization result "
                        + "was rejected as a surrogate for the source's module construction."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula w = F.Id("W");
        Formula j = F.Id("J");
        Formula x = F.Id("x");
        Formula n = F.Id("n");
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula identity = Seq(F.Id("I"), Underscore, Grp(w));
        Formula inflation = F.Id("Phi");
        Formula visible = Seq(F.Id("pi"), Underscore, Grp(F.Id("vis")));
        Formula hidden = Seq(F.Id("pi"), Underscore, Grp(F.Id("hid")));
        Formula epsilon = F.Id("epsilon");
        Formula phi = Seq(Operatorname, Grp(F.Id("goldenRatio")));
        Formula phiConj = Seq(Operatorname, Grp(F.Id("goldenConj")));
        Formula half = Seq(Frac, Grp(D(1)), Grp(D(2)));
        Formula sqrtFive = Seq(Sqrt, Grp(D(5)));

        Formula Apply(Formula function, Formula argument) =>
            Seq(function, Open, argument, Close);
        Formula Scale(Formula coefficient, Formula value) =>
            Seq(coefficient, Sp, Cdot, Sp, value);
        Formula Abs(Formula value) => Seq(Vert, Sp, value, Sp, Vert);
        Formula Pow(Formula value, Formula exponent) =>
            Seq(value, Caret, Grp(exponent));

        Formula linearMapType = Call("LinearMap", reals, w, w);
        Formula inflationBody = Seq(
            half, Grp(identity, Sp, Plus, Sp, j));
        Formula visibleBody = Seq(
            half, Grp(identity, Sp, Plus, Sp,
                Frac, Grp(D(1)), Grp(sqrtFive), j));
        Formula hiddenBody = Seq(
            half, Grp(identity, Sp, Minus, Sp,
                Frac, Grp(D(1)), Grp(sqrtFive), j));
        Formula epsilonBody = Seq(Abs(phiConj), Caret, Grp(n));

        Formula visibleLaw = Seq(
            Forall, Sp, x, Colon, Sp, w, Comma, Sp,
            Apply(visible, Apply(inflation, x)), Sp, Eq, Sp,
            Scale(phi, Apply(visible, x)));
        Formula hiddenLaw = Seq(
            Forall, Sp, x, Colon, Sp, w, Comma, Sp,
            Apply(hidden, Apply(inflation, x)), Sp, Eq, Sp,
            Scale(phiConj, Apply(hidden, x)));
        Formula epsilonLaw = Seq(
            Forall, Sp, n, Colon, Sp, naturals, Comma, Sp,
            Apply(epsilon, n), Sp, Eq, Sp,
            Pow(Grp(phi, Caret, Grp(Minus, D(1))), n));

        return Disp(Seq(
            Forall, Sp, w, Colon, Sp, F.Id("Type"), Comma, Sp,
            Open, Call("AddCommGroup", w), Sp, Land, Sp,
                Call("Module", reals, w), Close, Sp, Rightarrow, Sp,
            Forall, Sp, j, Colon, Sp, linearMapType, Comma, Sp,
            j, Sp, Circ, Sp, j, Sp, Eq, Sp, Scale(D(5), identity), Sp,
            Rightarrow, RowBreak, Grp(),
            F.Text, Grp(F.Id("let"), Sp), Sp,
            inflation, Sp, Colon, Eq, Sp, inflationBody, Semi, Sp,
            visible, Sp, Colon, Eq, Sp, visibleBody, Semi, RowBreak, Grp(),
            hidden, Sp, Colon, Eq, Sp, hiddenBody, Semi, Sp,
            epsilon, Colon, naturals, To, reals, Sp, Colon, Eq, Sp,
            Open, n, Colon, Sp, naturals, Sp, Mapsto, Sp, epsilonBody, Close, Semi,
            RowBreak, Grp(),
            Open, visibleLaw, Close, Sp, Land, Sp,
            D(1), Sp, Lt, Sp, phi, Sp, Land, RowBreak, Grp(),
            Open, hiddenLaw, Close, Sp, Land, Sp,
            phiConj, Sp, Lt, Sp, D(0), Sp, Land, RowBreak, Grp(),
            Abs(phiConj), Sp, Eq, Sp, phi, Caret, Grp(Minus, D(1)), Sp, Land, Sp,
            phi, Caret, Grp(Minus, D(1)), Sp, Lt, Sp, D(1), Sp, Land,
            RowBreak, Grp(),
            Open, epsilonLaw, Close, Sp, Land, Sp,
            Call("Tendsto", epsilon,
                Seq(Operatorname, Grp(F.Id("atTop"))), Call("nhds", D(0))), Dot));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) pieces.AddRange([Comma, Sp]);
            pieces.Add(arguments[index]);
        }

        pieces.Add(Close);
        return Seq([.. pieces]);
    }
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class FiniteRealZeroFillRegisterDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Linear/FiniteRealZeroFillRegister.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite real zero-fill register reads every original sign through its horizon.",
        H("Finite Real Zero-Fill Register"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-real-zero-fill-x"),
                DeclarationHandle.Create(Prefix + "X"),
                H("Infinite binary inputs"),
                StatementSource.FromAuthor(InputFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An input is an arbitrary function from natural times to Bool; no finite encoding or probability measure is imposed."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-real-zero-fill-bitsign"),
                DeclarationHandle.Create(Prefix + "bitSign"),
                H("The original real sign"),
                StatementSource.FromAuthor(BitSignFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original sign is minus one raised to the Boolean natural value: false has sign +1 and true has sign -1."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-real-zero-fill-signal"),
                DeclarationHandle.Create(Prefix + "signal"),
                H("The time-indexed original signal"),
                StatementSource.FromAuthor(SignalFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At time t the signal reads the sign of the original input coordinate x(t)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-real-zero-fill-state"),
                DeclarationHandle.Create(Prefix + "State"),
                H("The finite real state"),
                StatementSource.FromAuthor(StateFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any natural horizon H, the state is the real vector with coordinates Fin(H+1). Its entries are arbitrary real numbers; H=0 still has coordinate zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-real-zero-fill-initstate"),
                DeclarationHandle.Create(Prefix + "initState"),
                H("Initialization from the original input"),
                StatementSource.FromAuthor(InitialFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Initialize coordinate i with signal(i,x), thereby storing the first H+1 original signs once."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-real-zero-fill-update"),
                DeclarationHandle.Create(Prefix + "update"),
                H("A fixed linear update with real-zero fill"),
                StatementSource.FromAuthor(UpdateFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The update copies coordinate i+1 when that coordinate lies in Fin(H+1), and otherwise writes the real number 0. Both additivity and real scalar compatibility are part of this linear map; Hom over the reals denotes the space of real-linear maps. The boundary value is different from the sign of false. The update uses neither time nor a subsequent input sample."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-real-zero-fill-readout"),
                DeclarationHandle.Create(Prefix + "readout"),
                H("A fixed linear readout"),
                StatementSource.FromAuthor(ReadoutFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The readout is the real-linear coordinate-zero projection on the same finite real state."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-real-zero-fill-update-iterate"),
                DeclarationHandle.Create(Prefix + "update_iterate"),
                H("Every in-bound coordinate of every iterate"),
                StatementSource.FromAuthor(IterateFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For all H,t, arbitrary real state q and coordinate i satisfying i.val+t<H+1, the t-fold update at i equals the original q at i.val+t. Induction on t applies the successor equation for function iteration; the in-bound inequality selects the copy branch at the successor step. The statement concerns only in-bound coordinates."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-real-zero-fill-pointwise-attainment"),
                DeclarationHandle.Create(Prefix + "pointwise_attainment"),
                H("Pointwise attainment of the original signal"),
                StatementSource.FromAuthor(AttainmentFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Apply the arbitrary-state invariant to the initialized vector at coordinate zero. For every infinite input x and every t<=H, including H=t=0, the fixed readout after t fixed updates is exactly signal(t,x). This is the finite real construction in original theorem 12.4. In the binary-shift source, the unit-word orbit at coordinate j is x(j+word.length); its coordinate-zero sign observation is therefore this same signal at time t. The construction proves the pointwise upper realization. It asserts no lower bound, minimum dimension, state cardinality, after-boundary identity, or almost-everywhere endpoint."))),
                DescribeRole.Theorem))));

    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Bool => Seq(Mathrm, Grp(F.Id("Bool")));
    private static Formula Op(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula App(Formula function, Formula argument) => Seq(function, Open, argument, Close);
    private static Formula StateOf(Formula horizon) => App(Op("State"), horizon);
    private static Formula FinOf(Formula horizon) => App(Op("Fin"), Seq(horizon, Plus, D(1)));
    private static Formula Val(Formula index) => Seq(index, Dot, Op("val"));
    private static Formula Pair(Formula value, Formula bound) => Seq(Langle, value, Comma, bound, Rangle);
    private static Formula Hom(Formula domain, Formula codomain) =>
        Seq(Op("Hom"), Underscore, Grp(Real), Open, domain, Comma, codomain, Close);

    private static Formula InputFormula() => Disp(Seq(
        F.Id("X"), Colon, Eq, Open, Nat, To, Bool, Close));

    private static Formula BitSignFormula() => Disp(Seq(
        Begin, Grp(F.Id("gathered")),
        Forall, Sp, F.Id("b"), InMacro, Bool, Comma, Quad,
        App(Op("bitSign"), F.Id("b")), Eq, Open, Minus, D(1), Close,
        Caret, Grp(App(Op("toNat"), F.Id("b"))), InMacro, Real,
        RowBreak, Grp(),
        App(Op("bitSign"), Op("false")), Eq, Plus, D(1), Comma, Quad,
        App(Op("bitSign"), Op("true")), Eq, Minus, D(1),
        End, Grp(F.Id("gathered"))));

    private static Formula SignalFormula() => Disp(Seq(
        Forall, Sp, F.Id("t"), InMacro, Nat, Comma, Sp,
        Forall, Sp, F.Id("x"), InMacro, F.Id("X"), Comma, Quad,
        App(Op("signal"), Seq(F.Id("t"), Comma, F.Id("x"))), Eq,
        App(Op("bitSign"), App(F.Id("x"), F.Id("t")))));

    private static Formula StateFormula() => Disp(Seq(
        Forall, Sp, F.Id("H"), InMacro, Nat, Comma, Quad,
        StateOf(F.Id("H")), Colon, Eq, Open, FinOf(F.Id("H")), To, Real, Close));

    private static Formula InitialFormula() => Disp(Seq(
        Forall, Sp, F.Id("H"), InMacro, Nat, Comma, Sp,
        Forall, Sp, F.Id("x"), InMacro, F.Id("X"), Comma, Sp,
        Forall, Sp, F.Id("i"), InMacro, FinOf(F.Id("H")), Comma, Quad,
        App(App(Op("initState"), Seq(F.Id("H"), Comma, F.Id("x"))), F.Id("i")), Eq,
        App(Op("signal"), Seq(Val(F.Id("i")), Comma, F.Id("x")))));

    private static Formula UpdateFormula()
    {
        Formula h = F.Id("H"), q = F.Id("q"), v = F.Id("v"), i = F.Id("i"), c = F.Id("c");
        Formula u = Seq(F.Id("U"), Underscore, Grp(h));
        Formula next = Seq(Val(i), Plus, D(1));
        return Disp(Seq(Forall, Sp, h, InMacro, Nat, Comma, Quad,
            Begin, Grp(F.Id("gathered")),
            u, Colon, Eq, App(Op("update"), h), InMacro, Hom(StateOf(h), StateOf(h)),
            RowBreak, Grp(),
            Forall, Sp, q, InMacro, StateOf(h), Comma, Sp,
            Forall, Sp, i, InMacro, FinOf(h), Comma, Quad,
            App(App(u, q), i), Eq, Begin, Grp(F.Id("cases")),
            App(q, Pair(next, F.Id("h"))), Comma, Amp, Sp,
            F.Id("h"), Colon, next, Lt, h, Plus, D(1), Comma,
            RowBreak, Grp(), D(0), InMacro, Real, Comma, Amp, Sp,
            Mathrm, Grp(F.Id("otherwise")),
            End, Grp(F.Id("cases")),
            RowBreak, Grp(),
            Forall, Sp, q, Comma, v, InMacro, StateOf(h), Comma, Sp,
            Forall, Sp, c, InMacro, Real, Comma, Quad,
            App(u, Seq(q, Plus, v)), Eq, App(u, q), Plus, App(u, v), Comma, Quad,
            App(u, Seq(c, Cdot, q)), Eq, c, Cdot, App(u, q),
            End, Grp(F.Id("gathered"))));
    }

    private static Formula ReadoutFormula()
    {
        Formula h = F.Id("H"), q = F.Id("q"), r = Seq(F.Id("R"), Underscore, Grp(h));
        return Disp(Seq(Forall, Sp, h, InMacro, Nat, Comma, Quad,
            r, Colon, Eq, App(Op("readout"), h), InMacro, Hom(StateOf(h), Real), Comma, Quad,
            Forall, Sp, q, InMacro, StateOf(h), Comma, Quad,
            App(r, q), Eq, App(q, D(0))));
    }

    private static Formula IterateFormula()
    {
        Formula h = F.Id("H"), t = F.Id("t"), q = F.Id("q"), i = F.Id("i");
        Formula hi = Seq(F.Id("h"), Underscore, Grp(i));
        Formula index = Seq(Val(i), Plus, t);
        Formula iterate = Seq(App(Op("update"), h), Caret, Grp(OpenBracket, t, CloseBracket));
        return Disp(Seq(
            Forall, Sp, h, Comma, t, InMacro, Nat, Comma, Sp,
            Forall, Sp, q, InMacro, StateOf(h), Comma, Sp,
            Forall, Sp, i, InMacro, FinOf(h), Comma, Sp,
            Forall, Sp, hi, Colon, index, Lt, h, Plus, D(1), Comma, Quad,
            App(App(iterate, q), i), Eq, App(q, Pair(index, hi))));
    }

    private static Formula AttainmentFormula()
    {
        Formula h = F.Id("H"), x = F.Id("x"), t = F.Id("t");
        Formula ht = Seq(F.Id("h"), Underscore, Grp(t));
        Formula iterate = Seq(App(Op("update"), h), Caret, Grp(OpenBracket, t, CloseBracket));
        Formula initial = App(Op("initState"), Seq(h, Comma, x));
        return Disp(Seq(
            Forall, Sp, h, InMacro, Nat, Comma, Sp,
            Forall, Sp, x, InMacro, F.Id("X"), Comma, Sp,
            Forall, Sp, t, InMacro, Nat, Comma, Sp,
            Forall, Sp, ht, Colon, t, Leq, h, Comma, Quad,
            App(App(Op("readout"), h), App(iterate, initial)), Eq,
            App(Op("signal"), Seq(t, Comma, x))));
    }
}

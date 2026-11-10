using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Dynamics;

internal sealed class TopologicalFactorMinimalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Continuous surjective equivariant factors descend forward-orbit minimality.",
        H("Topological Factor Minimality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a-continuous-surjective-equivariant-factor-descends-minimality"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Dynamics/TopologicalFactorMinimality."
                        + "continuous_surjective_equivariant_minimality"),
                H("A continuous surjective equivariant factor descends minimality"),
                StatementSource.FromAuthor(AdditiveFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A continuous surjective map intertwining two additive monoid actions "
                            + "carries every dense source orbit onto a dense target orbit. "
                            + "The proof uses only continuity, surjectivity, and the equivariance "
                            + "identity; no compactness or separation assumptions are required.")),
                    Paragraph(Text(
                        "For a target point choose a source preimage. A second target point is "
                            + "the continuous image of a point in the closure of the source orbit. "
                            + "Equivariance maps each source orbit element into the target orbit, "
                            + "so `map_mem_closure` gives the result."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a-continuous-semiconjugate-factor-preserves-forward-orbits"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Dynamics/TopologicalFactorMinimality."
                        + "dense_forward_orbit_of_continuous_surjective_semiconj"),
                H("A continuous semiconjugate factor preserves forward-orbit minimality"),
                StatementSource.FromAuthor(ForwardFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The same closure argument is stated directly for iterates of two "
                            + "self-maps. A continuous surjective semiconjugacy sends each "
                            + "iterated source orbit into the corresponding target orbit.")),
                    Paragraph(Text(
                        "This form applies to symbolic observation factors and provides the "
                            + "bridge from symbolic dynamics to topological dynamics without "
                            + "choosing a particular alphabet or metric."))),
                DescribeRole.Theorem)),
        []));

    private static Formula App(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Named(string name) =>
        Seq(Operatorname, Grp(F.Id(name.Replace(".", ""))));

    private static Formula Typeclass(string name, params Formula[] arguments) =>
        Seq(OpenBracket, App(Named(name), arguments), CloseBracket);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Binder(string name, Formula type) =>
        Seq(F.Id(name), Colon, Sp, type);

    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Binder(name, type), Comma, Sp, body);

    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula DenseRange(Formula function) => App(Named("Dense"), App(Named("Set.range"), function));

    private static Formula AdditiveFormula()
    {
        Formula m = F.Id("M");
        Formula x = F.Id("X");
        Formula y = F.Id("Y");
        Formula f = F.Id("f");
        Formula mm = F.Id("m");
        Formula xx = F.Id("x");
        Formula hypotheses = Seq(
            Typeclass("AddMonoid", m), Sp,
            Typeclass("TopologicalSpace", x), Sp,
            Typeclass("TopologicalSpace", y), Sp,
            Typeclass("AddAction", m, x), Sp,
            Typeclass("AddAction", m, y), Sp,
            Typeclass("AddAction.IsMinimal", m, x), Sp,
            Binder("f", Arrow(x, y)), Comma, Sp,
            Binder("hf", App(Named("Continuous"), f)), Comma, Sp,
            Binder("hsurj", App(Named("Surjective"), f)), Comma, Sp,
            Binder("hequiv", All("m", m,
                All("x", x, Seq(App(f, App(F.Id("vadd"), mm, xx)), Eq,
                    App(F.Id("vadd"), mm, App(f, xx)))))));
        return Disp(Seq(
            Forall, Sp, Binder("M", F.Id("Type")), Comma, Sp,
            Forall, Sp, Binder("X", F.Id("Type")), Comma, Sp,
            Forall, Sp, Binder("Y", F.Id("Type")), Comma, Esc,
            hypotheses, Rightarrow, Sp,
            App(Named("AddAction.IsMinimal"), m, y), Dot));
    }

    private static Formula ForwardFormula()
    {
        Formula x = F.Id("X");
        Formula y = F.Id("Y");
        Formula f = F.Id("f");
        Formula g = F.Id("g");
        Formula factor = F.Id("factor");
        Formula n = F.Id("n");
        Formula naturals = Nat();
        Formula sourceOrbit = Seq(Open, n, InMacro, Sp, naturals, Sp, Mapsto, Sp,
            App(Seq(f, Caret, n), F.Id("x")), Close);
        Formula targetOrbit = Seq(Open, n, InMacro, Sp, naturals, Sp, Mapsto, Sp,
            App(Seq(g, Caret, n), F.Id("y")), Close);
        Formula hypotheses = Seq(
            Binder("f", Arrow(x, x)), Comma, Sp,
            Binder("g", Arrow(y, y)), Comma, Sp,
            Binder("factor", Arrow(x, y)), Comma, Sp,
            Binder("hfactor", App(Named("Continuous"), factor)), Comma, Sp,
            Binder("hsurj", App(Named("Surjective"), factor)), Comma, Sp,
            Binder("hsemiconj", App(Named("Semiconj"), factor, f, g)), Comma, Sp,
            Binder("hminimal", All("x", x, DenseRange(sourceOrbit))));
        return Disp(Seq(
            Forall, Sp, Binder("X", F.Id("Type")), Comma, Sp,
            Forall, Sp, Binder("Y", F.Id("Type")), Comma, Esc,
            Typeclass("TopologicalSpace", x), Sp,
            Typeclass("TopologicalSpace", y), Comma, Esc,
            hypotheses, Rightarrow, Sp,
            All("y", y, DenseRange(targetOrbit)), Dot));
    }
}

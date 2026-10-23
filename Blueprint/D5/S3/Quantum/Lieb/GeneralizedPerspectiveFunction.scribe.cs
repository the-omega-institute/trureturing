using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Lieb;

internal sealed class GeneralizedPerspectiveFunctionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Attributed reusable operator API: GeneralizedPerspectiveFunction.",
        H("GeneralizedPerspectiveFunction"),
        Blocks(
            Paragraph(Text("Consumed Apache-2.0 Physlib source at immutable revision "
                + "b9043cc548ef6d63a28454cf3a57fb12a0c2e142, credited to Kei Tsukamoto, Kento Mori and "
                + "Hayata Yamasaki. Retire each supplier when an equivalent consumed declaration is "
                + "available in the repository-pinned Mathlib.")),
            Describe.Lean(
                DescribeId.Create("positive-generalized-perspective-concavity"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Lieb/GeneralizedPerspectiveFunction.theorem_2_6_forward_jointlyConcaveOn_psd_pd_Ici"),
                H("Joint concavity of the generalized perspective"),
                StatementSource.FromAuthor(EndpointFormula()),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Divergence/tsukamotomoriyamasaki2026lieb")),
                Blocks(
                    Paragraph(Text("The carrier is a nontrivial complete complex Hilbert space. The function f is "
                        + "operator concave on [0,infinity) uniformly over all such Hilbert spaces in the same "
                        + "universe, continuous there, and satisfies f(0) at least zero. The function h is "
                        + "operator concave on (0,infinity) on the fixed carrier, continuous there, and strictly "
                        + "positive at every positive real argument.")),
                    Paragraph(Text("The first argument A is self-adjoint with nonnegative spectrum (PSD); the second B is "
                        + "self-adjoint with strictly positive spectrum (PD). The generalized perspective is "
                        + "h(B)^(1/2) f(h(B)^(-1/2) A h(B)^(-1/2)) h(B)^(1/2), using real CFC. It is jointly "
                        + "concave under the same mixture coefficient in both arguments, with no A/B commutation "
                        + "and no finite-dimensionality requirement."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)) };
        if (arguments.Length == 0) return Seq([.. items]);
        items.Add(Open);
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula Instance(string name, params Formula[] arguments) =>
        Seq(OpenBracket, Call(name, arguments), CloseBracket);
    private static Formula RealType => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula ComplexType => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula U => F.Id("u");
    private static Formula Carrier => F.Id("H");
    private static Formula Nonnegative => Call("Ici", D(0));
    private static Formula Positive => Call("Ioi", D(0));
    private static Formula RealFunction => Seq(RealType, Sp, To, Sp, RealType);
    private static Formula HilbertPrefix(bool nontrivial = true, bool finite = false,
        bool complete = true)
    {
        var items = new List<Formula> {
            Forall, Sp, U, Colon, Sp, Call("Level"), Comma, Esc,
            Carrier, Colon, Sp, Call("Type", U), Comma, Esc,
            Instance("NormedAddCommGroup", Carrier), Comma, Sp,
            Instance("InnerProductSpace", ComplexType, Carrier), Comma, Sp };
        if (complete) items.AddRange([Instance("CompleteSpace", Carrier), Comma, Sp]);
        if (nontrivial) items.AddRange([Instance("Nontrivial", Carrier), Comma, Sp]);
        if (finite) items.AddRange([Instance("FiniteDimensional", ComplexType, Carrier), Comma, Sp]);
        return Seq([.. items]);
    }
    private static Formula Conjunction(params Formula[] clauses)
    {
        var items = new List<Formula>();
        for (var i = 0; i < clauses.Length; i++)
        {
            if (i > 0) items.AddRange([Sp, Land, Sp]);
            items.Add(clauses[i]);
        }
        return Seq([.. items]);
    }

    private static Formula EndpointFormula()
    {
        Formula f = F.Id("f"), h = F.Id("h"), x = F.Id("x");
        var hypotheses = Conjunction(
            Call("OperatorConcaveOnAll", U, Nonnegative, f),
            Call("ContinuousOn", f, Nonnegative),
            Seq(D(0), Sp, Le, Sp, Call("f", D(0))),
            Call("OperatorConcaveOn", Carrier, Positive, h),
            Call("ContinuousOn", h, Positive),
            Seq(Open, Forall, Sp, x, Colon, Sp, RealType, Comma, Sp,
                x, Sp, InMacro, Sp, Positive, Sp, Implies, Sp,
                D(0), Sp, Lt, Sp, Call("h", x), Close));
        return Disp(Seq(HilbertPrefix(), f, Comma, Sp, h, Colon, Sp,
            RealFunction, Comma, Esc, hypotheses, Sp, Implies, Sp,
            Call("JointlyConcaveOn", Call("psdSet", Carrier), Call("pdSet", Carrier),
                Call("GeneralizedPerspective", Carrier, f, h)), Dot));
    }
}

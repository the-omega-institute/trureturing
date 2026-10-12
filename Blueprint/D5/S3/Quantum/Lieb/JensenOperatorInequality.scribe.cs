using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Lieb;

internal sealed class JensenOperatorInequalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Attributed reusable operator API: JensenOperatorInequality.",
        H("JensenOperatorInequality"),
        Blocks(
            Paragraph(Text("Consumed Apache-2.0 Physlib source at immutable revision "
                + "b9043cc548ef6d63a28454cf3a57fb12a0c2e142, credited to Kei Tsukamoto, Kento Mori and "
                + "Hayata Yamasaki. Retire each supplier when an equivalent consumed declaration is "
                + "available in the repository-pinned Mathlib.")),
            Describe.Lean(
                DescribeId.Create("jensen-positive-two-term"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Lieb/JensenOperatorInequality.theorem_2_5_2_i_ici_all_imp_v"),
                H("Localized Jensen for two operator terms"),
                StatementSource.FromAuthor(EndpointFormula()),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Divergence/tsukamotomoriyamasaki2026lieb")),
                Blocks(
                    Paragraph(Text("The carrier is a nontrivial complete complex Hilbert space. CondIciAll includes "
                        + "uniform operator convexity of f on [0,infinity) over all nontrivial complete complex "
                        + "Hilbert spaces in the same universe, continuity there, and f(0) at most zero.")),
                    Paragraph(Text("For self-adjoint A,B with nonnegative real spectra and arbitrary X,Y satisfying X* X "
                        + "+ Y* Y at most I, CondV gives f(X* A X + Y* B Y) at most X* f(A) X + Y* f(B) Y. The "
                        + "normalization is an inequality, so a nonzero defect is allowed. No A/B commutation is "
                        + "assumed."))),
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
    private static Formula EndpointFormula() => Disp(Seq(
        HilbertPrefix(), F.Id("f"), Colon, Sp, RealFunction, Comma, Esc,
        Call("CondIciAll", U, F.Id("f")), Sp, Implies, Sp,
        Call("CondV", Carrier, F.Id("f")), Dot));
}

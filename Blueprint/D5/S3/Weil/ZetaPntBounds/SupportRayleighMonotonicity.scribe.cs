using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaPntBounds;

internal sealed class SupportRayleighMonotonicityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula energy = F.Id("q");
        Formula test = F.Id("f");
        Formula l1 = new Formula.Subscript(F.Id("L"), D(1));
        Formula l2 = new Formula.Subscript(F.Id("L"), D(2));
        Formula r1 = new Formula.Subscript(F.Id("R"), D(1));
        Formula r2 = new Formula.Subscript(F.Id("R"), D(2));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula tests = Seq(Mathcal, Grp(F.Id("W")));

        Formula SupportCondition(Formula scale) => Seq(
            Call("tsupport", test), Sp, Subseteq, Sp,
            Call("Ioo", Seq(Minus, scale), scale));
        Formula RayleighSet(Formula scale) => Seq(
            OpenBrace, Call("q", scale, test), Sp, Mid, Sp,
            test, Sp, InMacro, Sp, tests, Comma, Sp,
            SupportCondition(scale), Sp, Land, Sp,
            Call("l2Mass", test), Sp, Eq, Sp, D(1), CloseBrace);

        Formula invariant = Seq(
            Forall, Sp, test, InMacro, Sp, tests, Comma, Sp,
            SupportCondition(l1), Sp, Rightarrow, Sp,
            Call("q", l2, test), Sp, Eq, Sp, Call("q", l1, test));
        Formula premises = Seq(
            l1, Sp, Lt, Sp, l2, Sp, Land, Sp,
            Grp(invariant), Sp, Land, Sp,
            Call("BddBelow", r2), Sp, Land, Sp,
            Call("Nonempty", r1));
        Formula conclusion = Seq(
            Call("sInf", r2), Sp, Leq, Sp, Call("sInf", r1));

        Formula statement = Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, energy, Colon, Sp, reals, Sp, To, Sp, tests,
                Sp, To, Sp, reals, Comma, Sp,
                l1, Comma, Sp, l2, InMacro, Sp, reals, Comma),
            Seq(
                Operatorname, Grp(F.Id("let")), Sp,
                r1, Sp, Eq, Sp, RayleighSet(l1), Comma),
            Seq(
                r2, Sp, Eq, Sp, RayleighSet(l2), Comma),
            Seq(
                premises, Sp, Rightarrow, Sp, conclusion, Dot),
        ]));

        return DocumentDefinition.Create(ScribeNode.Create(
            "A support-window enlargement expands the normalized Weil test class and cannot "
                + "increase the lowest Rayleigh value of a window-invariant quadratic cost.",
            H("Support Rayleigh Monotonicity"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("support-rayleigh-monotonicity"),
                    DeclarationHandle.Create(
                        "D5/S3/Weil/ZetaPntBounds/SupportRayleighMonotonicity."
                            + "support_rayleigh_monotonicity"),
                    H("The lowest Rayleigh value is antitone under support enlargement"),
                    StatementSource.FromAuthor(statement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "W is the canonical carrier of even smooth compactly supported "
                                + "complex tests, and l2Mass is its canonical squared real-line "
                                + "mass. The two displayed sets are the attained quadratic-cost "
                                + "values on unit-mass tests in the respective open windows.")),
                        Paragraph(Text(
                            "The window-invariance premise is the source clause that the explicit "
                                + "formula value does not change when a smaller-supported test is "
                                + "viewed in a larger external window. Set inclusion and the "
                                + "conditional-complete-lattice infimum lemma yield the result."))),
                    DescribeRole.Theorem))));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}

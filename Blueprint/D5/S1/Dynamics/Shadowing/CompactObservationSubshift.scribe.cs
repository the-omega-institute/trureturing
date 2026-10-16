using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class CompactObservationSubshiftDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/CompactObservationSubshift.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compact continuous finite observations form closed shift-invariant sofic languages.",
        H("Compact Observation Subshifts"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("observation-language"),
                DeclarationHandle.Create(Owner + "observationLanguage"),
                H("Observation language"),
                StatementSource.FromAuthor(DefinitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The observation language is the range of x↦(n↦a(f^[n](x)))."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("continuous-observation-name"),
                DeclarationHandle.Create(Owner + "continuous_observationName"),
                H("Continuous observation names"),
                StatementSource.FromAuthor(ContinuityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Continuity of the dynamics and readout gives continuity into the countable product."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("compact-closed-observation-language"),
                DeclarationHandle.Create(Owner + "observationLanguage_isCompact_isClosed"),
                H("Compact and closed observation language"),
                StatementSource.FromAuthor(CompactClosedFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A compact source and finite discrete alphabet make the observation range compact and closed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("observation-language-shift"),
                DeclarationHandle.Create(Owner + "observationLanguage_shift_invariant"),
                H("Shift invariance"),
                StatementSource.FromAuthor(ShiftFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Shifting a complete observation name is the name of the forward image point."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("compact-observation-sofic"),
                DeclarationHandle.Create(Owner + "compact_observation_is_closed_shift_invariant_sofic"),
                H("Compact observation subshift is closed, invariant and sofic"),
                StatementSource.FromAuthor(MainFormula()),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Dynamics/peng2026shadowing")),
                Blocks(
                    Paragraph(Text(
                        "For a compact source with continuous dynamics and a continuous finite discrete readout, "
                        + "the observed language is compact and closed. Under HasShadowing, the finite-observation "
                        + "graph construction gives an exact sofic presentation, and the forward shift preserves "
                        + "the range. This is a formal bridge from topological dynamics to symbolic dynamics; it "
                        + "does not resolve the global zero-dimensional extension questions."))),
                DescribeRole.Theorem))));

    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Map(Formula x, Formula y) => Seq(x, Sp, Rightarrow, Sp, y);
    private static Formula Call(string name, params Formula[] args)
    {
        var names = name.Split('.');
        var head = new List<Formula> { F.Id(names[0]) };
        for (var j = 1; j < names.Length; j++) head.AddRange([Dot, F.Id(names[j])]);
        var items = new List<Formula> { Seq([.. head]) };
        items.Add(Open);
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula Iter(Formula f, Formula n, Formula x) => Call("Function.iterate", f, n, x);
    private static Formula Name(Formula f, Formula a, Formula x) =>
        Seq(Open, n(), Sp, Mapsto, Sp, a, Open, Iter(f, n(), x), Close, Close);
    private static Formula n() => F.Id("n");

    private static Formula DefinitionFormula()
    {
        var X = F.Id("X"); var A = F.Id("A"); var f = F.Id("f"); var a = F.Id("a"); var S = F.Id("S");
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, Typed(X, Seq(F.Id("Type"), Sp, F.Id("u"))), Comma, Sp,
                Typed(A, Seq(F.Id("Type"), Sp, F.Id("v"))), Comma, Sp,
                Typed(f, Map(X, X)), Comma, Sp, Typed(a, Map(X, A)), Comma),
            Seq(Call("observationLanguage", f, a), Sp, Eq, Sp, Call("Set.range",
                Seq(x(), Sp, Mapsto, Sp, Name(f, a, x()))), Dot)
        ]));
    }

    private static Formula ContinuityFormula()
    {
        var X = F.Id("X"); var A = F.Id("A"); var f = F.Id("f"); var a = F.Id("a");
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, Typed(X, Seq(F.Id("Type"), Sp, F.Id("u"))), Comma, Sp,
                Typeclass("TopologicalSpace", X), Comma, Sp,
                Typed(A, Seq(F.Id("Type"), Sp, F.Id("v"))), Comma, Sp,
                Typeclass("TopologicalSpace", A), Comma),
            Seq(Typed(f, Map(X, X)), Comma, Sp, Typed(a, Map(X, A)), Comma, Sp,
                Hyp(Seq(Call("Continuous", f), Sp, Land, Sp, Call("Continuous", a))),
                Call("Continuous", Seq(x(), Mapsto, Name(f, a, x()))), Dot)
        ]));
    }

    private static Formula CompactClosedFormula()
    {
        var X = F.Id("X"); var A = F.Id("A"); var f = F.Id("f"); var a = F.Id("a");
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, Typed(X, Seq(F.Id("Type"), Sp, F.Id("u"))), Comma, Sp,
                Typeclass("TopologicalSpace", X), Comma, Sp, Typeclass("CompactSpace", X), Comma, Sp,
                Typed(A, Seq(F.Id("Type"), Sp, F.Id("v"))), Comma, Sp,
                Typeclass("TopologicalSpace", A), Comma, Sp, Typeclass("DiscreteTopology", A), Comma, Sp,
                Typeclass("Finite", A), Comma),
            Seq(Typed(f, Map(X, X)), Comma, Sp, Typed(a, Map(X, A)), Comma, Sp,
                Hyp(Seq(Call("Continuous", f), Sp, Land, Sp, Call("Continuous", a))),
                Call("IsCompact", Call("observationLanguage", f, a)), Sp, Land, Sp,
                Call("IsClosed", Call("observationLanguage", f, a)), Dot)
        ]));
    }

    private static Formula ShiftFormula()
    {
        var X = F.Id("X"); var A = F.Id("A"); var f = F.Id("f"); var a = F.Id("a"); var w = F.Id("w");
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, Typed(f, Map(X, X)), Comma, Sp, Typed(a, Map(X, A)), Comma, Sp,
                Typed(w, Map(Nat(), A)), Comma, Sp,
                Hyp(Seq(w, Sp, InMacro, Sp, Call("observationLanguage", f, a))),
                Seq(ShiftWord(w), Sp, InMacro, Sp, Call("observationLanguage", f, a)), Dot)
        ]));
    }

    private static Formula MainFormula()
    {
        var X = F.Id("X"); var A = F.Id("A"); var f = F.Id("f"); var a = F.Id("a");
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, Typed(X, Seq(F.Id("Type"), Sp, F.Id("u"))), Comma, Sp,
                Typeclass("TopologicalSpace", X), Comma, Sp, Typeclass("CompactSpace", X), Comma, Sp,
                Typed(A, Seq(F.Id("Type"), Sp, F.Id("v"))), Comma, Sp,
                Typeclass("TopologicalSpace", A), Comma, Sp, Typeclass("DiscreteTopology", A), Comma, Sp,
                Typeclass("Finite", A), Comma),
            Seq(Typed(f, Map(X, X)), Comma, Sp, Typed(a, Map(X, A)), Comma, Sp,
                Hyp(Seq(Call("Continuous", f), Sp, Land, Sp, Call("Continuous", a))),
                Hyp(Call("HasShadowing", f)),
                Seq(Call("IsSofic", Call("observationLanguage", f, a)), Sp, Land, Sp,
                    Call("IsClosed", Call("observationLanguage", f, a)), Sp, Land, Sp,
                    Forall, Sp, Typed(F.Id("w"), Map(Nat(), A)), Comma, Sp,
                    Hyp(Seq(F.Id("w"), Sp, InMacro, Sp, Call("observationLanguage", f, a))),
                    Seq(ShiftWord(F.Id("w")), Sp, InMacro, Sp, Call("observationLanguage", f, a))), Dot)
        ]));
    }

    private static Formula x() => F.Id("x");
    private static Formula ShiftWord(Formula w) =>
        Seq(Open, n(), Sp, Mapsto, Sp, Apply(w, Seq(n(), Plus, D(1))), Close);
    private static Formula Apply(Formula f, Formula arg) => Seq(f, Open, arg, Close);
    private static Formula Typed(Formula value, Formula type) => Seq(value, Colon, Sp, type);
    private static Formula Typeclass(string name, Formula type) => Seq(OpenBracket, Call(name, type), CloseBracket);
    private static Formula Hyp(Formula premise) => Seq(premise, Sp, Rightarrow, Sp);
}
